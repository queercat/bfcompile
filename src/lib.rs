use std::collections::HashSet;

/// <instruction> ::= ">" | "<" | "+" | "-"  | "," | "." | "[" <instruction> "]"
/// <program> ::= <instruction>?
#[derive(Debug, PartialEq)]
enum Instruction {
    IncPtr,
    DecPtr,
    IncData,
    DecData,
    Print,
    Read,
    Loop(Vec<Instruction>),
}

type Program = Vec<Instruction>;

struct Parser {
    index: usize,
    characters: Vec<u8>,
    valid_tokens: HashSet<char>,
}

impl Parser {
    pub fn new() -> Self {
        Parser {
            index: 0,
            characters: vec![],
            valid_tokens: HashSet::from(['.', ',', '>', '<', '+', '-', '[', ']']),
        }
    }

    pub fn parse(&mut self, source: &String) -> Program {
        self.index = 0;
        self.characters = source
            .bytes()
            .filter(|c| self.valid_tokens.contains(&(*c as char)))
            .collect();
        let mut program = Program::new();

        while self.index < self.characters.len() {
            program.push(self.parse_program());
        }

        program
    }

    fn parse_program(&mut self) -> Instruction {
        let c = self.characters[self.index];

        match c {
            b'[' => self.parse_loop(),
            b']' => panic!("Ending loop delimiter found while none were expected."),
            _ => self.parse_operator(),
        }
    }

    fn parse_operator(&mut self) -> Instruction {
        let operator = self.characters[self.index];
        self.index += 1;

        match operator {
            b'>' => Instruction::IncPtr,
            b'<' => Instruction::DecPtr,
            b'+' => Instruction::IncData,
            b'-' => Instruction::DecData,
            b'.' => Instruction::Print,
            b',' => Instruction::Read,
            _ => panic!("Unsupported operator {:?}!", operator),
        }
    }

    fn parse_loop(&mut self) -> Instruction {
        let mut instructions = Vec::<Instruction>::new();
        self.index += 1;

        while self.index < self.characters.len() && self.characters[self.index] != b']' {
            instructions.push(self.parse_program());
        }

        if self.index == self.characters.len() && self.characters[self.index - 1] != b']' {
            panic!("Expected closing delimiter but found none!")
        }

        self.index += 1;

        Instruction::Loop(instructions)
    }
}

#[derive(Debug, PartialEq, Clone)]
enum Opcode {
    /// ip += 1
    IP,
    /// ip -= 1
    DP,
    /// *ip += 1
    ID,
    /// *ip -= 1
    DD,
    /// Print(*ip)
    PR,
    /// *ip = char from STDIN
    RE,
    /// if *ip == 0 { ip = A }
    JZ(i32),
    /// ip = A
    JMP(i32),
}

trait Serialize {
    fn serialize(&self) -> Vec<u16>;
}

///
/// 0000000000000 000
///               ^^^ enum identifer
/// ^^^^^^^^^^^^^ optional numeric identifier
/// enum mapping {
///     0 : IP
///     1 : DP
///     2 : ID
///     3 : DD
///     4 : PR
///     5 : RE
///     6 : JZ
///     7 : JMP
/// }
impl Serialize for Vec<Opcode> {
    fn serialize(&self) -> Vec<u16> {
        let binary = self
            .iter()
            .map(|x| match *x {
                Opcode::IP => 0,
                Opcode::DP => 1,
                Opcode::ID => 2,
                Opcode::DD => 3,
                Opcode::PR => 4,
                Opcode::RE => 5,
                Opcode::JZ(position) => 6 + (position << 3) as u16,
                Opcode::JMP(position) => 7 + (position << 3) as u16,
            })
            .collect();

        binary
    }
}

trait Deserialize {
    fn deserialize(&self) -> Vec<Opcode>;
}

impl Deserialize for Vec<u16> {
    fn deserialize(&self) -> Vec<Opcode> {
        let opcodes = self
            .iter()
            .map(|x| {
                let identifier = x & 7;
                let number = x >> 3;

                match identifier {
                    0 => Opcode::IP,
                    1 => Opcode::DP,
                    2 => Opcode::ID,
                    3 => Opcode::DD,
                    4 => Opcode::PR,
                    5 => Opcode::RE,
                    6 => Opcode::JZ(number as i32),
                    7 => Opcode::JMP(number as i32),
                    _ => panic!("Unknown identifer {:}", identifier),
                }
            })
            .collect();

        opcodes
    }
}

trait Compile {
    fn compile(&self) -> Vec<Opcode>;
}

impl Compile for Program {
    fn compile(&self) -> Vec<Opcode> {
        let mut program: Vec<Opcode> = self.iter().flat_map(|x| x.compile()).collect();

        for i in 0..program.len() {
            match program[i] {
                Opcode::JZ(offset) => program[i] = Opcode::JZ(offset + i as i32),
                Opcode::JMP(offset) => program[i] = Opcode::JMP(offset + i as i32),
                _ => (),
            }
        }

        program
    }
}

impl Compile for Instruction {
    fn compile(&self) -> Vec<Opcode> {
        let compiled_loop: Option<Vec<Opcode>> = match self {
            Instruction::Loop(instructions) => {
                let mut body: Vec<Opcode> =
                    instructions.iter().flat_map(|x| x.compile()).collect();
                body.append(&mut vec![Opcode::JMP(-(body.len() as i32 + 1))]);
                let length = body.len();
                let mut opcodes = vec![Opcode::JZ((length as i32) + 1)];
                opcodes.append(&mut body);
                Some(opcodes)
            }
            _ => None,
        };

        if compiled_loop.is_some() {
            return compiled_loop.unwrap();
        }

        let mut opcodes = Vec::<Opcode>::new();

        opcodes.push(match self {
            Instruction::DecPtr => Opcode::DP,
            Instruction::IncPtr => Opcode::IP,
            Instruction::DecData => Opcode::DD,
            Instruction::IncData => Opcode::ID,
            Instruction::Print => Opcode::PR,
            Instruction::Read => Opcode::RE,
            _ => panic!("Invalid opcode {:?}", self),
        });

        opcodes
    }
}

#[derive(Debug)]
struct VM {
    ip: usize,
    opcodes: Vec<Opcode>,
    dp: usize,
    memory: [i32; 30_000],
}

impl From<&str> for VM {
    fn from(source: &str) -> Self {
        VM::from(&source.to_string())
    }
}

impl From<&String> for VM {
    fn from(source: &String) -> Self {
        let mut parser = Parser::new();
        let ast = parser.parse(source);
        let opcodes = ast.compile();

        VM::from(&opcodes)
    }
}

impl From<&Vec<u16>> for VM {
    fn from(bytecodes: &Vec<u16>) -> Self {
        let opcodes = bytecodes.clone().deserialize();

        VM::from(&opcodes)
    }
}

impl From<&Vec<Opcode>> for VM {
    fn from(opcodes: &Vec<Opcode>) -> Self {
        VM {
            ip: 0,
            opcodes: opcodes.clone(),
            dp: 0,
            memory: [0; 30_000],
        }
    }
}

impl VM {
    pub fn new(opcodes: &Vec<Opcode>) -> Self {
        VM {
            ip: 0,
            opcodes: vec![],
            dp: 0,
            memory: [0; 30_000],
        }
    }

    pub fn execute(&mut self) -> i32 {
        while self.ip < self.opcodes.len() {
            match self.opcodes[self.ip] {
                Opcode::IP => self.dp += 1,
                Opcode::DP => self.dp -= 1,
                Opcode::ID => self.memory[self.dp] += 1,
                Opcode::DD => self.memory[self.dp] -= 1,
                Opcode::JMP(address) => self.ip = address as usize - 1,
                Opcode::PR => print!("{}", self.memory[self.dp] as u8 as char),
                Opcode::RE => {
                    let mut buffer = [0; 1];
                    std::io::Read::read_exact(&mut std::io::stdin(), &mut buffer)
                        .expect("Failed to read input");
                    self.memory[self.dp] = buffer[0] as i32;
                }
                Opcode::JZ(address) => {
                    if self.memory[self.dp] == 0 {
                        self.ip = address as usize - 1
                    }
                }
                _ => panic!("Unrecognized opcode {:?}", self.opcodes[self.ip]),
            }

            self.ip += 1;
        }

        self.memory[self.dp]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_construct_ast() {
        let ast: Program = vec![
            Instruction::Read,
            Instruction::IncPtr,
            Instruction::Loop(vec![Instruction::Read]),
        ];

        assert!(!ast.is_empty());
    }

    #[test]
    fn can_parse_source() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"+-><".into());

        assert_eq!(
            ast,
            vec![
                Instruction::IncData,
                Instruction::DecData,
                Instruction::IncPtr,
                Instruction::DecPtr
            ]
        );
    }

    #[test]
    fn can_parse_complex_source() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"+++++[]+++---[----++]---[+[][][][[[[]]]]]+".into());

        assert!(!ast.is_empty())
    }

    #[test]
    fn can_compile_ast() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"+-><".into());

        let compiled = ast.compile();

        assert_eq!(
            compiled,
            vec![Opcode::ID, Opcode::DD, Opcode::IP, Opcode::DP]
        )
    }

    #[test]
    fn can_serialize_opcodes() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"+-><".into());

        let compiled = ast.compile();
        let serialized = compiled.serialize();

        assert_eq!(serialized, vec![2, 3, 0, 1]);
    }

    #[test]
    fn can_deserialize_bytecodes() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"+-><".into());

        let compiled = ast.compile();
        let serialized = compiled.serialize();

        assert_eq!(serialized.deserialize(), compiled)
    }

    #[test]
    fn can_deserialize_complex_bytecodes() {
        let mut parser = Parser::new();
        let ast = parser.parse(&"[[[[[[[[[+][[[-]]][+]]]]]]]]".into());

        let compiled = ast.compile();
        let serialized = compiled.serialize();

        assert_eq!(serialized.deserialize(), compiled)
    }

    #[test]
    fn can_run_program() {
        let mut vm = VM::from("++++++++++[->++++<]>++");
        assert_eq!(vm.execute(), 42);
    }

    #[test]
    fn can_handle_hell() {
        let source = "
        [
    This routine is a demonstration of checking for the three cell sizes
    that are normal for Brainfuck. The demo code also checks for bugs
    that have been noted in various interpreters and compilers.

    It should print one of three slight variations of Hello world followed
    by an exclamation point then the maximum cell value (if it's less than a
    few thousand) and a newline.

    If the interpreter is broken in some way it can print a lot of other
    different strings and frequently causes the interpreter to crash.

    It does work correctly with 'bignum' cells.
]
+>>

	This code runs at pointer offset two and unknown bit width; don't
	assume you have more that eight bits

	======= DEMO CODE =======
	First just print Hello

	Notice that I reset the cells despite knowing that they are zero
	this is a test for proper functioning of the ability to skip over
	a loop that's never executed but isn't actually a comment loop

	Secondly there's a NOP movement between the two 'l' characters

	Also there's some commented out code afterwards

	>[-]<[-]++++++++[->+++++++++<]>.----[--<+++>]<-.+++++++.><.+++.
	[-][[-]>[-]+++++++++[<+++++>-]<+...--------------.>++++++++++[<+
	++++>-]<.+++.-------.>+++++++++[<----->-]<.-.>++++++++[<+++++++>
	-]<++.-----------.--.-----------.+++++++.----.++++++++++++++.>++
	++++++++[<----->-]<..[-]++++++++++.[-]+++++++[.,]-]

	===== END DEMO CODE =====
<<-

Calculate the value 256 and test if it's zero
If the interpreter errors on overflow this is where it'll happen
++++++++[>++++++++<-]>[<++++>-]
+<[>-<
Multiply by 256 again to get 65536
[>++++<-]>[<++++++++>-]<[>++++++++<-]
+>[>
	Cells should be 32bits at this point

	The pointer is at cell two and you can continue your code confident
	that there are big cells

	======= DEMO CODE =======
	This code rechecks that the test cells are in fact nonzero
	If the compiler notices the above is constant but doesn't
	properly wrap the values this will generate an incorrect
	string

	An optimisation barrier; unbalanced loops aren't easy
	>+[<]>-<

	Print a message
	++>[-]++++++[<+++++++>-]<.------------.[-]
	<[>+<[-]]>
	++++++++>[-]++++++++++[<+++++++++++>-]<.--------.+++.------.
	--------.[-]

	===== END DEMO CODE =====

<[-]<[-]>] <[>>
	Cells should be 16bits at this point

	The pointer is at cell two and you can continue your code confident
	that there are medium sized cells; you can use all the cells on the
	tape but it is recommended that you leave the first two alone

	If you need 32bit cells you'll have to use a BF doubler

	======= DEMO CODE =======
	Space
	++>[-]+++++[<++++++>-]<.[-]

	I'm rechecking that the cells are 16 bits
	this condition should always be true

	+>>++++[-<<[->++++<]>[-<+>]>]< + <[ >>

	    Print a message
	    >[-]++++++++++[<+++++++++++>-]<+++++++++.--------.
	    +++.------.--------.[-]

	<[-]<[-] ] >[> > Dead code here
	    This should never be executed because it's in an 8bit zone hidden
	    within a 16bit zone; a really good compiler should delete this
	    If you see this message you have dead code walking

	    Print a message
	    [-]>[-]+++++++++[<++++++++++>-]<.
	    >++++[<+++++>-]<+.--.-----------.+++++++.----.
	    [-]

	<<[-]]<
	===== END DEMO CODE =====

<<[-]] >[-]< ] >[>
	Cells should be 8bits at this point

	The pointer is at cell two but you only have 8 bits cells
	and it's time to use the really big and slow BF quad encoding

	======= DEMO CODE =======

	A broken wrapping check
	+++++[>++++<-]>[<+++++++++++++>-]<----[[-]>[-]+++++[<++++++>-]<++.
	>+++++[<+++++++>-]<.>++++++[<+++++++>-]<+++++.>++++[<---->-]<-.++.
	++++++++.------.-.[-]]

	Space
	++>[-]+++++[<++++++>-]<.[-]

	An exponent checker for github user btzy
	>++[>++<-]>[<<+>>[-<<[>++++<-]>[<++++>-]>]]<<[>++++[>---<++++]>++.
	[<++>+]<.[>+<------]>.+++.[<--->++]<--.[-]<[-]]

        Another dead code check
        [-]>[-]>[-]<++[>++++++++<-]>[<++++++++>-]<[>++++++++<-]>[<++++++++>-
        ]<[<++++++++>-]<[[-]>[-]+++++++++[<++++++++++>-]<.>++++[<+++++>-]<+.
        --.-----------.+++++++.----.>>[-]<+++++[>++++++<-]>++.<<[-]]

	Print a message
	[-] <[>+<[-]]> +++++>[-]+++++++++[<+++++++++>-]<.
	>++++[<++++++>-]<.+++.------.--------.
	[-]
	===== END DEMO CODE =====

<[-]]<

+[[>]<-]    Check unbalanced loops are ok

>>
	======= DEMO CODE =======
	Back out and print the last two characters

	[<[[<[[<[[<[,]]]<]<]<]<][ Deep nesting non-comment comment loop ]]

	Check that an offset of 128 will work
	+>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>-[+<-]

	And back
	+++[->++++++<]>[-<+++++++>]<[->>[>]+[<]<]>>[->]<<<<<<<<<<<<<<<<<<<<<
	<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

	And inside a loop
	--[>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>++<<<
	<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<+]+>----[++
	++>----]-[+<-]

	This is a simple multiply loop that looks like it goes off the
	start of the tape
	+[>]<- [-
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
	    ++++
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	    >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
	]

	[ Check there are enough cells. This takes 18569597 steps. ]
	[
	    >++++++[<+++>-]<+[>+++++++++<-]>+[[->+>+<<]>>
	    [-<<+>>]<[<[->>+<<]+>[->>+<<]+[>]<-]<-]<[-<]
	]

	This loop is a bug check for handling of nested loops; it goes
	round the outer loop twice and the inner loop is skipped on the
	first pass but run on the second

	BTW: It's unlikely that an optimiser will notice how this works

	>
	    +[>[
		Print the exclamation point
		[-]+++>
		[-]+++++ +#-
		[<+++2+++>-]<
		.

	    <[-]>[-]]+<]
	<

	Clean up any debris
	++++++++[[>]+[<]>-]>[>]<[[-]<]

	This is a hard optimisation barrier
	It contains several difficult to 'prove' constructions close together
	and is likely to prevent almost all forms of optimisation
	+[[>]<-[,]+[>]<-[]]

	This part finds the actual value that the cell wraps at; even
	if it's not one of the standard ones; but it gets bored after
	a few thousand: any higher and we print nothing

	This has a reasonably deep nested loop and a couple of loops
	that have unbalanced pointer movements

	Find maxint (if small)
	[-]>[-]>[-]>[-]>[-]>[-]>[-]>[-]<<<<<<<++++[->>++++>>++++>>++
	++<<<<<<]++++++++++++++>>>>+>>++<<<<<<[->>[->+>[->+>[->+>+[>
	>>+<<]>>[-<<+>]<-[<<<[-]<<[-]<<[-]<<[-]>>>[-]>>[-]>>[-]>->+]
	<<<]>[-<+>]<<<]>[-<+>]<<<]>[-<+>]<<<]>+>[[-]<->]<[->>>>>>>[-
	<<<<<<<<+>>>>>>>>]<<<<<<<]<

	The number is only printed if we found the actual maxint
	>+<[
	    Space
	    >[-]>[-]+++++[<++++++>-]<++.[-]<

	    Print the number
	    [[->>+<<]>>[-<++>[-<+>[-<+>[-<+>[-<+>[-<+>[-<+>[-<+>[-<+>[<[-]+>
	    ->+<[<-]]]]]]]]]]>]<<[>++++++[<++++++++>-]<-.[-]<]]

	]

	Check if we should have had a value but didn't
	>[
	    >[-]>[-]++++[<++++++++>-]<[<++++++++>-]>+++[<++++++++>-]<+++++++
	    [<-------->-]<------->+<[[-]>-<]>[>[-]<[-]++++[->++++++++<]>.+++
	    +++[-<++>]<.[-->+++<]>++.<++++[>----<-]>.[-]<]<

	    [-]>[-]++++++++[<++++++++>-]<[>++++<-]+>[<->[-]]<[>[-]<[-]++++[-
	    >++++++++<]>.---[-<+++>]<.---.--------------.[-->+<]>--.[-]<]
	]<

	Clean up any debris
	++++++++[[>]+[<]>-]>[>]<[[-]<]

	One last thing: an exclamation point is not a valid BF instruction!

	Print the newline
	[-]++++++++++.[-]
	[
	    Oh, and now that I can use ! the string you see should be one of:
	    Hello World! 255
	    Hello world! 65535
	    Hello, world!

	    And it should be followed by a newline.
	]

	===== END DEMO CODE =====

<<  Finish at cell zero
        ";

        let mut parser = Parser::new();

        let ast = parser.parse(&source.into());

        assert!(!ast.is_empty());

        let opcodes = ast.compile();

        assert!(!opcodes.is_empty());

        let mut vm = VM::from(&opcodes);

        vm.execute();

        assert!(true);
    }
}
