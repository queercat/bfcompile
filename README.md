# Compile Fuck

This is a Brainfuck bytecode compiler and virtual machine written in Rust. It parses Brainfuck source code, converts it into a series of opcodes, and executes the program on a virtual machine. The interpreter also supports serialization and deserialization of opcodes for saving or sharing bytecode as binary data.

## Opcode Table

The following table maps each opcode to its corresponding number and description:

| Opcode Identifier | Opcode Name | Description                                               |
|-------------------|-------------|-----------------------------------------------------------|
| 0                 | IP          | Increment the data pointer (`dp += 1`)                     |
| 1                 | DP          | Decrement the data pointer (`dp -= 1`)                     |
| 2                 | ID          | Increment the value at the data pointer (`*dp += 1`)       |
| 3                 | DD          | Decrement the value at the data pointer (`*dp -= 1`)       |
| 4                 | PR          | Print the value at the data pointer (`print(*dp as char)`) |
| 5                 | RE          | Read a character from stdin and store it at the data pointer (`*dp = stdin`) |
| 6                 | JZ          | Jump to the specified address if the value at the data pointer is zero (`if *dp == 0 { ip = address }`) |
| 7                 | JMP         | Jump to the specified address unconditionally (`ip = address`) |

## Deserialization Format

The deserialization format represents opcodes as 16-bit unsigned integers (`u16`), where the lower 3 bits represent the opcode identifier and the upper 13 bits represent the numeric value (for `JZ` and `JMP` opcodes). Here’s the breakdown:

```
0000000000000 000
              ^^^ Opcode identifier
^^^^^^^^^^^^^ Address for JZ / JMP
```

## Running Tests
```sh
git clone https://github.com/queercat/compile-fuck
cd compile-fuck
cargo test
```
