---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.moveB_run
---

# Move B run

`moveB` moves the bit block `p` of `a` onto `b` (reversed, re-encoded by `g`) in exactly
`p.length + 1` steps, leaving the rest of `a` and every other stack unchanged.

## Depends on

- [Ends Bit Block](ends-bit-block.md)
- [Flag](../program/part-01/flag.md)
- [Is Bit Block](is-bit-block.md)
- [Run](../program/part-01/run.md)
- [Move B](move-b.md)

## Proof depends on

- [Single](../program/part-01/single.md)
- [Bit Of](bit-of.md)
- [Is Bit](is-bit.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
