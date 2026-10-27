---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.cmpB_prefix
---

# Cmp B prefix

Common leading bits: if both blocks start with the bits `p`, `cmpB` pops them in exactly
`p.length` steps, pushing them onto the scratch stacks, and is back at its own label.

## Depends on

- [Distinct4](distinct4.md)
- [Flag](../program/part-01/flag.md)
- [Is Bit Block](is-bit-block.md)
- [Run](../program/part-01/run.md)
- [Cmp B](cmp-b.md)

## Proof depends on

- [Bit Of](bit-of.md)
- [Is Bit](is-bit.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
