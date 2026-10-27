---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.cmpB
---

# Cmp B

Compare the bit blocks of `a` and `b`. While both tops are equal bits, pop them and push the
bit onto the scratch stacks `ta` (via `ea`) and `tb` (via `eb`). When both blocks end together go
to `eqL`; on a mismatch (different bits, or one block ending first) go to `neL` without popping.

## Depends on

- [Flag](../program/part-01/flag.md)

## Proof depends on

- [Bit Of](bit-of.md)
- [Is Bit](is-bit.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
