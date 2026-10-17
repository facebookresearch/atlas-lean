---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.moveB
---

# Move B

Loop: while the top of `a` is a bit, pop it and push its re-encoding `g bit` onto `b`; at a
marker or an empty stack go to `next`.

## Depends on

- [Flag](../program/part-01/flag.md)

## Proof depends on

- [Bit Of](bit-of.md)
- [Is Bit](is-bit.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
