---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.cmpB_last
---

# Cmp B last

The deciding step: when the tops of `a` and `b` are not two equal bits, `cmpB` takes one step
to `eqL` if both blocks have ended and to `neL` otherwise, changing no stack.

## Depends on

- [Flag](../program/part-01/flag.md)
- [Run](../program/part-01/run.md)
- [Cmp B](cmp-b.md)

## Proof depends on

- [Single](../program/part-01/single.md)
- [Bit Of](bit-of.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
