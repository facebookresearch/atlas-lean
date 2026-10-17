---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.mul_run
---

# Mul run

`c += a · b`: a `for` loop over `a` (index on `ad`) whose body copies `b` into `c` through
`t`. Exactly `m (2n + 3) + m + 2` steps; all stacks but `c` end as they started.

## Depends on

- [Flag](../part-01/flag.md)
- [Run](../part-01/run.md)
- [Cnt](../part-01/cnt.md)
- [For Head](../part-01/for-head.md)
- [Xfer](../part-01/xfer.md)

## Proof depends on

- [Copy run](copy-run.md)
- [For Loop run](../part-01/for-loop-run.md)
- [Sum From](../part-01/sum-from.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
