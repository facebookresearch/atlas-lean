---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.forLoop_le
---

# For Loop le

`forLoop_reach` with a time bound: if every iteration of the body takes at most `B` steps,
the loop takes at most `n (B + 1) + n + 2`.

## Depends on

- [Flag](../part-01/flag.md)
- [Run Le](run-le.md)
- [Cnt](../part-01/cnt.md)
- [For Head](../part-01/for-head.md)
- [Xfer](../part-01/xfer.md)

## Proof depends on

- [Run](../part-01/run.md)
- [Single](../part-01/single.md)
- [Add U](../part-01/add-u.md)
- [Xfer run](../part-01/xfer-run.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
