---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.copy_run
---

# Copy run

Non-destructive `c += a` through the empty scratch stack `t`: `xfer a → [c, t]`, then
`xfer t → [a]`. Exactly `2m + 2` steps.

## Depends on

- [Flag](../part-01/flag.md)
- [Run](../part-01/run.md)
- [Cnt](../part-01/cnt.md)
- [Xfer](../part-01/xfer.md)

## Proof depends on

- [Add U](../part-01/add-u.md)
- [Xfer run](../part-01/xfer-run.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
