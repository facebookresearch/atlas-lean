---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.emitDiff_run
---

# Emit Diff run

Gap emission. From `P = q + gap + 1` and `Q = q`: repeatedly decrement `P`, compare with `Q`
(non-destructively), and while they differ prepend `ys` to `o`. Ends with `P = q`, having
prepended `rep ys gap`. Labels: `dec` (decrement), `cmpL` + restore families `r`, `rB` (the
comparison), `emitL` (prepend). `ifZero` is unreachable.

## Depends on

- [Flag](../part-01/flag.md)
- [Run](../part-01/run.md)
- [Cmp Step](../part-01/cmp-step.md)
- [Cnt](../part-01/cnt.md)
- [Decr](../part-01/decr.md)
- [Emit R](emit-r.md)
- [Rep](rep.md)
- [Xfer](../part-01/xfer.md)

## Proof depends on

- [Single](../part-01/single.md)
- [Cmp run](../part-01/cmp-run.md)
- [Emit](../part-01/emit.md)
- [Push List](../part-01/push-list.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
