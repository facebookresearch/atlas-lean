---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.forLoop_run
---

# For Loop run

`for i < n do body`, with `c` holding `n - i` (units still to do) and `cd` holding the
index `i + 1` while the body of iteration `i` runs. The body must preserve `c` and `cd`, end at
`head`, and take `cost i` steps; `P` is the caller's invariant, which must not depend on `c`, `cd`.
Total: `Σ_{i<n} (cost i + 1) + n + 2` steps, and afterwards `c = n`, `cd = []` again.

## Depends on

- [Flag](flag.md)
- [Run](run.md)
- [Cnt](cnt.md)
- [For Head](for-head.md)
- [Sum From](sum-from.md)
- [Xfer](xfer.md)

## Proof depends on

- [Single](single.md)
- [Add U](add-u.md)
- [Xfer run](xfer-run.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
