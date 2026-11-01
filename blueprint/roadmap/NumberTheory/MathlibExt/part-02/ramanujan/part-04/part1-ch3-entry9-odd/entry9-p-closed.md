---
article_id: af_94e4df97c342b8d966fc2f4d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9Odd.entry9_P_closed
---

# Entry9 P closed

Closed form of `entry9_P` off the poles: with `w = (z + a) / b` in the sector
`|arg w| ≤ π - ε`, `‖w‖ > 0`, and no vanishing factor `w + (r + 1)`, the defining product
series equals `Complex.exp (-x)` times the factorial-weighted series
`∑' m, x^(m+1) / (m! * (z + (a + b * (m + 1))))`. The two exponential series multiplied in
the proof are absolutely summable, so this is the source's value of the Entry 9(i)
expression on this domain.

## Depends on

- [Entry9 P](entry9-p.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9Odd](../../../../../../../sources/v2/MathlibExt.md)
