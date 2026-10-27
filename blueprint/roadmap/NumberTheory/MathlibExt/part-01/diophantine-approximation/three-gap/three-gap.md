---
article_id: af_83477e6fd171007f5b0daf0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.three_gap
---

# Three gap

Three-gap theorem (statement `three-gap-s1`): the fractional parts of the
multiples `0, α, 2 * α, ..., (n - 1) * α` cut the circle into `n` arcs taking
at most three distinct lengths. Irrationality ensures the indexed points are distinct.
When exactly three lengths occur, the largest is the sum of the other two.

Proof: We formalize the standard successor argument of Sós (1958) and Świerczkowski (1959),
following Alessandri and Berthé, *Three distance theorems and combinatorics on words*, §2.

## Depends on

- [Is Three Gap Length](is-three-gap-length.md)

## Proof depends on

- [Is Three Gap Point](is-three-gap-point.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DiophantineApproximation.ThreeGap](../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Three-gap_theorem.
