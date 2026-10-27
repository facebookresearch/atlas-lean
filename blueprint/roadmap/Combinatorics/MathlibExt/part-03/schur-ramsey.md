---
article_id: af_a07ca8c01e2aeb8bb85955c0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.schur_ramsey
---

# Schur Ramsey

Schur's theorem (Ramsey form): for every `r ≥ 1` there is a bound `S` such that any
`r`-coloring of `Finset.Icc 1 S` contains a monochromatic solution to `x + y = z` with
positive integers `x y z` (not necessarily distinct). The witness is only a forcing bound,
obtained from `MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform` by coloring each pair with
the color of its difference; it is not the Schur number `S(r)`, the largest `S` that admits a
coloring with no such solution.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ramsey](ramsey-two-uniform.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SchurRamsey](../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Schur%27s_theorem (statement schur-ramsey-s1).
