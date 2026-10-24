---
article_id: af_e858f327d3864e1b0c044fd0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.FieldTheory.HermiteDickson.hermite_dickson_permutation_criterion
---

# Hermite Dickson

Hermite–Dickson criterion: `f ∈ Fq[X]` over a finite field `Fq` of characteristic `p`
is a permutation polynomial (evaluation map `x ↦ f.eval x` bijective) iff (1) `f`
has exactly one root in `Fq`, and (2) for each `1 ≤ t ≤ q - 2` with `p ∤ t`, the
remainder of `f ^ t` upon division by `X ^ q - X` has `natDegree ≤ q - 2`, where
`q = Fintype.card Fq`.

## Depends on

- [Is Permutation Polynomial](finite/permutation-polynomial/is-permutation-polynomial.md)

## Sources

- [MathlibExt, MathlibExt.FieldTheory.HermiteDickson](../../../sources/v2/MathlibExt.md)
- Brian G. Kronenthal, "An Integer Sequence Motivated by Generalized Quadrangles", Journal of Integer Sequences 18 (2015), Article 15.7.8. Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL18/Kronenthal/kron3.tex Hermite–Dickson statement at source lines 120–126. Full source SHA-256: 4968a89e5a6c165ef1c2ab57a9eb6be1a4852e1bc905ec796b3c9abf2158a78d Normalized no-final-newline source-span SHA-256: ddd646ddcecd21e43eeb4e08d3c2405988e7ff842268dd6020ed2d7e603314af
