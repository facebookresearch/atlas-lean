---
article_id: af_90fd8bc2121a5975a30ed00a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted.josefson_nissenzweig
---

# Josefson Nissenzweig

If `E` is an infinite-dimensional Banach space over `𝕜 = ℝ` or `ℂ`, then its strong dual contains
a sequence of norm-one functionals that converges weak-star to zero, i.e. `‖φ n‖ = 1` for all `n`
and `(φ n) x → 0` for every `x : E`. Source: B. Josefson, Weak sequential convergence in the
dual of a Banach space does not imply norm convergence, Bull. Amer. Math. Soc. 81 (1975),
166–168, DOI 10.1090/S0002-9904-1975-13691-3; and A. Nissenzweig, w* sequential convergence,
Israel J. Math. 22 (1975), 266–272, DOI 10.1007/BF02761594, Josefson-Nissenzweig theorem;
Diestel, Sequences and Series; Lean states `RCLike` infinite-dimensional Banach case with
`‖φ n‖=1` and pointwise weak-star nullness.

Proof: We apply Rosenthal's `ℓ¹` dichotomy to a separated dual sequence, then use the stable-block
and Banach-limit/Rademacher route of Hagler--Johnson (1977) and Behrends (1995).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Banach Limit](banach-limit.md)
- [Has Uniform L1 Lower Bound](../part-02/rosenthal-l1/has-uniform-l1-lower-bound.md)
- [Rosenthal l1](../part-02/rosenthal-l1/rosenthal-l1.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweig](../../../../../../sources/v2/MathlibExt.md)
