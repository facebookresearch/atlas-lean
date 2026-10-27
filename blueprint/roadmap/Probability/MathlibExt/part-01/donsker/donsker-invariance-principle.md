---
article_id: af_16e3e3d83e0f0674793d3eed
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.DonskerWanted.donsker_invariance_principle
---

# Donsker invariance principle

If `X : ℕ → Ω → ℝ` is i.i.d. with mean `0`, variance `1` and `MemLp` `2`, then for any Brownian
motion `B` with `IsBrownianReal B P'` there exists `Y : Ω' → C([0, 1], ℝ)` restricting to `B` a.e.
on `[0, 1]` such that `donskerProcess n X` converges in distribution to `Y`. Source: M. D.
Donsker, An invariance principle for certain probability limit theorems, Mem. Amer. Math. Soc. 6
(1951); extension Prohorov 1956 to Polish; textbook in Billingsley, Convergence of Probability
Measures, 2nd ed., Kallenberg, Foundations of Modern Probability; Lean is `C(Icc 0 1, ℝ)`
polygonal process with `MemLp 2`, mean-zero variance-one standardization.

Proof: The route combines finite-dimensional convergence from the central limit theorem,
tightness from a maximal inequality and a modulus-of-continuity criterion, Prokhorov's theorem,
and uniqueness of laws on `C([0,1])` from finite-dimensional distributions.

## Depends on

- [Donsker Process](donsker-process.md)
- [Icc To NNReal](icc-to-nnreal.md)

## Proof depends on

- [Continuous Map measure ext of finset eval](continuous-map-measure-ext-of-finset-eva.md)
- [Donsker Process apply eq](donsker-process-apply-eq.md)
- [Donsker Weight CM](donsker-weight-cm.md)
- [Etemadi maximal inequality](etemadi-maximal-inequality.md)

## Sources

- [MathlibExt, MathlibExt.Probability.Donsker](../../../../../sources/v2/MathlibExt.md)
