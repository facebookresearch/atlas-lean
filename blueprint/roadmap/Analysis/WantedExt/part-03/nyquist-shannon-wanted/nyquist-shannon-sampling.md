---
article_id: af_20c5e2a574ada5f10f12590b
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.NyquistShannonWanted.Analysis.NyquistShannon.nyquist_shannon_sampling
---

# Nyquist--Shannon sampling theorem / Whittaker--Shannon interpolation formula

**Nyquist--Shannon sampling theorem / Whittaker--Shannon interpolation
formula** for Schwartz functions with Fourier support in the mathlib-convention
Nyquist band `[-1/2, 1/2]`.

The explicit `Summable` conjunct records the convergence content of the
cardinal series, rather than relying only on Lean's total `tsum`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.NyquistShannonWanted](../../../../../sources/v2/WantedExt.md)
- C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179. Via leanprover/lean-eval@38361be, problem `nyquist_shannon_sampling`.
