---
article_id: af_a5c06f07c48a42e9b20822ff
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.BochnerWanted.bochner
---

# Bochner

A function `f : ℝ → ℂ` is continuous, `f 0 = 1`, and positive-definite `∀ n x c, S = ∑_i∑_j
star(c_i) * c_j * f(x_i-x_j) satisfies S.im = 0 ∧ 0 ≤ S.re` iff there exists Borel probability `μ
: Measure ℝ` with `f t = charFun μ t` for all `t`. Source: Bochner's theorem on positive-definite
functions, S. Bochner, Vorlesungen über Fouriersche Integrale 1932 and Math. Ann. 108 (1933); see
Folland, Abstract Harmonic Analysis, Fourier Analysis on Groups; Lean is ℝ→ℂ iff version
continuous f 0=1 positive- definite via double sum iff ∃ Borel probability μ with f = charFun μ,
fixed +I sign via charFun.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.Bochner](../../../../../sources/v2/MathlibExt.md)
