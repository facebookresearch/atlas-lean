---
article_id: af_19d841b8815cbe10d5fc8b13
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Fourier.fourierLaplace_ofReal
---

# Fourier Laplace of Real

On the real axis `fourierLaplace` coincides with Mathlib's Fourier integral
for the standard `2π` additive character `Real.fourierChar`.

More precisely, for `r : ℝ` (coerced to `ℂ`) we have
`fourierLaplace f (r : ℂ) = fourierIntegral Real.fourierChar volume f r`.

## Depends on

- [Fourier Laplace](fourier-laplace.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FourierLaplace](../../../../../../sources/v2/MathlibExt.md)
