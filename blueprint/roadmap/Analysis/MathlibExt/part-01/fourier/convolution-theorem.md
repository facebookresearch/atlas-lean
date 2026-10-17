---
article_id: af_7dc2fca891b04a9558eebdb1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.convolution_theorem
---

# Convolution Theorem

Convolution theorem: the Fourier transform turns convolution into pointwise
product. For a sigma-finite translation-invariant Borel measure `μ` and integrable
`f g : ℝ → ℂ`, the Fourier transform of the Mathlib convolution
`(f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, μ] g)` at `w` equals the pointwise product
of the Fourier transforms at `w`.

Proof: The proof uses convolution-integrand integrability, Fubini, translation invariance, and
character factorization, following Stein--Shakarchi, Ch. 5, Prop. 1.11, and Mathlib's
`Real.fourier_bilin_convolution_eq_integral`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.ConvolutionTheorem](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Convolution_theorem (statement `convolution-theorem-s1`).
