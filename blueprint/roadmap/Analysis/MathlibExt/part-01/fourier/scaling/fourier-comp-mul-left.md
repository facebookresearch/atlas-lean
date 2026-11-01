---
article_id: af_ec5a21b6f782147da52921d7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Real.fourier_comp_mul_left
---

# Fourier comp mul left

Fourier transform of a dilated function: scaling `x ↦ f (a * x)` by
`a ≠ 0` scales the transform by `|a|⁻¹` and dilates frequencies by `a⁻¹`.
No integrability hypothesis is needed because Mathlib's Bochner integral is
totalized, so the identity also uses that convention for nonintegrable
functions.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.Scaling](../../../../../../sources/v2/MathlibExt.md)
