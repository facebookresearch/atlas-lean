# Local Fourier transform

`tateFourier ψ μ f y = ∫ x, f x * ψ (x * y) ∂μ`, in Tate's
convention: the kernel `ψ (x * y)`, with a plus sign, and no normalizing constant.
`NumberField.AdelicFourier.fourierIntegral` uses the kernel `ψ (-(x * y))`, so
`tateFourier ψ μ f y = fourierIntegral ψ μ f (-y)` (`tateFourier_eq_fourierIntegral_neg`).
For any additive character and measure this is a Bochner integral, `0` where the integrand
is not integrable; it is Tate's Fourier transform for a continuous nontrivial `ψ` and an
additive Haar measure `μ`.
