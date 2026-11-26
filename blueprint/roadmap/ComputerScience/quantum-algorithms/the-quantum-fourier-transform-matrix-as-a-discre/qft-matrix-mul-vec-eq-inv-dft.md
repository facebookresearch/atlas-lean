# Quantum Fourier transform as an inverse discrete Fourier transform

Let `q ≠ 0`. For every `Φ : ZMod q → ℂ` and `k : Fin q`, the quantum Fourier
transform matrix applied to the vector `Φ` (indexed by `Fin q ≃ ZMod q`) has
`k`-th entry `√q * dft⁻¹ Φ k`, where `dft⁻¹ Φ k = (1 / q) ∑ j, exp (2πi j k
/ q) Φ j` is the inverse discrete Fourier transform on `ZMod q`.

Here `qftMatrix q` is the `q × q` complex matrix with entries `qftMatrix q j
k = (√q)⁻¹ exp (2πi j k / q)`.
