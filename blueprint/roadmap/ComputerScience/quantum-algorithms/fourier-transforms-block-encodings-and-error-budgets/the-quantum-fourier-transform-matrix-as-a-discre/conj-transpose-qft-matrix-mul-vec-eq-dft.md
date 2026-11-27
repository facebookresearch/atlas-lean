# Inverse quantum Fourier transform as a discrete Fourier transform

Let `q ≠ 0`. For every `Φ : ZMod q → ℂ` and `k : Fin q`, the conjugate
transpose of the quantum Fourier transform matrix applied to the vector `Φ`
(indexed by `Fin q ≃ ZMod q`) has `k`-th entry `(√q)⁻¹ * dft Φ k`, where
`dft Φ k = ∑ j, exp (-2πi j k / q) Φ j` is the discrete Fourier transform on
`ZMod q`.

Here `qftMatrix q` is the `q × q` complex matrix with entries `qftMatrix q j
k = (√q)⁻¹ exp (2πi j k / q)`.
