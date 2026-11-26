# Inner product of scaled Fourier amplitude rows

For a complex number `ω`, a real scale `s` and natural numbers `N`, `j₁`,
`j₂`, the inner product `∑ k < N, conj (qftAmp ω s j₁ k) * qftAmp ω s j₂ k`
of the amplitude rows of the inputs `j₁` and `j₂` equals `s ^ 2` times the
unscaled sum `∑ k < N, conj (ω ^ (j₁ * k)) * ω ^ (j₂ * k)`.
