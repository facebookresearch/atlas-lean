# Fourier transform in angular frequency

The Fourier transform in angular frequency `ω`: `∫ t, e^{-iωt} * f t`. Mathlib's `𝓕` uses frequency in hertz (`e^{-2πitξ}`), so the angular form at
`ω` is the hertz form at `ω / (2π)`; see `fourierAngular_eq`.
