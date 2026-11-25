# Pointwise bias of the KDE vanishes

Assume `Measurable f`, `∀ x, 0 ≤ f x`, `∀ x, f x ≤ B`, `Measurable K`, `Integrable K`, `∫ u, K u = 1`, `0 < n` and `∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P`.

**Pointwise bias of the KDE vanishes** at a continuity point of the density: the bias
`(∫ ω, kde K h X t ∂P) - f t` tends to `0` as `h → 0⁺`.
