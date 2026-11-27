# DDPM sampler step

One step of the DDPM sampler with the score value frozen at the start
of the step: the law of `e^h x + 2 (e^h - 1) σ x + √(e^{2h} - 1) ξ` for `x ∼ μ` and an independent
standard Gaussian `ξ`, the closed-form solution of equation (2.8) of Chen et al.
(arXiv:2209.11215v3) over one step. If the update map is not a.e.-measurable, `Measure.map` falls
back to a Dirac mass. Only steps `h ≥ 0` are meaningful: for `h < 0`, `e^{2h} - 1` is negative and
its `Real.sqrt` is `0`.
