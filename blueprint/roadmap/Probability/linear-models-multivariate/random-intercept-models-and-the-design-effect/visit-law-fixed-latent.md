# Fixed-latent visit law

At a fixed latent `z`, the visit
error vector `e` with independent centered Gaussian coordinates
(`Measure.pi (fun j : Fin n => gaussianReal (0 : ℝ) (v j))`) pushed through the
coordinatewise map `e ↦ (fun j => Real.exp (m j + e j))` is exactly
the product of the per-visit lognormal laws
`Measure.pi (fun j : Fin n => (gaussianReal (m j) (v j)).map Real.exp)`:
each visit is the exp-pushforward of its Gaussian (the lognormal
visit law), with mutual independence of visit errors.
