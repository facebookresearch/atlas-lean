# GTR inference corollary

**GTR inference corollary** (identifiability + sampling law ⇒ consistency). Let `Θ` be a
compact parameter space with a continuous site-pattern law `law`, and let the true parameter
`θ₀` be identified up to the class `E` of symmetry-equivalent parameters
(`hId : law θ = law θ₀ → θ ∈ E`, the T66 identifiability input). If the alignment columns are
pairwise independent and identically distributed with `P (X 0 = a) = law θ₀ a`, then every
minimum-distance estimator `est` for the empirical site-pattern frequencies satisfies
`infDist (est n) E → 0` in probability.
