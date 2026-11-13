# Neutral Wright–Fisher martingale problem from the Markov property

Let `X` be a
continuous `[0, 1]`-valued process adapted to a filtration `ℱ` under a finite measure `μ`, and
suppose `X` is Markov with respect to `ℱ` with the neutral Wright–Fisher transition semigroup:
for `s ≤ t` and every continuous `g` on `[0, 1]`,
`μ[g (X t) | ℱ s] = (wfSemigroup (t - s) g) (X s)` almost surely. Then `X` solves the neutral
Wright–Fisher martingale problem `IsWrightFisherSolution 0 ℱ μ X`: for every `C²` test function
`f`, `f (X t) - f (X 0) - ∫₀ᵗ (x (1 - x) / 2 · f'') (X s) ds` is an `ℱ`-martingale.

The semigroup is only known to have the generator `x (1 - x) / 2 · p''` on polynomials
(`hasDerivAt_wfSemigroup_toContinuousMapOn`). The proof derives the martingale identity on
polynomials from the Markov property, Fubini's theorem and the semigroup identity
`wfSemigroup_sub_eq_integral`, and passes to `C²` test functions through the simultaneous
uniform approximation of `f` and `f''` on `[0, 1]` by polynomials
(`exists_polynomial_near_contDiff_two`), the error terms being bounded uniformly on the
sample space.

## Sources

- Ethier & Kurtz (1986), ch. 4, Prop. 1.7 (Markov processes solve the martingale problem for their generator), and ch. 10 (polynomials as a core for the Wright–Fisher generator, here replaced by direct `C²` approximation).
