# Strong Markov property, integrated form

Let `X` be a continuous process adapted to `ℱ`
under a finite measure `μ` that is Markov with respect to `ℱ` with the neutral Wright–Fisher
semigroup, in the form of `NeutralMartingaleProblem.isWrightFisherSolution_zero_of_markov`.
Then for every `ℱ`-stopping time `τ`, every `A ∈ ℱ_τ`, every `t ≥ 0` and every continuous `g`
on `[0, 1]`,
`∫_{A ∩ {τ < ∞}} g (X (τ + t)) dμ = ∫_{A ∩ {τ < ∞}} (wfSemigroup t g) (X τ) dμ`.

## Sources

- Ethier & Kurtz (1986), ch. 4, Thm. 2.7; Revuz & Yor (1999), ch. III, §3 (dyadic approximation of `τ` from above and right continuity of the paths).
