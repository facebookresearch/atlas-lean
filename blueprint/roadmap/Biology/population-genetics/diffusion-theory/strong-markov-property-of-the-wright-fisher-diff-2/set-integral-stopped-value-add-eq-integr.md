# Strong Markov property for a Feller kernel family, integrated form

Let `X` be a
continuous process adapted to `ℱ` under a finite measure `μ` that is Markov for the Feller
kernel family `κ`: `μ[g (X t) | ℱ s] = ∫ g dκ_{t - s}(X s)` for `s ≤ t` and continuous `g`.
Then for every `ℱ`-stopping time `τ`, every `A ∈ ℱ_τ`, every `t ≥ 0` and every continuous `g`,
`∫_{A ∩ {τ < ∞}} g (X (τ + t)) dμ = ∫_{A ∩ {τ < ∞}} ∫ g dκ_t(X τ) dμ`.

## Sources

- Ethier & Kurtz (1986), ch. 4, Thm. 2.7; Revuz & Yor (1999), ch. III, §3.
