# Is Selection Markov

`X` is a **Wright–Fisher diffusion with scaled selection coefficient `sel` (`σ = 2Ns`),
Markov for the kernel family `κ`**: it solves the martingale problem
`IsWrightFisherSolution sel` for the generator `L_σ f = x (1 - x) / 2 · f'' + σ x (1 - x) · f'`,
and for `s ≤ t` and every continuous `g`, `μ[g (X t) | ℱ s] = ∫ g dκ_{t - s}(X s)` almost surely.
