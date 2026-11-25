# Time reversal of a stationary finite Markov chain, general support

Assume that equality on `ι` is decidable. Assume `P ∈ rowStochastic ℝ ι`, `(∀ i, 0 ≤ π i) ∧ ∑ i, π i = 1`, `π ᵥ* P = π`, `∀ i j, π i ≠ 0 → Pstar i j = π j * P j i / π i` and `∀ i, π i = 0 → (∀ j, 0 ≤ Pstar i j) ∧ ∑ j, Pstar i j = 1`.

Let `P` be a
row-stochastic matrix on a finite state space `ι` and let `π` be a probability vector that is
stationary for `P` (`π ᵥ* P = π`). Let `Pstar` satisfy `Pstar i j = π j * P j i / π i` on every
row `i` in the support of `π`, and have arbitrary stochastic rows off the support. Then `Pstar` is
row-stochastic, the support of `π` is closed under `Pstar`, and `Pstar` agrees with `P` on every
row in the support of `π` (`P* = P` `π`-almost everywhere) if and only if `π` and `P` are in
detailed balance: `π i * P i j = π j * P j i` for all `i j`.
