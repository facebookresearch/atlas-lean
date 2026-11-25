# Time reversal of a stationary finite Markov chain, full support

Assume that equality on `ι` is decidable and that `ι` is finite. Assume `P ∈ rowStochastic ℝ ι` and `π ᵥ* P = π`.

If `π` is a stationary
probability vector of the row-stochastic matrix `P` and `π i > 0` for every state `i`, then the
reversed matrix `P* i j = π j * P j i / π i` is row-stochastic, and `P* = P` if and only if `π`
and `P` are in detailed balance: `π i * P i j = π j * P j i` for all `i j`.
