# Kurtz's pathwise estimate

Let `(S, I, R)` be a chain path of population size `N ≥ 1`
and `(s, i, r)` a solution of the SIR system `s' = -β s i`, `i' = β s i - γ i`, `r' = γ i`
started in the simplex. If on the clock ranges `[0, β T]` and `[0, γ T]` the scaled driving
counts stay within `η` of the identity, `|y(N a) / N - a| ≤ η`, then on `[0, T]`

`|S/N - s| + |I/N - i| + |R/N - r| ≤ (initial distance + 4 η) e^{2 (β + γ) t}`.

Proof: subtracting the integral form of the ODE from the time-change equations leaves the
initial error, the clock errors (at most `η` each), and the integral of the drift difference,
which is `2 (β + γ)`-Lipschitz in `ℓ¹` on the simplex; Gronwall's inequality closes it.
