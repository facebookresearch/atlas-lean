# Flexible Hamming distance

Let $n \le m$ be natural numbers, $\sigma$ a permutation of
$\{0, \dots, n-1\}$ and $\tau$ a permutation of $\{0, \dots, m-1\}$. The flexible Hamming distance
of $\sigma$ and $\tau$ is the real number

$$
d^{\mathrm{flex}}_n(\sigma, \tau) = \frac{\#\{i < n : \sigma(i) \ne \tau(i)\} + (m - n)}{n}.
$$

For $n = 0$ this quotient is taken to be $0$; this single value does not affect statements about
limits as $n \to \infty$.

## Sources

- Kourovka Notebook 21.84. The source is internally inconsistent about the argument order: it first defines the distance with the small permutation first, `d_n^flex(σ, τ)` for `σ ∈ S_n`, `τ ∈ S_m`, but later writes the convergence expression with `ρ_n(g)` first. This formalization follows the definition site (small first), which is also the type-correct order for the embedding `Fin n → Fin m`.
