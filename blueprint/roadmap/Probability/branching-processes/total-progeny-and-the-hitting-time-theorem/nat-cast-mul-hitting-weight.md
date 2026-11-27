# Hitting-time theorem

Let $R$ be a commutative semiring, $p : \mathbb{N} \to R$ and $k, n \in \mathbb{N}$. Then the
[hitting weight](hitting-weight.md) and the [walk weight](walk-weight.md) satisfy

$$n \cdot H_p(k, n) = k \cdot W_p(k, n) .$$

For probability weights $p(j) = P(\xi = j)$ this is the hitting-time theorem: the walk with
i.i.d. steps $\xi_i - 1$ started at $k$ first hits $0$ at time $n$ with probability
$\tfrac{k}{n} P(\xi_1 + \dots + \xi_n = n - k)$ for $n \ge 1$. The proof double counts cyclic
shifts with the [cycle lemma](card-filter-is-first-passage-rotate.md).

## Sources

- R. van der Hofstad and M. Keane, *An elementary proof of the hitting time theorem*, American
  Mathematical Monthly 115 (2008), 753–756.
