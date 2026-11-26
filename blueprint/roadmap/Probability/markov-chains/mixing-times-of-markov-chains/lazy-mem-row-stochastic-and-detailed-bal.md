# The lazy version of a reversible stochastic matrix is reversible and stochastic

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$, and $K$ a stochastic $S \times S$ matrix
(nonnegative entries, rows summing to $1$) in detailed balance with $\pi$:
$\pi(x) K(x, y) = \pi(y) K(y, x)$ for all $x, y$. Then the lazy matrix $\frac{1}{2}(I + K)$ is
stochastic and is in detailed balance with $\pi$.

## Sources

- A. Sinclair and M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov
  chains*, Information and Computation 82 (1989), 93–133, Proposition 3.2.
