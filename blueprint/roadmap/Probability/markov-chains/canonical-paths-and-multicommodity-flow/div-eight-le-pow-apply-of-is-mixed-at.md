# Sinclair's Lemma 7 from a single mixing time

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$ a probability vector with $\pi(x) > 0$ for every
$x$, and $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows summing to $1$) in
detailed balance with $\pi$: $\pi(x) P(x, y) = \pi(y) P(y, x)$ for all $x, y$. If $P$ is
[$1/4$-mixed](../mixing-times-of-markov-chains/is-mixed-at.md) with respect to $\pi$ at time
$\tau$, then for every $t \ge 2\tau$ and all $x, y \in S$,

$$P^t(x, y) \ge \frac{\pi(y)}{8} .$$

Sinclair's Lemma 7 gives the bound at $t = 2\tau$; [being $1/4$-mixed
persists](../mixing-times-of-markov-chains/is-mixed-at-mono.md), which gives the later times.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Lemma 7.
