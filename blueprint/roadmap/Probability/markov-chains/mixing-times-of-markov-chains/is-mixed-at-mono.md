# Being $1/4$-mixed persists

Let $S$ be a finite set, $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows summing
to $1$) and $\pi : S \to \mathbb{R}$ a vector with $\pi P = \pi$. If $P$ is [$1/4$-mixed](is-mixed-at.md)
with respect to $\pi$ at time $t$, then it is $1/4$-mixed with respect to $\pi$ at every time
$t' \ge t$.

This holds because $t \mapsto d_{TV}(P^t(x, \cdot), \pi)$ is nonincreasing for every start $x$.
Consequently the least time at which $P$ is $1/4$-mixed agrees with Sinclair's mixing time
$\tau_x(\varepsilon) = \min\{t : \Delta_x(t') \le \varepsilon \text{ for all } t' \ge t\}$ at
$\varepsilon = 1/4$, maximised over the start $x$.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Section 2.
