# Mixing of a lazy reversible chain from its spectral gap

Let $S$ be a finite set, $\pi$ a probability vector on $S$ with $\pi(x) > 0$ for every $x$, and $K$
a stochastic $S \times S$ matrix (nonnegative entries, rows summing to $1$) in detailed balance with
$\pi$: $\pi(x) K(x, y) = \pi(y) K(y, x)$. Let $P = \frac{1}{2}(I + K)$ be its lazy version and let
$\gamma$ be a real number with $0 < \gamma \le 1$ and $\gamma \le \lambda(P, \pi)$, the [spectral
gap](spectral-gap.md) of $P$. If $t \in \mathbb{N}$ satisfies

$$(1 - \gamma)^t \Bigl(\frac{1}{\pi(x)} - 1\Bigr) \le \frac{1}{4} \qquad \text{for every } x \in S,$$

then $P$ is [$1/4$-mixed](../mixing-times-of-markov-chains/is-mixed-at.md) with respect to $\pi$ at
time $t$. This is Sinclair's mixing bound with its Poincaré hypothesis read off the spectral gap
through [the equivalence of the two](inv-le-spectral-gap-iff-poincare.md), for $B = 1/\gamma$.

## Background

- [A Poincaré inequality bounds the mixing time of the lazy chain](../mixing-times-of-markov-chains/is-mixed-at-of-poincare.md): Sinclair's statement,
  of which this is a restatement through the spectral gap.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370, Proposition 1(i).
