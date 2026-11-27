# Detailed balance propagates to the transition function

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$ and $Q$ a real $S \times S$ matrix in [detailed
balance](is-detailed-balance.md) with $\pi$. Then for every real $t$, the [transition
function](../the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md) $P(t) = e^{tQ}$ is in
detailed balance with $\pi$:

$$\pi(i)\, P(t)(i, j) = \pi(j)\, P(t)(j, i) \qquad \text{for all } i, j \in S .$$

For a probability vector $\pi$ and a rate matrix $Q$ this is the reversibility of the chain started
from $\pi$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 3.7.
