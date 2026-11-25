# Detailed balance

Let $S$ be a finite set. A row vector $\pi : S \to \mathbb{R}$ is in detailed balance with a real
$S \times S$ matrix $Q$ if

$$\pi(i)\, Q(i, j) = \pi(j)\, Q(j, i) \qquad \text{for all } i, j \in S .$$

This is only the algebraic equation: it holds for $\pi = 0$ and every $Q$. For a probability vector
$\pi$ and a stochastic matrix (or a rate matrix) it is the reversibility of the chain started from
$\pi$.

## Sources

- J. R. Norris, *Markov Chains*, Cambridge Series in Statistical and Probabilistic Mathematics 2, Cambridge University Press, 1997, Section 3.7.
