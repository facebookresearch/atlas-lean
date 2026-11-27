# Extinction probability of a Galton–Watson process

For a measure $\nu$ on $\mathbb{N}$ let $\mathcal{L}_n$ be the [law of the $n$-th generation
size](law.md) of the Galton–Watson process with offspring law $\nu$, a measure on $\mathbb{N}$, and
let $r_n \in [0, \infty)$ be the mass $\mathcal{L}_n(\{0\})$ as a real number, a mass $\infty$ counting
as $0$. The extinction probability is the supremum in $\mathbb{R}$

$$q = \sup_{n \in \mathbb{N}} r_n ,$$

taken to be $0$ if the $r_n$ are unbounded. For an offspring law $\nu$ (a probability measure)
$r_n = P(Z_n = 0) \in [0, 1]$, and these probabilities increase to $q$
([convergence](tendsto-law-real-zero.md)). On a probability space carrying the process the
events $\{Z_n = 0\}$ increase with $n$, since $0$ is absorbing, so $q$ is the probability of
eventual extinction.
