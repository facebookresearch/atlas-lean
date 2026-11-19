# Otter–Dwass formula

Let $\nu$ be a finite measure on $\mathbb{N}$ and $k, n \in \mathbb{N}$, and let
$\nu^{\otimes n}$ be the product measure on $\mathbb{N}^n$. Then, in $[0, \infty]$,

$$n \cdot \nu^{\otimes n}\{x : x_0 + \dots + x_{n-1} + k = n,\ x \text{ a first-passage sequence}\} = k \cdot \nu^{\otimes n}\{x : x_0 + \dots + x_{n-1} + k = n\},$$

with [first-passage sequences](is-first-passage.md). When $\nu$ is a probability
measure, the offspring law of a Galton–Watson process with $k$ ancestors, this reads
$n \, P(T = n) = k \, P(\xi_1 + \dots + \xi_n = n - k)$ for the total progeny $T$ and i.i.d.
offspring numbers $\xi_i$ with law $\nu$.

## Sources

- R. Otter, *The multiplicative process*, Annals of Mathematical Statistics 20 (1949), 206–224.
- M. Dwass, *The total progeny in a branching process and a related random walk*, Journal of
  Applied Probability 6 (1969), 682–686.
