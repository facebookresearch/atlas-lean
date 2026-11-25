# Doeblin's argument

Let $S$ be a finite set, $P$ a stochastic $S \times S$ matrix (nonnegative entries, rows summing
to $1$) and $\pi$ a stationary distribution: $\pi \ge 0$, $\sum_y \pi(y) = 1$ and $\pi P = \pi$.
Let $r \in \mathbb{N}$ and $\delta \in \mathbb{R}$ satisfy the minorisation
$\delta\, \pi(y) \le P^r(x, y)$ for all $x, y \in S$. Then for every $n \in \mathbb{N}$ and every
start $x$,

$$d_{TV}\bigl(P^n(x, \cdot), \pi\bigr) \le (1 - \delta)^{\lfloor n / r \rfloor},$$

where $d_{TV}$ is the [total variation distance](../mixing-times-of-markov-chains/tv-dist.md) and
$\lfloor n / 0 \rfloor = 0$. The bound is informative when $r > 0$ and $\delta > 0$; for $r = 0$
or $\delta \le 0$ it reads $d_{TV} \le 1$ or something weaker.

## Sources

- D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and Mixing Times*, 2nd ed., American
  Mathematical Society, 2017, proof of Theorem 4.9.
- W. Doeblin, *Exposé de la théorie des chaînes simples constantes de Markov à un nombre fini
  d'états*, Revue Mathématique de l'Union Interbalkanique 2 (1938), 77–105.
