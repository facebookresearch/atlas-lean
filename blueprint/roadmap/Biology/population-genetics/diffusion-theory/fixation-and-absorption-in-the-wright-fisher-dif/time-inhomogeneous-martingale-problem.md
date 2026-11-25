# Time-inhomogeneous martingale problem

Let $E$ be a compact metric space, $\mathcal D \subseteq C(E)$ a common domain, and $(A_t)_{t \ge 0}$ a family of linear operators $A_t : \mathcal D \to B(E)$ such that, for each $f \in \mathcal D$, $(t, x) \mapsto A_t f(x)$ is jointly measurable and bounded on $[0, T] \times E$ for every $T$. An $E$-valued, progressively measurable process $X$ on a filtered probability space $(\Omega, \mathcal F, (\mathcal F_t), \mathbb P)$ *solves the time-inhomogeneous martingale problem* for $(A_t)$ if, for every $f \in \mathcal D$,

$$f(X_t) - f(X_0) - \int_0^t (A_s f)(X_s)\, ds$$

is an $(\mathcal F_t)$-martingale. When $A_t = A$ for all $t$, this is the [martingale problem](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $A$.

## Depends on

- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)

## Expansion

A full page must still check that the constant family $A_t = A$ recovers the generic definition exactly, including its measurability conventions.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (martingale problems; time-dependent generators via the space-time process), <https://doi.org/10.1002/9780470316658>
