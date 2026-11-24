# The chaining argument along a finite chain

Let $T$ be a finite metric space, $(X_t)$ a process of measurable random variables on a probability space with
the [sub-Gaussian increment condition](satisfies-increment-condition.md), $M \ge 1$, and
$\pi_0, \dots, \pi_M : T \to T$ approximation maps with $\pi_0 \equiv t_0$, $\pi_M = \mathrm{id}$
and, for $1 \le n \le M$, at most $2^{2^{n+1}}$ distinct pairs $(\pi_n(t), \pi_{n-1}(t))$, as when
$\operatorname{card}\pi_n(T) \le N_n$. Then

$$\mathbb{E}\sup_{t}(X_t - X_{t_0}) \le 7 \sup_t \sum_{n=1}^{M} 2^{n/2} d(\pi_n(t), \pi_{n-1}(t))$$

(Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2nd ed., 2021, Section 2.4, the
argument proving (2.34)). The expectation is that of the nonnegative variable $\sup_t (X_t - X_{t_0})$, taken in
$[0, \infty]$.

Write $X_t - X_{t_0}$ as the telescoping sum of the increments along the chain. Normalised by
$2^{n/2} d(\pi_n(t), \pi_{n-1}(t))$, the increments at level $n$ take at most $2^{2^{n+1}}$
values, so the union bound gives $\mathbb{P}(Z \ge v) \le
\sum_n 2^{2^{n+1}} \cdot 2 e^{-v^2 2^{n}/2}$ for their maximum $Z$ over all levels. At $v = 3 + j$
this is at most $2 \cdot 2^{-j}$, so $\mathbb{E}Z \le 3 + 4$, and
$\sup_t (X_t - X_{t_0})$ is at most $Z$ times the right-hand side sum.
