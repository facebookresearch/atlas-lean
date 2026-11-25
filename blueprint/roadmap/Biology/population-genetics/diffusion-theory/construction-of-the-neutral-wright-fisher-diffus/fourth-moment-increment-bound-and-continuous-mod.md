# Fourth-moment increment bound and continuous modification for the mutation diffusion

Let $\theta_1, \theta_2 \ge 0$ and let $(P^\theta_t)_{t \ge 0}$ be the transition semigroup of the two-allele Wright–Fisher diffusion with mutation on $[0, 1]$, with generator

$$L_\theta f(y) = \tfrac12 y(1 - y) f''(y) + \tfrac12\bigl(\theta_1(1 - y) - \theta_2 y\bigr) f'(y)$$

on polynomials. For each $x \in [0, 1]$ write $P^\theta_t g(x) = \int g(y)\, P^\theta_t(x, dy)$. Then there is a constant $C_\theta$, depending only on $\theta_1$ and $\theta_2$ and computed from $L_\theta$ applied to the polynomials $y \mapsto (y - x)^4$ and $y \mapsto (y - x)^2$, such that

$$P^\theta_t\bigl((\cdot - x)^4\bigr)(x) \le C_\theta\, t^2 \qquad \text{for all } x \in [0, 1],\ t \in [0, 1].$$

Consequently the coordinate process under the [canonical path measure of the mutation diffusion](mutation-wf-transition-kernel-and-canonical-path.md) started at $x$ satisfies Kolmogorov's continuity condition $\mathbb E_x |X_t - X_s|^4 \le C'_\theta |t - s|^2$ for all $s, t \ge 0$, with $C'_\theta = \max(C_\theta, 1)$, and has a continuous $[0, 1]$-valued modification with $X_0 = x$.

## Depends on

- [Mutation WF transition kernel and canonical path measure](mutation-wf-transition-kernel-and-canonical-path.md)

## Proof depends on

- [Mutation WF Feller semigroup via polynomial duality and chain limits](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md)
- [Kolmogorov continuity condition for the raw Wright–Fisher process](is-kolmogorov-process-raw-process.md), the neutral case

## Expansion

A full proof page must still establish:

- the polynomial computation of $L_\theta (y - x)^4$ and $L_\theta (y - x)^2$ and the Gronwall argument on the polynomial semigroup, with $C_\theta$ explicit in $\theta_1$ and $\theta_2$;
- the passage from the one-step bound to the two-time bound by the Markov property, and Kolmogorov's continuity theorem.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, <https://doi.org/10.1002/9780470316658>
