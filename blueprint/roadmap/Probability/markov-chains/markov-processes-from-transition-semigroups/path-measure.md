# Path-space measure of a Markov semigroup

Let $E$ be a Polish space with its Borel $\sigma$-algebra, $(K_t)_{t \ge 0}$ Markov kernels on $E$
satisfying the Chapman–Kolmogorov equations, and $x \in E$. The path measure $P_x$ is a measure on
$E^{[0, \infty)}$, chosen by the Kolmogorov extension theorem ([existence](exists-projective-limit.md)),
whose image under the projection to the coordinates in each finite set $J$ is the [Markov law at the
times $J$](finite-law.md) started from $x$.

No condition $K_0 = \mathrm{id}$ is imposed: the marginal of $P_x$ at time $0$ is $K_0(x, \cdot)$,
which is $\delta_x$ only when $K_0$ is the identity kernel.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986,
  Chapter 4, Section 4.1.
