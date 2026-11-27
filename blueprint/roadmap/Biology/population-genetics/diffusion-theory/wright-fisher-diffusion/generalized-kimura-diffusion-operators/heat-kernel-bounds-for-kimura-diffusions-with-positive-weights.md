# Heat-kernel bounds for Kimura diffusions with positive weights

Let $L$ be a generalized Kimura diffusion operator with smooth coefficients on a compact manifold with corners $P$, with weighted measure $\mu_L$ and intrinsic metric $\rho_i$ as in the [Harnack inequality](parabolic-harnack-inequality-for-generalized-kimura-diffusions.md), and suppose the weights of $L$ are positive along every boundary component.

**Theorem (Epstein–Mazzeo, Theorem 5.1).** If $u$ is a weak solution of $(\partial_t - L)u = 0$ with $u(\cdot,0) = f \in L^2(P; d\mu_L)$, then $u \in C^\infty(P \times (0,\infty))$.

**Theorem (Gaussian upper bound; Epstein–Mazzeo, Theorem 5.2).** Write the kernel of $e^{tL}$ as $p_t(\xi,\eta)\, d\mu_L(\eta)$. There are positive constants $C_0, C_1, C_2$ such that for all $t > 0$ and $\xi,\eta \in P$

$$p_t(\xi,\eta) \le \frac{C_0 \exp\big(-\rho_i^2(\xi,\eta)/(C_2 t)\big)}{\sqrt{\mu_L(B^i_{\sqrt t}(\xi))\, \mu_L(B^i_{\sqrt t}(\eta))}} \left(1 + \frac{\rho_i(\xi,\eta)}{\sqrt t}\right)^{D} e^{C_1 t},$$

where $D$ is the doubling exponent of $\mu_L$. For each $\eta$, $(\xi,t) \mapsto p_t(\xi,\eta)$ is smooth on $P \times (0,\infty)$.

When the weights are constant along the boundary and $L$ is defined by a globally defined Dirichlet form, the kernel $p_t(\xi,\eta)$ is smooth on $P \times P \times (0,\infty)$ (Corollary 5.2 of the paper); with variable weights it is smooth in $\xi$ but singular as $\eta$ approaches the boundary. The bound is anisotropic: near a boundary face the volume $\mu_L(B^i_{\sqrt t})$ decays like a power of $t$ fixed by the weights at that face, so mutation rates directly control the short-time size of the heat kernel.

## Depends on

- [Parabolic Harnack inequality for generalized Kimura diffusions](parabolic-harnack-inequality-for-generalized-kimura-diffusions.md)

## Expansion

In local adapted coordinates $L$ is the operator of a possibly non-symmetric Dirichlet form with respect to $\mu_L$, plus lower-order terms. The local Harnack inequality gives Hölder continuity of weak solutions at positive times, and the existing regularity theory for Kimura operators on anisotropic Hölder spaces then upgrades this to smoothness. Volume doubling and the Poincaré inequality give, by the Grigor'yan–Saloff-Coste equivalence, Gaussian bounds for the local heat kernels of $L_Q$; a partition of unity patches local estimates, and the factor $e^{C_1 t}$ absorbs the non-symmetric and lower-order parts.

## Sources

- C. L. Epstein and R. Mazzeo, *Harnack inequalities and heat-kernel estimates for degenerate diffusion operators arising in population biology*, *Applied Mathematics Research eXpress* 2016(2) (2016), 217–280, <https://doi.org/10.1093/amrx/abw002>; preprint arXiv:1406.1426, <https://doi.org/10.48550/arXiv.1406.1426>.
