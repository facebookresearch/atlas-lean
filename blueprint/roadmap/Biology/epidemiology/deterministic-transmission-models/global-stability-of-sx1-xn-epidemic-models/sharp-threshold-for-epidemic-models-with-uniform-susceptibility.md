# Sharp global threshold for epidemic models with uniform susceptibility

**Model.** One susceptible class $S$ and $n$ non-susceptible classes $\mathbf{x} = (x_1,\dots,x_n)^\top$ (latent, infectious, hospitalized, recovered, ...), with arbitrary flows among the $x_j$ but none back to $S$:

$$\dot S = \Pi - \mu_S S - \lambda S, \qquad \dot{\mathbf{x}} = \lambda S\,\mathbf{p} - M\mathbf{x}, \qquad \lambda = \boldsymbol{\beta}^\top\mathbf{x}.$$

Here $\Pi > 0$ is natality into $S$, $\mu_S, \mu_j > 0$ are mortalities, $\boldsymbol\beta \ge 0$ with some $\beta_j > 0$ are transmission rates, $\mathbf{p} \ge 0$ with $\sum_j p_j = 1$ distributes new infections, and the post-infection transfer matrix has $M_{ij} = -m_{ij} \le 0$ ($i \ne j$) and $M_{jj} = \mu_j + \sum_i m_{ij}$, so each column sum is $\mu_j > 0$ and $M$ is a non-singular M-matrix with $M^{-1} \ge 0$. No compartment is isolated from $S$: in the transfer digraph with an edge $S \to x_j$ whenever $p_j > 0$ and an edge $x_j \to x_i$ whenever $m_{ij} > 0$, every $x_j$ is reachable by a path from $S$. This is weaker than irreducibility of $M$, which is *not* assumed. All susceptibles are equally susceptible (uniform susceptibility).

**Reproduction number.**

$$\mathcal{R}_0 = \frac{\Pi}{\mu_S}\,\boldsymbol\beta^\top M^{-1}\mathbf{p} > 0 .$$

**Theorem.** If $\mathcal{R}_0 \le 1$, the disease-free equilibrium $(\Pi/\mu_S, \mathbf{0})$ is globally asymptotically stable. If $\mathcal{R}_0 > 1$, there is a unique endemic equilibrium, and it is globally asymptotically stable (excluding initial states, such as the disease-free set, from which transmission can never occur).

## Depends on

- [Solutions of the Kermack-McKendrick SIR model](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

$\boldsymbol\beta^\top M^{-1}\mathbf{p}$ is the expected total infectiousness of one newly infected individual, since $M^{-1}_{ij}$ is the expected time spent in $x_i$ starting from $x_j$; multiplying by the disease-free susceptible density gives $\mathcal{R}_0$. For $\mathcal{R}_0 \le 1$ a linear Lyapunov function $\mathbf{w}^\top\mathbf{x}$ with $\mathbf{w}^\top = \boldsymbol\beta^\top M^{-1}$ decreases. For $\mathcal{R}_0 > 1$ a Volterra-type function $S - S^*\ln S + \sum_j c_j(x_j - x_j^*\ln x_j)$, with weights determined from the endemic flow balance over the transfer graph, has non-positive derivative, and LaSalle's principle finishes. The result covers SIR, SEIR, staged-progression, parallel-stage and arbitrary-duration models in one stroke; the limitation is uniform susceptibility, i.e. no reinfection classes.

## Sources

- D. J. D. Earn, C. C. McCluskey, "Global stability of epidemic models with uniform susceptibility", *Proceedings of the National Academy of Sciences* 122(49) (2025), e2510156122, model (eq:ODE)-(eq:PITmatrix), Eq. (eq:Rzero), Theorems 1-2, <https://doi.org/10.1073/pnas.2510156122> (preprint arXiv:2512.11003).
