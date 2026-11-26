# Lyapunov stability of saturated equilibria in virus–CTL networks

**Model.** Uninfected target cells $x$, viral variants $y_1, \dots, y_m$ and CTL (cytotoxic T lymphocyte) responses $Z_1, \dots, Z_n$, one per epitope, evolve (after rescaling) by the Lotka–Volterra-like system

$$
\dot x = 1 - x - x \sum_{i=1}^m \mathcal{R}_i y_i, \qquad \dot y_i = \gamma_i y_i \Big( \mathcal{R}_i x - 1 - \sum_{j=1}^n a_{ij} Z_j \Big), \qquad \dot Z_j = \frac{\sigma_j}{\rho_j} Z_j \Big( \sum_{i=1}^m a_{ij} y_i - \rho_j \Big),
$$

with $\mathcal{R}_i > 0$ the basic reproduction number of variant $i$, $a_{ij} \ge 0$ the killing rate of variant $i$ by response $j$ (zero if $i$ has escaped epitope $j$), and $\gamma_i, \sigma_j, \rho_j > 0$.

**Saturation.** For a nonnegative equilibrium $\mathcal{E}^* = (x^*, y^*, Z^*)$ let $\Omega_y, \Omega_z$ be its positive viral and immune components and $\Gamma_\Omega$ (its *positivity class*) the set of states with the same zero pattern. $\mathcal{E}^*$ is *saturated* if no missing population can invade:

$$
\mathcal{R}_i x^* - 1 - \sum_{j \in \Omega_z} a_{ij} Z_j^* \le 0 \ \ (i \notin \Omega_y), \qquad \sum_{i \in \Omega_y} a_{ij} y_i^* - \rho_j \le 0 \ \ (j \notin \Omega_z).
$$

Every stable equilibrium is saturated, since these quantities are eigenvalues of the Jacobian.

**Theorem.** If $\mathcal{E}^*$ is saturated, then it is locally stable and $x(t) \to x^*$ for every positive solution. If moreover $\mathcal{E}^*$ is the unique equilibrium in $\Gamma_\Omega$ and the saturation inequalities are strict, then $y_i(t) \to 0$ for $i \notin \Omega_y$ and $Z_j(t) \to 0$ for $j \notin \Omega_z$, the surviving $y_i, Z_j$ are uniformly persistent, and their time averages converge to $y_i^*, Z_j^*$. If in addition at most two persistent variants are still targeted by persistent responses ($|\{i \in \Omega_y : a_{ij} > 0 \text{ for some } j \in \Omega_z\}| \le 2$), $\mathcal{E}^*$ is globally asymptotically stable; global stability without this restriction is stated as a conjecture.

## Expansion

The Lyapunov function is the Volterra-type sum

$$
W = x - x^* \ln\frac{x}{x^*} + \sum_{i} \frac{1}{\gamma_i}\Big(y_i - y_i^* \ln\frac{y_i}{y_i^*}\Big) + \sum_j \frac{\rho_j}{\sigma_j}\Big(Z_j - Z_j^* \ln\frac{Z_j}{Z_j^*}\Big)
$$

(with the logarithmic terms dropped for zero components). The interaction terms cancel because virus–CTL interactions are antisymmetric after this weighting, leaving $\dot W = -(x - x^*)^2/x$ plus nonpositive saturation terms for the missing populations; LaSalle's invariance principle gives $x \to x^*$ and, under uniqueness and strict saturation, extinction of the missing variants and responses.

## Sources

- C. J. Browne, H. L. Smith, "Dynamics of Virus and Immune Response in Multi-Epitope Network", arXiv:1705.01188 (2017): Section 2 (model and rescaling), Section 3 (equilibria, positivity classes, saturation inequalities, Lyapunov function, Theorem 1 and the global-stability conjecture). <https://doi.org/10.48550/arXiv.1705.01188> Published version: Journal of Mathematical Biology 77 (2018) 1833–1870, <https://doi.org/10.1007/s00285-018-1224-z>.
