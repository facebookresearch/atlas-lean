# Thresholds for clearance, resistance takeover and coexistence of bacterial strains

**Model.** In dimensionless form, with $x, y$ the densities of susceptible and resistant bacteria relative to the carrying capacity,

$$\dot x = \beta_sx\,[1 - (x+y)] - (\alpha + \gamma)x - (1-h_1)qx - (1-h_2)xy,$$

$$\dot y = \beta_ry\,[1 - (x+y)] + (1-h_1)qx + (1-h_2)xy - \gamma y,$$

where $\beta_s \ge \beta_r$ are growth rates (resistance carries no fitness advantage), $\alpha$ the antibiotic killing rate of susceptible cells, $\gamma$ immune clearance, $q$ the mutation rate to resistance, the term $xy$ horizontal gene transfer, and $h_1, h_2\in[0,1]$ the efficacies of measures reducing mutation and transfer. The triangle $\Omega = \{x,y\ge0,\ x+y\le1\}$ is a trapping region. Define

$$R_r = \frac{\beta_r}{\gamma}, \quad R_s = \frac{\beta_s}{\alpha + \gamma + q(1-h_1)}, \quad h_s = \frac{1-h_2}{\alpha + \gamma + q(1-h_1)}, \quad h_{r1} = \frac{1-h_1}{\gamma}, \quad h_{r2} = \frac{1-h_2}{\gamma}.$$

**Theorem.**

1. (Equilibria.) The bacteria-free state $P_0 = (0,0)$ always exists; the resistant-only state $P_1 = \big(0, \frac{R_r-1}{R_r}\big)$ exists iff $R_r > 1$. A coexistence state $P^\ast = (x^\ast,y^\ast)$ requires $R_s > 1$; then $x^\ast = \frac{R_s - 1}{R_s} - \frac{R_s + h_s}{R_s}y^\ast$ and, for $0 < h_1, h_2 < 1$, $y^\ast$ is the unique positive root of $-a_2y^2 + a_1y + a_0 = 0$,

$$y^\ast = \frac{a_1 + \sqrt{a_1^2 + 4a_2a_0}}{2a_2}, \quad a_2 = h_{r2}(R_s + h_s) - h_sR_r, \quad a_1 = h_{r2}(R_s - 1) - h_{r1}q(R_s + h_s) + R_r - R_s, \quad a_0 = h_{r1}q(R_s - 1),$$

and $P^\ast\in\Omega$ exists if $R_s > 1$, $0 < h_1, h_2 < 1$ and $R_r(h_s + 1) < h_s + R_s$ (with analogous conditions when $h_1 = 1$ or $h_2 = 1$).
2. (Stability.) $P_0$ is locally asymptotically stable in $\Omega$ iff $R_s < 1$ and $R_r < 1$; $P_1$ is locally asymptotically stable if $R_r > 1$ and $R_r > \frac{R_s + h_s}{1 + h_s}$; $P^\ast$ is locally asymptotically stable if $R_s > 1$, $0 < h_1, h_2 < 1$ and $R_r < \frac{R_s + h_s}{1 + h_s}$.
3. (Optimal preventive control.) For the dimensional model in the sensitive and resistant populations $S, R$ (the system above before rescaling), started at a non-trivial equilibrium and with free end state, consider Problem (1) of the source: minimize

$$J[h] = \int_0^T\big[cR + (w_1 + w_2h_1)h_1 + (b_1 + b_2h_2)h_2\big]\,dt$$

   over measurable controls $h_1, h_2 : [0,T] \to [0,1]$. An optimal control exists and is characterized by Pontryagin's maximum principle with an explicit adjoint system.

So clearing an infection requires both strains to be subthreshold, while coexistence versus resistant takeover is decided by comparing $R_r$ with the weighted average $(R_s + h_s)/(1 + h_s)$.

## Expansion

At an equilibrium with $x > 0$ the first equation gives the line $R_s(1 - x - y) = 1 + h_sy$, and substituting into the second equation gives the quadratic for $y$; with $a_0 \ge 0$ and $a_2 > 0$ (from $\beta_s \ge \beta_r$ and $h_2 < 1$) it has exactly one positive root. Because mutation and transfer feed $y$ from $x$, no equilibrium has $x > 0 = y$. The Jacobian at $P_0$ is triangular with eigenvalues proportional to $R_s - 1$ and $R_r - 1$. At $P_1$ the $x$-direction eigenvalue is the invasion rate of susceptibles into the resistant-only state, proportional to $R_s(1 - y_1) - 1 - h_sy_1$ with $y_1 = 1 - 1/R_r$, which is negative exactly when $R_r > (R_s + h_s)/(1 + h_s)$; the same quantity changing sign creates $P^\ast$ by a transcritical exchange.

## Sources

- Alissen Peterson, Jhoana P. Romero-Leiton, Pablo Aguirre, Kamal R. Acharya, Bouchra Nasri, "Assessing the impact of mutations and horizontal gene transfer on the AMR control: a mathematical model", arXiv (2023). Section 3 (dimensionless model, Lemma 1, thresholds, Theorems 2–3), Section 4 (Theorem 4). <https://doi.org/10.48550/arXiv.2302.02280>. Published version: Computational and Applied Mathematics 44(2) (2025), article 82, <https://doi.org/10.1007/s40314-024-03043-4>; locators above refer to the arXiv version.
