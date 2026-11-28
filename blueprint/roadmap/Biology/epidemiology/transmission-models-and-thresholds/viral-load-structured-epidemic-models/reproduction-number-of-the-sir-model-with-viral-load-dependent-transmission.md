# Reproduction number of the SIR model with viral load-dependent transmission

**Model.** Infectious individuals carry a viral load $v \in [0,1]$ and pass through a phase $I_1$ of increasing load and a phase $I_2$ of decreasing load. Writing $\rho_j$ for the density of compartment $j$ and $n_j$ for its viral-load momentum (density times mean viral load), and taking the transmission rate linear in the infector's viral load, the kinetic description closes exactly into

$$\begin{aligned}
\dot\rho_S &= b - \beta\rho_S(n_{I_1} + n_{I_2}) - \mu\rho_S,\\
\dot\rho_{I_1} &= \beta\rho_S(n_{I_1} + n_{I_2}) - \lambda\gamma\nu_1\rho_{I_1} - \mu\rho_{I_1},\\
\dot\rho_{I_2} &= \lambda\gamma\nu_1\rho_{I_1} - \lambda\gamma\nu_2\rho_{I_2} - \mu\rho_{I_2},\\
\dot n_{I_1} &= \beta v_0\rho_S(n_{I_1} + n_{I_2}) + \lambda\gamma\nu_1(1-\nu_1)\rho_{I_1} - \lambda\gamma\nu_1(2-\nu_1)n_{I_1} - \mu n_{I_1},\\
\dot n_{I_2} &= \lambda\gamma\nu_1^2\rho_{I_1} + \lambda\gamma\nu_1(1-\nu_1)n_{I_1} - \lambda\gamma\nu_2(2-\nu_2)n_{I_2} - \mu n_{I_2},
\end{aligned}$$

with birth and death rate $b, \mu > 0$, transmission coefficient $\beta > 0$, viral load $v_0$ of newly infected individuals, rate $\lambda\gamma > 0$ of viral-load updates and $\nu_1, \nu_2 \in (0,1)$ shaping the within-host viral-load kinetics. The region $\{0 < \rho_S + \rho_{I_1} + \rho_{I_2} \le b/\mu,\ n_{I_j} \le \rho_{I_j}\}$ is positively invariant, and the disease-free equilibrium is $(b/\mu, 0, 0, 0, 0)$.

**Theorem 1.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$, where, with $a = \lambda\gamma$,

$$\mathcal R_0 = \frac{\beta b}{\mu}\cdot\frac{a\nu_1\big(a\nu_1(1-\nu_2)^2 + a\nu_2(2-\nu_2) + \mu\big) + v_0(a\nu_1 + \mu)\big(a\nu_1(1-\nu_1) + a\nu_2(2-\nu_2) + \mu\big)}{(a\nu_1 + \mu)\big(a\nu_1(2-\nu_1) + \mu\big)\big(a\nu_2(2-\nu_2) + \mu\big)}.$$

**Theorem 2.** If $\mathcal R_0 < 1$ there is no endemic equilibrium; if $\mathcal R_0 > 1$ there is a unique one, with $\rho_S^E = \frac{b}{\mu}\frac{1}{\mathcal R_0}$ and $\rho_{I_1}^E = \frac{b}{a\nu_1 + \mu}\big(1 - \frac{1}{\mathcal R_0}\big)$.

**Theorem 3.** The system undergoes a forward (transcritical) bifurcation at $\mathcal R_0 = 1$: the center-manifold coefficients satisfy $A < 0 < B$, so a locally stable endemic equilibrium emerges for $\mathcal R_0$ slightly above $1$.

## Expansion

At the disease-free state the Jacobian has eigenvalues $-\mu$ and $-a\nu_2 - \mu$, and the rest come from a $3 \times 3$ block in $(\rho_{I_1}, n_{I_1}, n_{I_2})$. Its characteristic polynomial $l^3 + a_1 l^2 + a_2 l + a_3$ has $\operatorname{sgn} a_3 = \operatorname{sgn}(1 - \mathcal R_0)$, and $\mathcal R_0 < 1$ also gives $a_1 > 0$ and $a_1 a_2 > a_3$, so the Routh–Hurwitz conditions decide stability; solving $\det = 0$ for $\beta$ gives the critical $\bar\beta$ and hence $\mathcal R_0$. Unlike the constant-rate model, $\mathcal R_0$ depends on the initial viral load $v_0$, a parameter absent from the density equations: transmission is weighted by viral load accumulated along the infectious period. Dropping transmission from $I_1$ (a latent phase) or from $I_2$ (isolated, treated cases) gives the corresponding reduced reproduction numbers.

## Sources

- R. Della Marca, N. Loy, A. Tosin, "An SIR model with viral load-dependent transmission", Journal of Mathematical Biology 86(4) (2023) 61, model (11), Equations (13)-(20), Theorems 1-3 and Remark 3.1, <https://doi.org/10.1007/s00285-023-01901-z>, PMCID PMC10042434.
