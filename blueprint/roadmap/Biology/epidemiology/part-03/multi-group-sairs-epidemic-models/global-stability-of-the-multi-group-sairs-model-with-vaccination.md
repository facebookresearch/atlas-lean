# Global stability of the multi-group SAIRS model with vaccination

**Model.** A population is split into $n$ communities. In community $i$, $S_i, A_i, I_i, R_i$ are the fractions susceptible, asymptomatic infectious, symptomatic infectious and recovered, with $S_i + A_i + I_i + R_i = 1$. Eliminating $R_i$:

$$\begin{aligned} \dot S_i &= \mu_i - \sum_{j=1}^n\bigl(\beta^A_{ij}A_j + \beta^I_{ij}I_j\bigr)S_i - (\mu_i + \nu_i + \gamma)S_i + \gamma(1 - A_i - I_i),\\ \dot A_i &= \sum_{j=1}^n\bigl(\beta^A_{ij}A_j + \beta^I_{ij}I_j\bigr)S_i - (\alpha + \delta_A + \mu_i)A_i,\\ \dot I_i &= \alpha A_i - (\delta_I + \mu_i)I_i, \end{aligned}$$

where $\mu_i$ is the birth and death rate, $\nu_i$ the vaccination rate, $\gamma$ the rate of loss of immunity, $\alpha$ the rate at which asymptomatic cases develop symptoms, and $\delta_A, \delta_I$ the recovery rates. The contact matrices $[\beta^A_{ij}]$ and $[\beta^I_{ij}]$ are irreducible with positive diagonals. The region $\Gamma = \{S_i + A_i + I_i \le 1\}$ is positively invariant. The basic reproduction number is the spectral radius

$$\mathcal R_0 = \rho\!\left(\Bigl[\Bigl(\beta^A_{ij} + \frac{\alpha\,\beta^I_{ij}}{\delta_I + \mu_i}\Bigr)\frac{\gamma + \mu_i}{(\gamma + \mu_i + \nu_i)(\alpha + \delta_A + \mu_i)}\Bigr]_{i,j=1}^n\right).$$

**Theorem.**

1. (Disease elimination.) The disease-free equilibrium is globally asymptotically stable in $\Gamma$ if $\mathcal R_0 < 1$, and unstable if $\mathcal R_0 > 1$. Without vaccination ($\nu_i = 0$) it is also globally asymptotically stable when $\mathcal R_0 = 1$.
2. (Endemic equilibrium.) There is a unique endemic equilibrium in the interior of $\Gamma$ if and only if $\mathcal R_0 > 1$, and the system is then uniformly persistent.
3. (SAIR: permanent immunity, $\gamma = 0$.) If $\mathcal R_0 > 1$, the endemic equilibrium is globally asymptotically stable in the interior of $\Gamma$, with no further parameter conditions.
4. (SAIRS with equal recovery rates, $\delta_A = \delta_I = \delta$.) If $\mathcal R_0 > 1$, $\delta > \nu_i$ and $(\mu_i + \nu_i)S_i^* \ge \gamma R_i^*$ for every $i$, the endemic equilibrium is globally asymptotically stable in the interior of $\Gamma$.

## Expansion

$\mathcal R_0$ comes from the next-generation matrix $FV^{-1}$, where $F$ collects new infections into the $A$ classes and $V$ the transitions $A \to I \to$ removal. Global stability of the disease-free equilibrium follows from the comparison $\dot{(A,I)} \le (F - V)(A,I)$ and the M-matrix criterion $\rho(FV^{-1}) < 1 \iff s(F - V) < 0$. Existence and uniqueness of the endemic equilibrium come from rewriting the equilibrium equations as a fixed point $x = \Phi(x)$ of a monotone, strictly sublinear map with irreducible Jacobian at $0$. Hethcote–Thieme's theorem then gives a unique positive fixed point exactly when $\rho(J_\Phi(0)) > 1$. For item 3, Volterra-type terms $S - S^* - S^*\ln(S/S^*)$ in each group are combined, with weights from Kirchhoff's matrix-tree theorem on the infection graph (the graph-theoretic method of Shuai and van den Driessche), into a global Lyapunov function, and LaSalle's principle concludes.

## Sources

- Stefania Ottaviano, Mattia Sensi, Sara Sottile, "Global stability of multi-group SAIRS epidemic models", arXiv (2022). Section 2 (model, assumptions, Theorem 1), Section 3 (formula for $\mathcal R_0$, Theorems 4–6), Section 4 (Theorems 8–9), Section 5 (Theorems 13–15). <https://doi.org/10.48550/arXiv.2202.02993>. Published version: Mathematical Methods in the Applied Sciences 46(13) (2023), 14045–14071, <https://doi.org/10.1002/mma.9303>; locators above refer to the arXiv version.
