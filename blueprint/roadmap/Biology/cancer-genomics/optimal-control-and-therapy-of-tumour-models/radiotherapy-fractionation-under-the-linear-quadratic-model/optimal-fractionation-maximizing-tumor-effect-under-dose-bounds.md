# Optimal radiotherapy fractionation with dose bounds: maximizing tumor effect

Under the linear-quadratic model, delivering $N$ fractions of doses $d = (d_1, \dots, d_N)$ produces the tumor effect and the organ-at-risk (OAR) effect

$$ E_T(N,d) = \alpha_T \sum_{i=1}^N d_i + \beta_T \sum_{i=1}^N d_i^2, \qquad E_{OAR}(N,d) = \alpha_0 \delta \sum_{i=1}^N d_i + \beta_0 \delta^2 \sum_{i=1}^N d_i^2, $$

where $\alpha_T, \beta_T > 0$ and $\alpha_0, \beta_0 > 0$ are the radiosensitivities of tumor and OAR and $\delta \in (0,1]$ is the fraction of the dose reaching the OAR (the surviving fraction of cells is $e^{-E}$). The healing problem $(P_1)$ is to maximize $E_T(N,d)$ over $N \in \mathbb N$ and $d \in \mathbb R^N$ subject to $E_{OAR}(N,d) \le \gamma_{OAR}$ and $d_{\min} \le d_i \le d_{\max}$, with $0 < d_{\min} < d_{\max}$. Write $\varphi_0(r) = \alpha_0 \delta r + \beta_0 \delta^2 r^2$,

$$ \lambda_0 = \max\left\{1, \frac{\gamma_{OAR}}{\varphi_0(d_{\max})}\right\}, \qquad \rho_0 = \frac{\gamma_{OAR}}{\varphi_0(d_{\min})}, \qquad \omega_\delta = \frac{\alpha_T}{\beta_T} - \frac{\alpha_0}{\beta_0 \delta}, $$

and, for $N$ fractions, $\bar d_0(N)$ for the equal dose that exhausts the OAR budget, $N \varphi_0(\bar d_0) = \gamma_{OAR}$:

$$ \bar d_0(N) = \frac{-\alpha_0 N + \sqrt{(\alpha_0 N)^2 + 4 \beta_0 N \gamma_{OAR}}}{2 \beta_0 \delta N}. $$

Assume $\rho_0 \ge 2$ (so $(P_1)$ has a solution and at least two fractions are feasible).

- If $\lfloor\lambda_0\rfloor = \lfloor\rho_0\rfloor$, the unique solution is $N = \lfloor\lambda_0\rfloor$ fractions, all at $d_{\max}$.
- If $\lfloor\lambda_0\rfloor < \lfloor\rho_0\rfloor$ and $\omega_\delta > 0$ (tumor $\alpha/\beta$ larger than the effective OAR ratio, the common clinical case), the unique solution is **hyperfractionation**: $N = \lfloor\rho_0\rfloor$ equal fractions of dose $\bar d_0(\lfloor\rho_0\rfloor)$.
- If $\lfloor\lambda_0\rfloor < \lfloor\rho_0\rfloor$ and $\omega_\delta < 0$, a solution is **hypofractionation**: either $N = \lfloor\lambda_0\rfloor$ fractions at $d_{\max}$, or $N = \lceil\lambda_0\rceil$ fractions of which $K$ are at $d_{\min}$, at most one is at an intermediate dose $d^*$ and the rest are at $d_{\max}$, where $K = \lfloor (N\varphi_0(d_{\max}) - \gamma_{OAR}) / (\varphi_0(d_{\max}) - \varphi_0(d_{\min})) \rfloor$ and $d^*$ solves $\varphi_0(d^*) = \gamma_{OAR} - K\varphi_0(d_{\min}) - (N-K-1)\varphi_0(d_{\max})$. Solutions with unequal doses are unique only up to permutation.
- If $\omega_\delta = 0$, every feasible pair with $E_{OAR} = \gamma_{OAR}$ is optimal.

In every case the optimal number of fractions increases with $\gamma_{OAR}$, decreases with $\alpha_0$, $\beta_0$ and $\delta$, and does not depend on $\alpha_T$, $\beta_T$.

## Expansion

For fixed $N$ the problem maximizes a convex function, a nonconvex quadratically constrained program. For $N > \lambda_0$ the OAR constraint must be active, and on the surface $E_{OAR} = \gamma_{OAR}$ one has $\sum d_i^2 = (\gamma_{OAR} - \alpha_0\delta\sum d_i)/(\beta_0\delta^2)$, so $E_T = \beta_T \gamma_{OAR}/(\beta_0\delta^2) + \beta_T\, \omega_\delta \sum d_i$ exactly: the problem reduces to maximizing ($\omega_\delta > 0$) or minimizing ($\omega_\delta < 0$) the total dose on the constraint surface. Maximizing $\sum d_i$ on this sphere gives equal doses; minimizing it pushes doses to the box corners, with one coordinate absorbing the remainder. Comparing the resulting values across the finitely many feasible $N \in [1, \rho_0]$ shows monotonicity in $N$, which pins $\bar N$ at the largest or smallest feasible value. Unlike earlier treatments with only $d_i \ge 0$, the positive lower bound $d_{\min}$ is what keeps the number of fractions finite and the solution in closed form. These are Theorems 4–8, Proposition 3 and Corollary 1 of the source.

## Sources

- L. A. Fernández and L. Fernández, *Analytical solution to the radiotherapy fractionation problem including dose bound constraints*, arXiv:2102.08237 (2021), Section "Maximizing the effect of radiation on the tumor", Theorems 4–8, Proposition 3, Corollary 1. <https://doi.org/10.48550/arXiv.2102.08237> Published version: Operations Research Forum 3 (2022) 40, <https://doi.org/10.1007/s43069-022-00146-8>.
