# Tumor-free equilibrium of the glioblastoma–immune model

Let $C(t)$, $T(t)$, $M(t)$ be the numbers of glioma cells, activated T cells and MDSCs, with all parameters positive:

$$\frac{dC}{dt} = \lambda_C C\Big(1 - \frac{C}{C_{\max}}\Big) - \eta T C,$$

$$\frac{dT}{dt} = \frac{a_T + s_T T C}{1 + \rho T(T + \varepsilon_C C)} - r T M - d_T T,$$

$$\frac{dM}{dt} = s_M C + \frac{\alpha C}{q + C} - d_M M.$$

Here $\lambda_C$ and $C_{\max}$ are the tumor growth rate and carrying capacity, $\eta$ the kill rate of tumor cells by T cells, $a_T$ the T-cell activation rate, $s_T$ tumor-stimulated T-cell recruitment, $\rho$ the inhibition of T cells by PD-L1–PD-1 complexes, $\varepsilon_C$ the expression of PD-L1 on tumor cells relative to T cells, $r$ the suppression of T cells by MDSCs, $d_T$, $d_M$ death rates, $s_M$ chemokine-driven (CCL2/CCL7) MDSC recruitment, and $lpha$, $q$ the rate and steepness coefficient of MDSC expansion.

**Statement.**

1. Solutions starting with $C, T, M > 0$ stay positive and bounded; in particular $C(t) \le \max\{C(0), C_{\max}\}$.
2. There is a unique tumor-free equilibrium $(0, T_0^*, 0)$, where $T_0^*$ is the unique positive root of $d_T\rho T^3 + d_T T - a_T = 0$; $T_0^*$ is increasing in $a_T$ and decreasing in $d_T$ and $\rho$.
3. The Jacobian at $(0, T_0^*, 0)$ has eigenvalues

$$\lambda_1 = \lambda_C - \eta T_0^*, \qquad \lambda_2 = -\frac{2a_T\rho T_0^*}{(1 + \rho T_0^{*2})^2} - d_T < 0, \qquad \lambda_3 = -d_M < 0.$$

Hence the tumor-free equilibrium is locally asymptotically stable if $\lambda_C < \eta T_0^*$ and a saddle if $\lambda_C > \eta T_0^*$.

## Proof depends on

- [Explicit solution of the logistic equation](../../../../../population-dynamics/logistic-growth-equation/logistic.md)

## Expansion

With $C = 0$ the $M$ equation forces $M = 0$, and the $T$ equation reduces to $d_T T(1 + \rho T^2) = a_T$; the cubic $d_T\rho T^3 + d_T T - a_T$ has one sign change, hence by Descartes' rule exactly one positive root, and implicit differentiation gives the monotonicity. At $C = 0$ the Jacobian is block triangular: the $C$ row has the single entry $\lambda_C - \eta T_0^*$, the $M$ row contributes $-d_M$, and $\lambda_2$ is the derivative of $a_T/(1 + \rho T^2) - d_T T$ at $T_0^*$. Positivity uses $dT/dt = a_T > 0$ on $\{T = 0\}$ and the exponential representation of $C$.

## Sources

- H. G. Anderson, G. P. Takacs, D. C. Harris, Y. Kuang, J. K. Harrison and T. L. Stepien, "Global stability and parameter analysis reinforce therapeutic targets of PD-L1-PD-1 and MDSCs for glioblastoma", Journal of Mathematical Biology 88 (2024), article 10, <https://doi.org/10.1007/s00285-023-02027-y> (PMC10724342), section 2, Equation (1), and Theorems 1–4.
