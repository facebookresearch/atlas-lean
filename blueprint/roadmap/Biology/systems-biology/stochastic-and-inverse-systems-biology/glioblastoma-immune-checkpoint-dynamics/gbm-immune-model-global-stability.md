# Convergence to the tumor-free equilibrium under trajectory bounds

In the [glioblastoma–immune model](gbm-immune-model-tumour-free-equilibrium.md), fix a solution $(C, T, M)$ with positive initial values, and let $\bar C$, $\bar T$, $\bar M > 0$ be upper bounds with $C(t) \le \bar C$, $T(t) \le \bar T$, $M(t) \le \bar M$ for all $t \ge 0$ along this solution (such bounds exist by boundedness, with $\bar C = \max\{C(0), C_{\max}\}$; in general they depend on the initial state). Define

$$\beta = \frac{a_T}{\big(1 + \rho\bar T(\bar T + \varepsilon_C\bar C)\big)\big(r\bar M + d_T\big)}.$$

**Statement.** If

$$\lambda_C < \eta\,\beta,$$

then this solution converges to the tumor-free equilibrium $(0, T_0^*, 0)$; in particular the tumor is eliminated, $C(t) \to 0$, exponentially fast. If the same constants $\bar C, \bar T, \bar M$ bound every solution with positive initial values in a set $\mathcal S$ of initial states and satisfy the inequality, then every solution starting in $\mathcal S$ converges to $(0, T_0^*, 0)$. Since such a solution has $\liminf T \ge \beta$ and $T \to T_0^*$, the inequality also gives $\lambda_C < \eta T_0^*$, so the equilibrium is locally asymptotically stable as well.

For a given trajectory, the condition requires T-cell activation and killing to beat tumor growth even at the worst-case levels of PD-L1–PD-1 inhibition and MDSC suppression; it points to $\varepsilon_C$, $r$ and $C_{\max}$ as treatment targets (through anti-PD-1/PD-L1 therapy, L-arginine and surgical resection, respectively).

## Depends on

- [Tumor-free equilibrium of the glioblastoma–immune model](gbm-immune-model-tumour-free-equilibrium.md)

## Expansion

Using the bounds and $T C \ge 0$ in the numerator, $dT/dt \ge \gamma - (r\bar M + d_T)T$ with $\gamma = a_T/(1 + \rho\bar T(\bar T + \varepsilon_C\bar C))$, so by comparison $\liminf_{t\to\infty}T(t) \ge \gamma/(r\bar M + d_T) = \beta$. Then for large $t$, $dC/dt \le C(\lambda_C - \eta T) \le C(\lambda_C - \eta(\beta - \epsilon))$, which is negative for small $\epsilon > 0$, so $C(t) \to 0$ exponentially; the $M$ equation then gives $M \to 0$, and the $T$ equation becomes asymptotically autonomous with unique attracting equilibrium $T_0^*$.

## Sources

- H. G. Anderson, G. P. Takacs, D. C. Harris, Y. Kuang, J. K. Harrison and T. L. Stepien, "Global stability and parameter analysis reinforce therapeutic targets of PD-L1-PD-1 and MDSCs for glioblastoma", Journal of Mathematical Biology 88 (2024), article 10, <https://doi.org/10.1007/s00285-023-02027-y> (PMC10724342), section 3, Theorem 5.
