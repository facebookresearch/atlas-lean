# Global stability of the tumor-free equilibrium

In the [glioblastoma–immune model](gbm-immune-model-tumour-free-equilibrium.md), let $\bar C$, $\bar T$, $\bar M > 0$ be upper bounds with $C(t) \le \bar C$, $T(t) \le \bar T$, $M(t) \le \bar M$ for all $t \ge 0$ along a positive solution (such bounds exist by boundedness, with $\bar C = \max\{C(0), C_{\max}\}$). Define

$$\beta = \frac{a_T}{\big(1 + \rho\bar T(\bar T + \varepsilon_C\bar C)\big)\big(r\bar M + d_T\big)}.$$

**Statement.** If

$$\lambda_C < \eta\,\beta,$$

then the tumor-free equilibrium $(0, T_0^*, 0)$ is globally stable: every solution starting with positive values converges to it, and in particular the tumor is eliminated, $C(t) \to 0$.

The condition requires T-cell activation and killing to beat tumor growth even at the worst-case levels of PD-L1–PD-1 inhibition and MDSC suppression; it points to $\varepsilon_C$, $r$ and $C_{\max}$ as treatment targets (through anti-PD-1/PD-L1 therapy, L-arginine and surgical resection, respectively).

## Depends on

- [Tumor-free equilibrium of the glioblastoma–immune model](gbm-immune-model-tumour-free-equilibrium.md)

## Expansion

Using the bounds and $T C \ge 0$ in the numerator, $dT/dt \ge \gamma - (r\bar M + d_T)T$ with $\gamma = a_T/(1 + \rho\bar T(\bar T + \varepsilon_C\bar C))$, so by comparison $\liminf_{t\to\infty}T(t) \ge \gamma/(r\bar M + d_T) = \beta$. Then for large $t$, $dC/dt \le C(\lambda_C - \eta T) \le C(\lambda_C - \eta(\beta - \epsilon)) $, which is negative for small $\epsilon > 0$, so $C(t) \to 0$ exponentially; the $M$ equation then gives $M \to 0$, and the $T$ equation becomes asymptotically autonomous with unique attracting equilibrium $T_0^*$.

## Sources

- H. G. Anderson, G. P. Takacs, D. C. Harris, Y. Kuang, J. K. Harrison and T. L. Stepien, "Global stability and parameter analysis reinforce therapeutic targets of PD-L1-PD-1 and MDSCs for glioblastoma", Journal of Mathematical Biology 88 (2024), article 10, <https://doi.org/10.1007/s00285-023-02027-y> (PMC10724342), section 3, Theorem 5.
