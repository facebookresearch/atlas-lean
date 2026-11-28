# Per-cycle tumor growth exponent under periodic bolus dosing

**Model.** Proliferating tumor cells $x_1$ grow exponentially at rate $\beta_1 > 0$ (below the switch to linear growth) and are damaged by drug at rate $\gamma(u)$, where $u(t)$ is plasma concentration; damaged cells pass through a chain of transit compartments with rate $k_1 > 0$:

$$\dot x_1 = \beta_1 x_1 - \gamma(u)\, x_1, \qquad \dot x_2 = \gamma(u) x_1 - k_1 x_2, \qquad \dot x_j = k_1 (x_{j-1} - x_j), \ j = 3, \dots, n.$$

The pharmacodynamic effect is a piecewise-linear threshold (hybrid) model approximating a sigmoidal $E_{\max}$ curve:

$$\gamma(u) = \begin{cases} 0, & u < \underline\theta,\\ q\,(u - \underline\theta), & \underline\theta \le u < \overline\theta,\\ q\,(\overline\theta - \underline\theta), & u \ge \overline\theta, \end{cases}$$

with $q > 0$ and $E_{\max} = q(\overline\theta - \underline\theta)$. A bolus every $\tau$ produces $u(t) = \zeta e^{-\lambda_d (t - k\tau)}$ on $[k\tau, (k+1)\tau)$ (no accumulation), with elimination rate $\lambda_d > 0$.

**Theorem 1 (proliferating cells dominate).** For frozen $u$, the linear system has a lower-triangular matrix with eigenvalues $\beta_1 - \gamma(u), -k_1, \dots, -k_1$. Hence all compartments decay when $\gamma(u) > \beta_1$ and the tumor grows exponentially when $\gamma(u) < \beta_1$: the sign of the net proliferation rate of $x_1$ decides the response of the whole tumor.

**Per-cycle exponent.** Suppose $\underline\theta < \zeta \le \overline\theta$ and the concentration falls below $\underline\theta$ within the cycle, that is $\ln(\zeta/\underline\theta)/\lambda_d \le \tau$. Then $x_1((k+1)\tau) = x_1(k\tau)\, e^{\Psi}$ with

$$\Psi = \beta_1 \tau + \frac{q}{\lambda_d}\Big[\zeta\ln\zeta - \underline\theta \ln\underline\theta - (1 + \ln\zeta)(\zeta - \underline\theta)\Big] = \beta_1\tau - \frac{q}{\lambda_d}\Big[\zeta - \underline\theta - \underline\theta\ln\frac{\zeta}{\underline\theta}\Big].$$

The regimen shrinks the proliferating pool over each cycle iff $\Psi < 0$. For $\zeta > \overline\theta$ the same computation, with the saturated phase, gives $\Psi = \beta_1 \tau + \frac{q}{\lambda_d}\big[\overline\theta\ln\overline\theta - \underline\theta \ln\underline\theta - (1 + \ln\zeta)(\overline\theta - \underline\theta)\big]$.

## Expansion

On each cycle the equation for $x_1$ is scalar and linear, so $\ln\big(x_1((k+1)\tau)/x_1(k\tau)\big) = \beta_1\tau - \int_{k\tau}^{(k+1)\tau} \gamma(u(t))\,dt$. The drug acts only while $u \ge \underline\theta$, which lasts $T = \ln(\zeta/\underline\theta)/\lambda_d$, and

$$\int_0^T q\big(\zeta e^{-\lambda_d s} - \underline\theta\big)\,ds = \frac{q}{\lambda_d}\Big[\zeta - \underline\theta - \underline\theta \ln\frac{\zeta}{\underline\theta}\Big],$$

the area of the concentration curve above the threshold; expanding $\ln(\zeta/\underline\theta)$ recovers the first form. With fixed total drug intake, $\zeta$ grows linearly with $\tau$: frequent small doses spend little time above $\underline\theta$, rare large doses waste drug above saturation and leave long drug-free regrowth, so $\Psi < 0$ holds only in an intermediate window of schedules ("drug efficacy regions"), and slower elimination enlarges it.

## Sources

- X. Li, L. Qian, M. L. Bittner, E. R. Dougherty, "A Systems Biology Approach in Therapeutic Response Study for Different Dosing Regimens: a Modeling Study of Drug Effects on Tumor Growth using Hybrid Systems", Cancer Informatics 11 (2012) 41, Equations (1)-(14), the expressions for $\Psi$, Theorem 1 and Appendix A, <https://doi.org/10.4137/cin.s8185>, PMCID PMC3298374.
