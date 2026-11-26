# Viral reproduction thresholds in a two-virus oncolytic virotherapy model

**Model.** In dimensionless form, uninfected tumor cells $y_u$, tumor cells infected by Vaccinia virus (VV) $y_1$ or by vesicular stomatitis virus (VSV) $y_2$, and free virions $x_1$ (VV) and $x_2$ (VSV) evolve by
$$\begin{aligned}
\dot y_u &= y_u(1 - y_u - y_1 - y_2) - \beta_1\frac{y_ux_1}{\kappa_1 + Y} - \beta_2^{\mathrm{eff}}\frac{y_ux_2}{\kappa_2 + Y},\\
\dot y_1 &= \beta_1\frac{y_ux_1}{\kappa_1 + Y} - a_1y_1, \qquad \dot y_2 = \beta_2^{\mathrm{eff}}\frac{y_ux_2}{\kappa_2 + Y} - a_2y_2,\\
\dot x_1 &= b_1y_1 - \beta_1\frac{y_ux_1}{\kappa_1 + Y} - \delta_1x_1, \qquad \dot x_2 = b_2y_2 - \beta_2^{\mathrm{eff}}\frac{y_ux_2}{\kappa_2 + Y} - \delta_2x_2,
\end{aligned}$$
where $Y = y_u + y_1 + y_2$, $a_i$ are infected-cell lysis rates, $b_i$ burst sizes, $\delta_i$ virion clearance rates, and

$$\beta_2^{\mathrm{eff}} = \frac{\beta_2}{1 + \frac{\theta_1}{\theta_2 + y_1}\,y_2}$$

is the VSV infection rate reduced by interferon produced by VSV-infected cells and restored by the interferon-neutralizing B18R protein produced by VV-infected cells (the "ping-pong" synergy).

**Theorem.** The system is well posed on $\mathbb{R}^5_+$: solutions exist, are unique, stay nonnegative (positive in $x_1, x_2$) and remain in a bounded invariant region. With the viral basic reproduction numbers

$$\mathcal{R}^1_0 = \frac{b_1\beta_1}{a_1(\delta_1 + \beta_1 + \delta_1\kappa_1)}, \qquad \mathcal{R}^2_0 = \frac{b_2\beta_2}{a_2(\delta_2 + \beta_2 + \delta_2\kappa_2)},$$

1. the tumor-free state $(0,0,0,0,0)$ is unstable;
2. the tumor-dominant state $(1,0,0,0,0)$ is stable iff $\mathcal{R}^1_0 < 1$ and $\mathcal{R}^2_0 < 1$;
3. each single-virus subsystem has a coexistence equilibrium (tumor, infected cells and virus all positive) iff its $\mathcal{R}^i_0 > 1$, and it is then locally asymptotically stable; in the full model the VV-only and VSV-only coexistence states are stable when $\mathcal{R}^1_0 > 1$, respectively $\mathcal{R}^2_0 > 1$;
4. full coexistence equilibria with both viruses persisting exist when both single-virus coexistence states are unstable.

## Depends on

- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

At the tumor-dominant state $y_u = 1$, $Y = 1$, the infected-cell and virion equations for virus $i$ decouple into a linear $2\times 2$ system with infection rate $\beta_i/(\kappa_i + 1)$. The next-generation matrix gives $\mathcal{R}^i_0$: an infected cell produces $b_i/a_i$ virions over its lifetime, each infecting before clearance with probability $\beta_i/(\beta_i + \delta_i(1 + \kappa_i))$. Crossing $\mathcal{R}^i_0 = 1$ is a transcritical bifurcation that hands stability from the tumor-dominant state to the corresponding coexistence state. In the dimensionless model the tumor-free state is unstable because uninfected cells grow logistically from small densities.

## Sources

- J. Malinzi, A. Eladdadi, R. Ouifki and R. Eftimie, "A Predictive Model for Synergistic Oncolytic Virotherapy: Unveiling the Ping-Pong Mechanism and Optimal Timing of Combined Vesicular Stomatitis and Vaccinia Viruses", arXiv:2601.10405 (2026), Theorems 1–4 and Section 6, <https://doi.org/10.48550/arXiv.2601.10405>.
