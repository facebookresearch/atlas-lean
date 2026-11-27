# Equilibria and stability of the logistic target-cell model

**Model.** Uninfected hepatocytes $T$, infected hepatocytes $I$, free virus $V$ and secreted surface antigen $S$ obey

$$\dot T = rT\Big(1 - \frac{T + I}{K}\Big) - \beta T V, \qquad \dot I = \beta T V - \delta I, \qquad \dot V = pI - cV, \qquad \dot S = r_S I - d_S S,$$

with logistic regrowth (maximal rate $r$, carrying capacity $K$ shared by uninfected and infected cells), infectivity $\beta$, infected-cell death $\delta$, virion production $p$ and clearance $c$, and antigen production $r_S$ and decay $d_S$; all parameters positive.

**Proposition.** Let $R_0 = \dfrac{K\beta p}{c\delta}$, the expected number of cells infected by the progeny of one infected cell in a fully uninfected liver.
1. The equilibria are the trivial $E_0 = (0,0,0,0)$, the infection-free $E_1 = (K, 0, 0, 0)$, and, if and only if $R_0 > 1$, the chronic equilibrium

$$E_2:\quad T^\ast = \frac{K}{R_0}, \qquad I^\ast = \frac{r(1 - 1/R_0)}{r/K + \beta p/c}, \qquad V^\ast = \frac{p}{c}I^\ast, \qquad S^\ast = \frac{r_S}{d_S} I^\ast .$$

2. $E_1$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
3. If $R_0 > 1$, the Jacobian at $E_2$ has eigenvalue $-d_S$ and three others solving $\lambda^3 + A_1\lambda^2 + A_2\lambda + A_3 = 0$ with $A_1 = c + \delta + r/R_0 > 0$, $A_2 > 0$ and $A_3 = c\,\delta\, r\,(R_0 - 1)/R_0 > 0$; hence $E_2$ is locally asymptotically stable exactly when $A_1A_2 - A_3 > 0$, which is equivalent to

    $$\big(\delta^2 + (3c + r)\delta + c^2\big)(\delta R_0 + r)R_0 + c\big(r^2 - R_0^3\delta^2\big) > 0,$$

    and loses stability (with oscillations around $E_2$) when the inequality is reversed.

## Depends on

- [Threshold and stability of the infected equilibrium](../within-host-effector-t-cell-model/threshold-and-stability-of-the-infected-equilibrium.md)

## Expansion

At $E_1$ the infected subsystem $(I, V)$ has Jacobian $\begin{pmatrix} -\delta & \beta K \\ p & -c\end{pmatrix}$, with determinant $c\delta - \beta pK = c\delta(1 - R_0)$, so the infection grows iff $R_0 > 1$; $T$ contributes the eigenvalue $-r$ and $S$ the eigenvalue $-d_S$, and $S$ never feeds back, so it only reports $I$. At $E_2$, the equation $\dot I = 0$ with $V = pI/c$ forces $\beta T^\ast p/c = \delta$, i.e. $T^\ast = K/R_0$, and the logistic balance $r(1 - (T^\ast + I^\ast)/K) = \beta V^\ast$ gives $I^\ast$. The remaining cubic follows from the $3 \times 3$ block in $(T, I, V)$, and the Routh–Hurwitz criterion for cubics (all coefficients positive and $A_1A_2 > A_3$) gives the stability condition; large $R_0$ with slow infected-cell death favours its violation and hence oscillatory chronic infection. An extension in which infected cells are cured at rate $\rho$ into a proliferating class refractory to reinfection (with waning back to susceptibility) lowers the chronic viral load while leaving antigen levels similar.

## Sources

- S. M. Ciupe, H. Dahari and A. Ploss, "Mathematical models of early hepatitis B virus dynamics in humanized mice", Bulletin of Mathematical Biology 86 (2024), 53, Mathematical Model (Eq. 1) and Analytical Results (equilibria, Eq. 4, Propositions 1–2), <https://doi.org/10.1007/s11538-024-01284-2>, PMCID: PMC11003933.
