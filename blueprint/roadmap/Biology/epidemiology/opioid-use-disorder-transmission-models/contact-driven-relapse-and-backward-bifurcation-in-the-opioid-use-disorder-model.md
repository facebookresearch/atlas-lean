# Contact-driven relapse and backward bifurcation in the opioid use disorder model

In the [opioid use disorder model with treatment and relapse](reproduction-number-of-the-opioid-use-disorder-model-with-treatment-and-relapse.md), take no treatment saturation ($\epsilon = 0$) and no recovered-prompted treatment ($\eta_2 = 0$). At an equilibrium with $I^* > 0$, substitute $N^* = (\Lambda - \delta I^*)/\mu$, $S^* = \Lambda N^*/(\beta I^* + \mu N^*)$, and the resulting $T^*$, $R^*$ into $I' = 0$. The equation reduces to a cubic without constant term,

$$0 = I^*\big[a (I^*)^2 + b I^* + c\big],$$

where

$$a = -\mu\alpha_2\big(\beta\eta_1 + \beta\kappa + \beta\mu + \beta\rho + \delta\eta_3\big) \le 0, \qquad c = (N^*)^2 \mu\, \mathcal D\, (\mathcal R_0 - 1),$$

$\mathcal D > 0$ is the denominator of $\mathcal R_0 = \beta(\kappa + \rho + \mu)(\alpha_1 + \mu)/\mathcal D$, and $b$ is an explicit polynomial in the parameters and $N^*$.

**Consequences.**

- *No contact-driven relapse ($\alpha_2 = 0$).* Then $a = 0$, and every term of $b$ is negative, so $b < 0$. The unique candidate $I^* = -c/b$ is positive exactly when $\mathcal R_0 > 1$: endemic equilibria appear only through a forward transcritical bifurcation at $\mathcal R_0 = 1$.
- *Contact-driven relapse ($\alpha_2 > 0$).* Then $a < 0$, and $c < 0$ when $\mathcal R_0 < 1$. By Descartes' rule of signs there are two positive roots or none if $b > 0$, and none if $b < 0$. With $b > 0$, which occurs for sufficiently large $\alpha_2$, two endemic equilibria coexist with the disorder-free equilibrium for $\mathcal R_0 < 1$: a backward bifurcation and a region of bistability. With the source's fitted parameters (except a doubled overdose rate $\delta = 0.06$), this requires $\alpha_2$ of order $10^3$, versus a fitted value of $0.01$.
- *Recovered-prompted treatment without contact-driven relapse ($\epsilon = 0$, $\alpha_2 = 0$, $\eta_2 > 0$).* The Castillo-Chavez–Song bifurcation coefficients at $\mathcal R_0 = 1$ rule out a backward bifurcation.
- *Saturated treatment ($\epsilon > 0$).* In the limiting system with $N = (\Lambda - \delta I)/\mu$, the endemic-equilibrium condition becomes a polynomial of degree 6 in $I^*$. Numerically, there is a critical saturation level above which a backward bifurcation occurs even with $\alpha_2 = 0$, at saturation values within the plausible range.

Since $\mathcal R_0$ does not involve $\alpha_2$, $\eta_2$ or $\epsilon$, these nonlinear relapse and capacity effects change whether pushing $\mathcal R_0$ below $1$ is enough to eliminate OUD without moving the threshold itself.

## Depends on

- [Reproduction number of the opioid use disorder model with treatment and relapse cycling](reproduction-number-of-the-opioid-use-disorder-model-with-treatment-and-relapse.md)

## Expansion

With $\eta_2 = 0$, the common denominator obtained after eliminating $S^*$, $T^*$ and $R^*$ is positive, so the sign structure of the equilibrium equation is carried by the cubic's coefficients. The constant coefficient $c$ is proportional to $\mathcal R_0 - 1$, exactly as in a forward bifurcation. The quadratic coefficient $a$ is the only one proportional to $\alpha_2$, so it vanishes without contact-driven relapse, leaving a linear equation with a single root. When $\alpha_2 > 0$, the leading and constant coefficients are both negative below threshold, and a sign change through $b > 0$ allows two positive roots. Every term of $b$ that can be negative carries a factor $\alpha_2$, which is why $b < 0$ when $\alpha_2 = 0$.

## Sources

- Cole S, Wirkus S. Modeling the dynamics of heroin and illicit opioid use disorder, treatment, and recovery. *Bulletin of Mathematical Biology* 84(4):48 (2022), subsection "Endemic equilibria", system (9), equations (10)–(13), the limiting system (14), and the appendix applying the Castillo-Chavez–Song criterion. <https://doi.org/10.1007/s11538-022-01002-w> (PMCID: PMC8891131)
