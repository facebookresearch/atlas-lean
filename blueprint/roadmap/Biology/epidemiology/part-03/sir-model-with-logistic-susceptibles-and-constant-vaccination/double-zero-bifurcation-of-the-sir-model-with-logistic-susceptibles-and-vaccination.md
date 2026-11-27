# Double-zero bifurcation of the SIR model with logistic susceptibles and constant vaccination

**Model.** Let $A, \beta, m, \mu, d, g > 0$ (carrying capacity of susceptibles, transmission rate, birth rate, natural death rate, disease-induced death rate, recovery rate), let $p \ge 0$ be the proportion of newborns successfully vaccinated, and put $\sigma = \mu + d$. Susceptibles grow logistically and a constant vaccination flux $pm$ is removed from them. Since the recovered class decouples, the dynamics reduce to

$$\dot S = S(A - S) - \beta I S - p m, \qquad \dot I = \beta I S - (\sigma + g) I,$$

on $(S, I) \in [0,\infty)^2$, extended by $\dot S = 0$, $\dot I = -(\sigma+g) I$ on the line $S = 0$. The basic reproduction number (computed at $p = 0$) is

$$\mathcal{R}_0 = \frac{A\beta}{\sigma + g}.$$

**Invariant region.** The set $\mathcal{M} = \{(S,I) : 0 \le S \le A,\ 0 \le S + I \le A(\sigma+g+A)/(\sigma+g)\}$ is positively invariant.

**Equilibria.** For $p \le A^2/(4m)$ there are two disease-free equilibria and, formally, one endemic equilibrium:

$$E_0^p = \Big(\tfrac{A - \sqrt{A^2 - 4pm}}{2}, 0\Big), \quad E_1^p = \Big(\tfrac{A + \sqrt{A^2 - 4pm}}{2}, 0\Big), \quad E_2^p = \Big(\tfrac{\sigma+g}{\beta}, \tfrac{-pm\beta^2 + A(\sigma+g)\beta - (\sigma+g)^2}{\beta^2(\sigma+g)}\Big).$$

**Theorem (codimension-two organizing centre).** In the parameter plane $(\mathcal{R}_0, p)$, the endemic equilibrium $E_2^p$ undergoes a double-zero (Bogdanov–Takens type) bifurcation at

$$(\mathcal{R}_0^\star, p^\star) = \Big(2, \frac{A^2}{4m}\Big),$$

where the Jacobian at $E_2^p$ is nilpotent with a double zero eigenvalue. The following curves pass through this point:

- saddle-node curve $\mathbf{SN}$: $p = A^2/(4m)$;
- transcritical curve $\mathbf{T}$: $p = \dfrac{A^2}{m}\dfrac{\mathcal{R}_0 - 1}{\mathcal{R}_0^2}$;
- Belyakov transition curve $\mathbf{B_t}$ (eigenvalues of the Jacobian at $E_2^p$ change between real and non-real): $p = \dfrac{\big(-2\beta + 1 + 2\sqrt{\beta(\mathcal{R}_0 + \beta - 2)}\big)A^2}{m\mathcal{R}_0^2}$;
- heteroclinic-cycle curve, obtained by numerical interpolation: $p \approx 4.495\,\mathcal{R}_0^{-2.313} - 0.039$;
- Hopf curve $\mathbf{H}$: $p = \dfrac{A^2}{m\mathcal{R}_0^2}$.

On the Hopf curve the equilibrium $E_2^p$ undergoes a **subcritical** Hopf bifurcation, producing an unstable periodic orbit as $\mathcal{R}_0$ increases. Writing $p_{SN}, p_T, p_H$ for the right-hand sides of the $\mathbf{SN}$, $\mathbf{T}$ and $\mathbf{H}$ curves, one has $p_T(\mathcal{R}_0) < p_{SN}(\mathcal{R}_0)$ for $\mathcal{R}_0 > 1$, $\mathcal{R}_0 \ne 2$; all three coincide at $\mathcal{R}_0 = 2$; and $p_H < p_T < p_{SN}$ for $\mathcal{R}_0 > 2$.

**Consequence.** There are open regions of the $(\mathcal{R}_0, p)$ plane in which the disease persists on a set of initial conditions of positive measure, including a region where an unstable limit cycle born at the Hopf curve bounds the basin of the endemic equilibrium; high vaccination does not eliminate the disease when $A$ is small relative to the infected population being generated.

## Depends on

- [Threshold and Belyakov transition of the logistic SIR model without vaccination](threshold-and-belyakov-transition-of-the-logistic-sir-model-without-vaccination.md)
- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

At $(\mathcal{R}_0, p) = (2, A^2/(4m))$ one has $pm\beta^2 = (\sigma+g)^2$, so the trace of the Jacobian at $E_2^p$ vanishes, and the lower-left entry $(-pm\beta^2 + A(\sigma+g)\beta - (\sigma+g)^2)/(\beta(\sigma+g))$ also vanishes; the Jacobian becomes $\begin{pmatrix} 0 & -(\sigma+g) \\ 0 & 0 \end{pmatrix}$. Instead of checking the normal-form nondegeneracy conditions, the authors verify analytically each codimension-one curve through this point: $E_0^p$ and $E_1^p$ collide when $A^2 = 4pm$ (saddle-node); $E_2^p$ crosses $E_0^p$ or $E_1^p$ when its $I$-coordinate vanishes (transcritical); the trace vanishes when $pm\beta^2 = (\sigma+g)^2$, i.e. $p = A^2/(m\mathcal{R}_0^2)$, and the real part of the eigenvalues has derivative $A/(2\mathcal{R}_0^2) \ne 0$ in $\mathcal{R}_0$ there (Hopf). The heteroclinic curve connecting the saddles $E_0^p$ and $E_1^p$ is located numerically at thirteen parameter points and fitted by $y = a x^b + c$.

## Sources

- J. P. S. Maurício de Carvalho and A. A. Rodrigues, "SIR model with vaccination: bifurcation analysis", arXiv:2211.16339 (2022): model in Section 3, Lemma 1 (invariant region), Theorem A (main result, Section 4), Lemma 3 (ordering of the bifurcation curves) and Lemma 8 (subcritical Hopf bifurcation, Section 6). <https://doi.org/10.48550/arXiv.2211.16339>. Published version: Qualitative Theory of Dynamical Systems 22(3) (2023), article 105, <https://doi.org/10.1007/s12346-023-00802-2>; locators above refer to the arXiv version.
