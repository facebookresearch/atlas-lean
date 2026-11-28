# Endemic equilibrium and Routh–Hurwitz stability of the SIRWS model with asymmetric immunity partition

**Model (SIRWS).** In a normalized population ($S + I + R + W = 1$) with birth and death rate $\mu > 0$, transmission rate $\beta > 0$ and recovery rate $\gamma > 0$, recovered individuals pass from full immunity $R$ to waning immunity $W$ and then back to $S$. The total immune period is $1/\kappa$, split into a full-immunity period $1/(\alpha\kappa)$ and a waning period $1/(\omega\kappa)$ with $\alpha, \omega > 1$ and

$$
\frac{1}{\alpha\kappa} + \frac{1}{\omega\kappa} = \frac{1}{\kappa}, \qquad\text{i.e.}\qquad \omega = \frac{\alpha}{\alpha - 1}.
$$

Exposure of a $W$ individual to infection boosts it back to $R$ at rate $\nu\beta I$ ($\nu > 0$):

$$
\begin{aligned}
\dot S &= -\beta I S + \omega\kappa W + \mu(1 - S), &
\dot I &= \beta I S - (\gamma + \mu) I,\\
\dot R &= \gamma I - \alpha\kappa R + \nu\beta I W - \mu R, &
\dot W &= \alpha\kappa R - \omega\kappa W - \nu\beta I W - \mu W .
\end{aligned}
$$

The classical symmetric case is $\alpha = \omega = 2$.

**Statement.** Let $\mathcal{R}_0 = \beta/(\gamma + \mu)$.

1. *Equilibria.* There is a unique disease-free equilibrium $(S,I,R) = (1,0,0)$. If $\mathcal{R}_0 \le 1$ there is no other equilibrium in the feasible simplex. If $\mathcal{R}_0 > 1$ there is a unique positive endemic equilibrium, with $S^* = (\gamma + \mu)/\beta$ and

$$
I^* = \frac{\sqrt{(c_1\nu + c_2)^2 + c_3\nu} + c_1\nu - c_2}{2\beta\nu(\gamma + \mu)},
$$

where $c_1 = \mu(\beta - \gamma - \mu)$, $c_2 = (\gamma + \mu)(\alpha + \omega)\kappa + \mu(\gamma + \mu) + \alpha\omega\kappa^2$ and $c_3 = 4\gamma(\beta - \gamma - \mu)\alpha\omega\kappa^2$.
2. *Forward bifurcation.* The disease-free equilibrium is locally asymptotically stable for $\mathcal{R}_0 < 1$ and unstable for $\mathcal{R}_0 > 1$, and a transcritical bifurcation of forward type occurs at $\mathcal{R}_0 = 1$: the endemic equilibrium emerges stable.
3. *Stability of the endemic equilibrium.* For $\mathcal{R}_0 > 1$ the linearization at the endemic equilibrium has characteristic polynomial $\lambda^3 + a_1\lambda^2 + a_2\lambda + a_3$ with $a_1, a_2, a_3 > 0$, so it is locally asymptotically stable iff $y_\nu(\alpha) := a_1a_2 - a_3 > 0$; sign changes of $y_\nu$ are Hopf points.
4. *Partition symmetry.* $y_\nu$ depends on $\alpha$ only through $\eta = \kappa(\alpha + \omega) = \kappa\alpha^2/(\alpha - 1) \in [4\kappa, \infty)$. Hence there is a bijection $(1,2) \ni \alpha \mapsto \alpha' \in (2,\infty)$ with $y_\nu(\alpha) = y_\nu(\alpha')$, i.e. swapping the lengths of the full and waning immunity periods leaves the stability of the endemic equilibrium unchanged, and the symmetric partition $\alpha = 2$ is a local extremum of $y_\nu$ for every boosting coefficient $\nu$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Eliminating $W = 1 - S - I - R$, the equilibrium equations force $I = 0$ (giving the disease-free state) or $S^* = (\gamma+\mu)/\beta$; the $S$ equation then makes $I^*$ affine in $R^*$, and the $R$ equation becomes a quadratic in $R^*$ with positive leading coefficient. Its roots give $I^*_\pm$, and the inequality $\sqrt{(c_1\nu + c_2)^2 + c_3\nu} \ge |c_1\nu - c_2| \iff 4c_1c_2 + c_3 \ge 0$ shows $I^*_- \le 0$ and $I^*_+ > 0 \iff \beta > \gamma + \mu$; feasibility follows by summing equations. The transcritical bifurcation is verified with the Castillo-Chavez–Song center-manifold criterion ($Z_1 < 0$, $Z_2 > 0$ for the null vectors of the Jacobian at $\mathcal{R}_0 = 1$). Using $\omega\kappa\beta\nu(1 - S^* - I^* - R^*) = \beta\nu(\gamma + \mu)I^* - c_1\nu$, all coefficients $a_i$ become symmetric functions of $\alpha\kappa$ and $\omega\kappa$, hence functions of $\eta$. Since $d\eta/d\alpha = \kappa\alpha(\alpha - 2)/(\alpha - 1)^2$ vanishes only at $\alpha = 2$ and $y_\nu$ is analytic and not identically zero, the first nonvanishing derivative at $\alpha = 2$ has even order, making it an extremum.

## Sources

- Richmond Opoku-Sarkodie, Ferenc A. Bartha, Mónika Polner and Gergely Röst, "Dynamics of an SIRWS model with waning of immunity and varying immune boosting period", *Journal of Biological Dynamics* 16 (2022), 596–618, <https://doi.org/10.1080/17513758.2022.2109766>. Preprint version: arXiv:2201.07137 (2022), Section 2 (equilibria, Routh–Hurwitz criterion and the $\eta$ substitution), Theorem 1, and Appendices A1–A3 (equilibrium formula, transcritical criterion, composite Taylor coefficients), <https://doi.org/10.48550/arXiv.2201.07137>.
