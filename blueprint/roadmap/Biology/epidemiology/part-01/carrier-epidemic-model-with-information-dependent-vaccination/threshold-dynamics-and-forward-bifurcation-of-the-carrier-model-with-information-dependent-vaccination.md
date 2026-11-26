# Threshold dynamics and forward bifurcation of the carrier model with information-dependent vaccination

**Setting.** Consider the $SVCIRM$ carrier model with information-dependent vaccination rate $\nu_0 + bM$, its absorbing region $\Omega$, disease-free equilibrium $E_0$ and basic reproduction number

$$\mathcal R_0 = \frac{\beta \mu}{(\mu + \nu_0)(\sigma + \delta + \mu)} \Bigl(\epsilon + \frac{\sigma}{\rho + \mu + d}\Bigr),$$

as defined in [Reproduction number of the carrier model with information-dependent vaccination](reproduction-number-of-the-carrier-model-with-information-dependent-vaccination.md).

**Results.**
1. (Proposition 1) If $\mathcal R_0 > 1$ the model has a unique endemic equilibrium $E^*$; if $\mathcal R_0 < 1$ it has none.
2. (Proposition 2) $E_0$ is locally asymptotically stable in $\Omega$ if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.
3. (Proposition 3) If $\mathcal R_0 < 1$, $E_0$ is globally asymptotically stable in $\Omega$.
4. (Theorem 2) With $\beta$ as bifurcation parameter and critical value

$$\beta^* = \frac{(\mu + \nu_0)(\sigma + \delta + \mu)(\rho + \mu + d)}{\mu\,[\epsilon (\rho + \mu + d) + \sigma]},$$

equivalent to $\mathcal R_0 = 1$, the system undergoes a forward (supercritical transcritical) bifurcation at $E_0$: as $\mathcal R_0$ crosses $1$ from below, $E_0$ loses stability and the endemic equilibrium that emerges is locally asymptotically stable for $\mathcal R_0$ near $1$.

Hence information-dependent vaccination cannot create a backward bifurcation in this model, and since $b$ does not enter $\mathcal R_0$, eradication requires the behaviour-independent rate $\nu_0$ alone to push $\mathcal R_0$ below $1$.

## Expansion

At equilibrium every compartment is proportional to $I^*$ ($C^* = \frac{\rho + \mu + d}{\sigma} I^*$, $M^* = k I^*$, and so on), and $I^*$ solves a quadratic $f(I) = b_2 I^2 + b_1 I + b_0$ with $b_2 > 0$ and $b_0$ a positive multiple of $\mathcal R_0 - 1$. Since $N^* > 0$ forces $I^* < \Lambda/d$ and $f(\Lambda/d) < 0$, for $\mathcal R_0 > 1$ the convex $f$ goes from positive to negative on $[0, \Lambda/d]$ and has exactly one root there. Local stability of $E_0$ is the van den Driessche–Watmough threshold theorem; global stability follows from the Kamgang–Sallet criterion for epidemic systems. For the bifurcation, the Jacobian at $(E_0, \beta^*)$ has a simple zero eigenvalue and five negative ones; with right and left null vectors $u, v$ ($v$ supported on $C, I$), the Castillo-Chavez–Song coefficients satisfy $A_1 = v \cdot D_{x\beta} f\, u > 0$ and $A_2 = \frac12 v \cdot D_{xx} f\, (u, u) < 0$, which is the forward case.

## Depends on

- [Reproduction number of the carrier model with information-dependent vaccination](reproduction-number-of-the-carrier-model-with-information-dependent-vaccination.md)

## Proof depends on

- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- B. Buonomo, A. d'Onofrio, S. M. Kassa, Y. H. Workineh, "Modeling the effects of information-dependent vaccination behavior on meningitis transmission", arXiv:2005.11823 (2020), Proposition 1 (Section 3), Propositions 2–3 and Theorem 2 (Section 4). <https://doi.org/10.48550/arXiv.2005.11823>
