# Steady states of the state-dependent-delay operon model

For the [state-dependent-delay operon model](goodwin-operon-model-with-state-dependent-delays.md) with positive production coefficients $\beta_M,\beta_I,\beta_E>0$, positive loss rates $\bar\gamma_M,\bar\gamma_I,\bar\gamma_E>0$ and $0\le f\le1$, at a steady state $(M^*,I^*,E^*)$ the delays are $\tau_M^*=a_M/v_M(E^*)$ and $\tau_I^*=a_I/v_I(M^*)$, the velocity ratios equal $1$, and

$$M^*=\frac{\beta_M}{\bar\gamma_M}e^{-\mu\tau_M^*(E^*)}f(E^*),\qquad I^*=\frac{\bar\gamma_E}{\beta_E}E^*,$$

where $E^*$ is a root of

$$g_E(E)=\frac{\beta_M\beta_I\beta_E}{\bar\gamma_M\bar\gamma_I\bar\gamma_E}\,e^{-\mu\left(\tau_I^*(M^*(E))+\tau_M^*(E)\right)}f(E)-E.$$

Every steady state satisfies $E^*\le\frac{\beta_M\beta_I\beta_E}{\bar\gamma_M\bar\gamma_I\bar\gamma_E}$ and $I^*\le\frac{\beta_M\beta_I}{\bar\gamma_M\bar\gamma_I}$. If $\mu=0$ or both delays are constant, $g_E(E)=C\,f(E)-E$ for a constant $C>0$; then a repressible operon (decreasing $f$) has exactly one steady state, and an inducible operon with the Hill-type $f$ above (one inflection point in $E>0$) has at most three. When $\mu>0$ and the delays are state dependent, the delays enter $g_E$ and additional steady states can appear.

## Depends on

- [Goodwin operon model with state-dependent transcription and translation delays](goodwin-operon-model-with-state-dependent-delays.md)

## Proof depends on

- [Goodwin operon model with state-dependent transcription and translation delays](goodwin-operon-model-with-state-dependent-delays.md)

## Expansion

Setting derivatives to zero, constant histories make the threshold integrals equal $v\tau$, which fixes the delays, and the velocity ratios cancel. Solving the $M$ and $E$ equations (dividing by $\bar\gamma_M$ and $\beta_E$) and substituting into the $I$ equation (dividing by $\bar\gamma_I$) leaves the scalar equation $g_E(E)=0$. The bounds follow from $f\le1$ and $e^{-\mu\tau}\le1$. For constant delays, $g_E$ is strictly decreasing in the repressible case; in the inducible case $g_E'=Cf'-1$ changes sign at most twice because $f'$ is unimodal, so $g_E$ has at most three zeros. Numerically, state-dependent delays give three steady states in a repressible case and five in an inducible case, impossible with constant delays.

## Sources

- T. Gedeon, A. R. Humphries, M. C. Mackey, H.-O. Walther, Z. Wang, "Operon dynamics with state dependent transcription and/or translation delays", J. Math. Biol. 84 (2022), article 2, Section 2.6, Equations (2.23)–(2.29), Table 1 and Figures 2–3, <https://doi.org/10.1007/s00285-021-01693-0>.
