# Nondimensionalization of the adiabatic stirred-tank reactor

Consider an adiabatic stirred-tank reactor of constant volume and pressure with dilution rate $D = Q/V > 0$, feed
concentration $C_{\mathrm{in}} > 0$, feed absolute temperature $T_{\mathrm{in}} > 0$ and one first-order reaction with
Arrhenius rate constant $k_0 e^{-E_a/(R T)}$, $k_0, E_a, R > 0$, constant density times heat capacity $\rho c_p > 0$
for feed and contents, and temperature-independent reaction enthalpy $\Delta H \le 0$:

$$C' = D(C_{\mathrm{in}} - C) - k_0 e^{-E_a/(R T)}\,C, \qquad
T' = D(T_{\mathrm{in}} - T) + \frac{-\Delta H}{\rho c_p}\,k_0 e^{-E_a/(R T)}\,C .$$

With $\tau = D t$, $c = C/C_{\mathrm{in}}$, $\theta = T/T_{\mathrm{in}}$, $a = \log(k_0/D)$, $b = E_a/(R T_{\mathrm{in}}) > 0$
and $\beta = -\Delta H\,C_{\mathrm{in}}/(\rho c_p T_{\mathrm{in}}) \ge 0$, a pair $(C, T)$ with $T > 0$ on a time interval $I$ solves
these balances on $I$ if and only if $(c, \theta)$, with $\theta > 0$, solves the dimensionless adiabatic reactor with
parameters $a$, $b$, $\beta$ on the rescaled interval $D I$; equilibria with positive temperature correspond in the same
way, and initial values with $C(0) \in [0, C_{\mathrm{in}}]$, $T(0) > 0$ map to $c(0) \in [0, 1]$, $\theta(0) > 0$.

The proof divides the balances by $D C_{\mathrm{in}}$ and $D T_{\mathrm{in}}$ and uses
$k_0 e^{-E_a/(R T_{\mathrm{in}} \theta)}/D = e^{a - b/\theta}$. A cooled reactor ($UA > 0$) has a different ratio of
thermal and material relaxation and is not of this form; neither is the constant-rate case $E_a = 0$, for which
$b = 0$.

## Depends on

- [Steady states and an energy invariant of the dimensionless adiabatic reactor](steady-states-of-the-dimensionless-adiabatic-reactor.md), for the dimensionless reactor

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 6.3, the transient material and energy balances, Equations 6.30–6.32 (pp. 284–285); Section 6.3.1, the material balance before Equation 6.37 and the energy balance with $U^o = 0$ (pp. 288–289).
