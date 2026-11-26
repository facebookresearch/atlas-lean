# Opinion-structured SEIR kinetic model and its closed macroscopic limit

This page covers Sections 2 and 3.1 of Zanella (2023): an SEIR epidemic in which each agent carries an opinion $w \in [-1, 1]$ about protective behaviour, and the moment system obtained when opinions relax fast.

**Kinetic model (eqs. (2)-(4)).** For compartments $J \in \{S, E, I, R\}$ let $f_J(w,t) \ge 0$ be the opinion density, $\rho_J = \int f_J\, dw$ the mass fraction ($\sum_J \rho_J = 1$) and $m_J = \rho_J^{-1}\int w f_J\, dw$ the mean opinion. Then
$$\begin{aligned}
\partial_t f_S &= -K(f_S, f_I) + \tfrac{1}{\tau} Q_S(f_S), \\
\partial_t f_E &= K(f_S, f_I) - \sigma_E f_E + \tfrac{1}{\tau} Q_E(f_E), \\
\partial_t f_I &= \sigma_E f_E - \gamma f_I + \tfrac{1}{\tau} Q_I(f_I), \\
\partial_t f_R &= \gamma f_I + \tfrac{1}{\tau} Q_R(f_R),
\end{aligned}$$
with local incidence $K(f_S, f_I)(w) = f_S(w) \int_{-1}^1 \kappa(w, w_*) f_I(w_*)\, dw_*$ and
$$\kappa(w, w_*) = \frac{\beta}{4^\alpha}(1 - w)^\alpha (1 - w_*)^\alpha, \qquad \beta, \alpha > 0,$$
so agents with stronger protective opinions transmit and acquire infection less. $Q_J$ are the opinion operators of [the Fokker-Planck opinion model](beta-equilibrium-of-opinion-fokker-planck.md), which conserve mass and mean opinion (symmetric interactions, no-flux boundaries), with $\nu_J = \sigma_J^2/\lambda_J$. With constant $\kappa \equiv \beta$ the masses obey the classical SEIR model (Remark 3).

**Macroscopic system for $\alpha = 1$ (eqs. (15)-(17)).** Integrating in $w$ gives, exactly,
$$\dot\rho_S = -\frac{\beta}{4}(1 - m_S)(1 - m_I)\rho_S \rho_I, \quad \dot\rho_E = \frac{\beta}{4}(1 - m_S)(1 - m_I)\rho_S\rho_I - \sigma_E \rho_E, \quad \dot\rho_I = \sigma_E\rho_E - \gamma\rho_I, \quad \dot\rho_R = \gamma\rho_I,$$
which is not closed because the mean opinions appear. In the fast-opinion regime $\tau \ll 1$, each $f_J$ is near its beta equilibrium with mass $\rho_J$ and mean $m_J$; closing the second moment with $\int w^2 f_J = \rho_J (\nu_J + 2m_J^2)/(2 + \nu_J)$ gives
$$\begin{aligned}
\dot m_S &= \frac{\beta}{4} \frac{\nu_S}{2 + \nu_S}(1 - m_I)\rho_I (1 - m_S^2), \\
\dot m_E &= \frac{\beta}{4}\frac{\rho_S\rho_I}{\rho_E}(1 - m_I)\Big[ m_S - \frac{\nu_S + 2m_S^2}{2 + \nu_S} - m_E(1 - m_S) \Big], \\
\dot m_I &= \sigma_E \frac{\rho_E}{\rho_I}(m_E - m_I), \qquad \dot m_R = \gamma\frac{\rho_I}{\rho_R}(m_I - m_R).
\end{aligned}$$

Consequences: $m_S$ is nondecreasing, because infection removes low-protection susceptibles preferentially; it is constant in the consensus limit $\nu_S \to 0^+$ (Remark 2), so the selection effect comes from opinion spread in the susceptible class.

## Depends on

- [Beta equilibrium of the Fokker-Planck opinion model](beta-equilibrium-of-opinion-fokker-planck.md)
- [The SEIR vector field](../seir-epidemic-model/seir-field.md)

## Expansion

For $\alpha = 1$, $\int (1 - w_*) f_I(w_*)\, dw_* = (1 - m_I)\rho_I$, so $K = \tfrac{\beta}{4}(1-w)(1 - m_I)\rho_I f_S$; integrating once more gives the $(1 - m_S)(1 - m_I)\rho_S\rho_I$ incidence, and $Q_J$ drops out because it conserves mass. Multiplying by $w$ and integrating gives $\tfrac{d}{dt}(\rho_S m_S) = -\tfrac{\beta}{4}(1 - m_I)\rho_I \int w(1 - w) f_S\, dw$, which involves the second moment; inserting the beta-equilibrium value and subtracting $m_S\dot\rho_S$ yields $\rho_S \dot m_S = \tfrac{\beta}{4}(1 - m_I)\rho_I\rho_S\big[\tfrac{\nu_S + 2m_S^2}{2 + \nu_S} - m_S^2\big]$, and the bracket equals $\nu_S(1 - m_S^2)/(2 + \nu_S)$. The other means follow the same way. The closure is formal; the source checks it against simulations of the kinetic model (Section 4).

## Sources

- M. Zanella, Kinetic models for epidemic dynamics in the presence of opinion polarization, *Bull. Math. Biol.* 85 (2023), <https://doi.org/10.1007/s11538-023-01147-2>, PMCID PMC10052322.
