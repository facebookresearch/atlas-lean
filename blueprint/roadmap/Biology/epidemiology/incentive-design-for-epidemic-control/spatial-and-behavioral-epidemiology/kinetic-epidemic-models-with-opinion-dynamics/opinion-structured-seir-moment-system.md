# Opinion-structured SEIR kinetic model and its closed macroscopic limit

This page covers Sections 2 and 3.1 of Zanella (2023): an SEIR epidemic in which each agent carries an opinion $w \in [-1, 1]$ about protective behaviour, and the moment system obtained when opinions relax fast.

**Kinetic model (eqs. (2)-(4)).** For compartments $J \in \{S, E, I, R\}$ let $f_J(w,t) \ge 0$ be the opinion density, $\rho_J = \int f_J\, dw$ the mass fraction ($\sum_J \rho_J = 1$), $M_J = \int w f_J\, dw$ the unnormalized first moment (so $|M_J| \le \rho_J$), and, when $\rho_J > 0$, $m_J = M_J/\rho_J$ the mean opinion. Then

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

$$\dot\rho_S = -\frac{\beta}{4}(\rho_S - M_S)(\rho_I - M_I), \quad \dot\rho_E = \frac{\beta}{4}(\rho_S - M_S)(\rho_I - M_I) - \sigma_E \rho_E, \quad \dot\rho_I = \sigma_E\rho_E - \gamma\rho_I, \quad \dot\rho_R = \gamma\rho_I,$$

which is not closed because the first moments appear. In the fast-opinion regime $\tau \ll 1$, each $f_J$ is near its beta equilibrium with mass $\rho_J$ and first moment $M_J$; closing the second moment of $f_S$ with

$$Z_S = \int w^2 f_S\, dw = \frac{\nu_S \rho_S^2 + 2M_S^2}{(2 + \nu_S)\rho_S} \quad (\rho_S > 0), \qquad Z_S = 0 \quad (\rho_S = 0),$$

which is continuous because $M_S^2 \le \rho_S^2$, gives the closed system for the unnormalized moments

$$\dot M_S = -\frac{\beta}{4}(\rho_I - M_I)(M_S - Z_S), \quad \dot M_E = \frac{\beta}{4}(\rho_I - M_I)(M_S - Z_S) - \sigma_E M_E, \quad \dot M_I = \sigma_E M_E - \gamma M_I, \quad \dot M_R = \gamma M_I,$$

which is defined for all nonnegative masses, including compartments of zero mass. On any time interval on which the corresponding masses are positive, the mean opinions $m_J = M_J/\rho_J$ satisfy

$$\begin{aligned}
\dot m_S &= \frac{\beta}{4} \frac{\nu_S}{2 + \nu_S}(\rho_I - M_I)(1 - m_S^2) && (\rho_S > 0), \\
\dot m_E &= \frac{\beta}{4}\frac{\rho_S(\rho_I - M_I)}{\rho_E}\Big[ m_S - \frac{\nu_S + 2m_S^2}{2 + \nu_S} - m_E(1 - m_S) \Big] && (\rho_S, \rho_E > 0), \\
\dot m_I &= \sigma_E \frac{\rho_E}{\rho_I}(m_E - m_I) && (\rho_I > 0), \\
\dot m_R &= \gamma\frac{\rho_I}{\rho_R}(m_I - m_R) && (\rho_R > 0),
\end{aligned}$$

where $\rho_I - M_I = (1 - m_I)\rho_I$ when $\rho_I > 0$; in the equation for $m_I$, $\rho_E m_E$ is read as $M_E$ when $\rho_E = 0$, and in that for $m_R$, $\rho_I m_I$ as $M_I$ when $\rho_I = 0$.

Consequences: $m_S$ is nondecreasing, because infection removes low-protection susceptibles preferentially; it is constant in the consensus limit $\nu_S \to 0^+$ (Remark 2), so the selection effect comes from opinion spread in the susceptible class.

## Depends on

- [Beta equilibrium of the Fokker-Planck opinion model](beta-equilibrium-of-opinion-fokker-planck.md)
- [The SEIR vector field](../../../seir-epidemic-model/seir-field.md)

## Expansion

For $\alpha = 1$, $\int (1 - w_*) f_I(w_*)\, dw_* = \rho_I - M_I$, so $K = \tfrac{\beta}{4}(1-w)(\rho_I - M_I) f_S$; integrating once more gives the $(\rho_S - M_S)(\rho_I - M_I)$ incidence, and $Q_J$ drops out because it conserves mass. Multiplying by $w$ and integrating gives $\dot M_S = -\tfrac{\beta}{4}(\rho_I - M_I) \int w(1 - w) f_S\, dw$, which involves the second moment; the other first moments follow the same way, since $Q_J$ also conserves the first moment. Inserting the beta-equilibrium value $\rho_S(\nu_S + 2m_S^2)/(2 + \nu_S)$ for $\int w^2 f_S$ gives $Z_S$. Where $\rho_S > 0$, $\rho_S \dot m_S = \dot M_S - m_S\dot\rho_S = \tfrac{\beta}{4}(\rho_I - M_I)\rho_S\big[\tfrac{\nu_S + 2m_S^2}{2 + \nu_S} - m_S^2\big]$, and the bracket equals $\nu_S(1 - m_S^2)/(2 + \nu_S)$; the quotient rule $\rho_J \dot m_J = \dot M_J - m_J \dot\rho_J$ gives the others where $\rho_J > 0$. The closure is formal; the source checks it against simulations of the kinetic model (Section 4).

## Sources

- M. Zanella, Kinetic models for epidemic dynamics in the presence of opinion polarization, *Bull. Math. Biol.* 85 (2023), <https://doi.org/10.1007/s11538-023-01147-2>, PMCID PMC10052322. Sections 2 and 3.1: kinetic model (2)-(4), first-moment balances and macroscopic system (15)-(17), Remarks 2-3.
