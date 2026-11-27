# Saturated incidence from fixed infected opinion in the opinion-structured SEIR model

This page covers Section 3.2 of Zanella (2023). Notation is as on [the opinion-structured SEIR kinetic model](opinion-structured-seir-moment-system.md), with $\alpha = 1$.

**Assumption.** Infected agents keep a fixed mean opinion $m_I(t) \equiv \bar m_I \in (0,1)$ (situational awareness).

**Mean susceptible opinion (eq. (18)).** Assume $\rho_S(0) > 0$, so that $\rho_S > 0$ for all $t$ and $m_S$ is defined. The closed equation $\dot m_S = J(\rho_I)(1 - m_S^2)$ with $J(\rho_I) = \tfrac{\beta}{4}\tfrac{\nu_S}{2 + \nu_S}(1 - \bar m_I)\rho_I \ge 0$ has two kinds of solutions.

- *Endpoint data.* If $m_S^0 = \pm 1$, then $m_S \equiv m_S^0$.
- *Interior data.* If $m_S^0 \in (-1, 1)$, then

$$m_S(t) = \tanh\Big( \operatorname{artanh} m_S^0 + \int_0^t J(\rho_I(s))\, ds \Big) = \frac{e^{2\int_0^t J} - e^{C_0}}{e^{2\int_0^t J} + e^{C_0}}, \qquad C_0 = \log\frac{1 - m_S^0}{1 + m_S^0},$$

so $m_S(t) \in (-1, 1)$ for all $t$, and $m_S$ is nondecreasing.

**Reduced SEIR (eq. (19)).** Substituting into the mass equations gives

$$\dot\rho_S = -\bar\beta H(t)\rho_S\rho_I, \quad \dot\rho_E = \bar\beta H(t)\rho_S\rho_I - \sigma_E\rho_E, \quad \dot\rho_I = \sigma_E\rho_E - \gamma\rho_I, \quad \dot\rho_R = \gamma\rho_I,$$

with $\bar\beta = \tfrac{\beta}{4}(1 - \bar m_I)$ and $H(t) = 1 - m_S(t)$. For endpoint data $H \equiv 0$ (if $m_S^0 = 1$) or $H \equiv 2$ (if $m_S^0 = -1$). For interior data

$$H(t) = \frac{2e^{C_0}}{e^{2\int_0^t J} + e^{C_0}} \in (0, 2).$$

$H$ is nonincreasing; for interior data it decreases faster the more infection has occurred, because $\int_0^t J$ grows with the accumulated prevalence $\int_0^t \rho_I$. The incidence thus saturates with the epidemic's own history, a memory analogue of saturated incidence rates (Capasso and Serio 1978).

**Initial growth.** Near the disease-free state at $t = 0$ ($\rho_S \approx 1$, $\rho_I \approx 0$) the per-capita incidence is $\bar\beta(1 - m_S^0)$, so the linearised infected subsystem has reproduction number

$$R_0 = \frac{\beta(1 - \bar m_I)(1 - m_S^0)}{4\gamma}.$$

The source reports $R_0 = \beta(1 - \bar m_I)/(4\gamma)$, which is this value for an initially neutral susceptible population, $m_S^0 = 0$ (where $H(0) = 1$).

## Depends on

- [Opinion-structured SEIR kinetic model and its closed macroscopic limit](opinion-structured-seir-moment-system.md)
- [Basic reproduction number of the next-generation matrix](../../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [For $\beta \ge 0$ and $\sigma, \gamma > 0$, the SEIR $R_0 = \rho(FV^{-1})$ equals $\beta/\gamma$](../../../seir-epidemic-model/r0-eq.md)

## Expansion

With $\bar m_I$ fixed, the $m_S$ equation decouples from the other means and is a Riccati equation $\dot m = J(1 - m^2)$. The constants $\pm 1$ are solutions, and by uniqueness no other solution reaches them in finite time; for interior data it is separable in the variable $\operatorname{artanh} m$, which increases at rate $J$. Then $1 - \tanh(x) = 2/(1 + e^{2x})$ gives $H$. For the reproduction number, the SEIR next-generation computation with transmission coefficient $\bar\beta H(0)$ gives $\bar\beta H(0)/\gamma$, the latent stage not affecting $R_0$ since every exposed agent becomes infectious.

## Sources

- M. Zanella, Kinetic models for epidemic dynamics in the presence of opinion polarization, *Bull. Math. Biol.* 85 (2023), Section 3.2 (eqs. (18)-(19); the endpoint data are treated separately before (18)), <https://doi.org/10.1007/s11538-023-01147-2>, PMCID PMC10052322.
- V. Capasso and G. Serio, A generalization of the Kermack-McKendrick deterministic epidemic model, *Math. Biosci.* 42 (1978), 43-61, <https://doi.org/10.1016/0025-5564(78)90006-8>.
