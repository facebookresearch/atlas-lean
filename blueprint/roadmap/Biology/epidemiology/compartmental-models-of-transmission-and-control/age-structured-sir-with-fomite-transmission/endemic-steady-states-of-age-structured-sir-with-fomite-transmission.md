# Endemic steady states of age-structured SIR with fomite transmission

**Model.** In a stationary population with age density $U(a)$ on $(0, a_m)$ (net reproduction rate one), let $\overline{S}, \overline{I}, \overline{R}$ be the age-specific proportions susceptible, infected and recovered. Infection arrives by direct contact, with age-dependent transmission kernel $r(a,b) \in L^\infty$, and by indirect contact with contaminated surfaces (fomites) at age-specific rate $c(a) \ge 0$; $b(a)$ is the recovery rate. The steady states solve

$$\frac{d\overline{S}}{da} = -(\lambda(a) + c(a))\overline{S}, \qquad \frac{d\overline{I}}{da} = (\lambda(a) + c(a))\overline{S} - b(a)\overline{I}, \qquad \overline{S}(0) = 1,\ \overline{I}(0) = 0,$$

with force of infection $\lambda(a) = \int_0^{a_m} r(a,\eta)U(\eta)\overline{I}(\eta)\,d\eta$. Eliminating $\overline{S}, \overline{I}$ turns this into the fixed-point equation $\lambda = \Phi(\lambda)$ on the positive cone of $L^1(0,a_m)$,

$$\Phi(\psi)(a) = \int_0^{a_m}\phi(a,\sigma)\big(\psi(\sigma) + c(\sigma)\big)e^{-\int_0^\sigma(\psi + c)}\,d\sigma, \qquad \phi(a,\sigma) = \int_\sigma^{a_m} r(a,\zeta)U(\zeta)e^{-\int_\sigma^\zeta b}\,d\zeta.$$

Assume (A1) $r$ is $L^1$-continuous under translation in its first argument; (A2) $r(a,b) \ge m > 0$ for $b$ in an interval $(a_m - \alpha, a_m)$; (A3) $c > 0$ a.e. on some interval $(a_1, a_2)$.

**Theorem (existence; no disease-free state).** Under (A1)–(A3), $\Phi$ maps a closed ball $\{\psi \in L^1_+ : \|\psi\|_1 \le M\}$ into itself and is completely continuous, so by Schauder's theorem it has a fixed point. Since $\Phi(0) = \int_0^{a_m}\phi(\cdot,\sigma)c(\sigma)e^{-\int_0^\sigma c}\,d\sigma > 0$, $\lambda = 0$ is not a fixed point: as long as fomites transmit, there is no disease-free steady state. Moreover every fixed point is positive a.e., since $\lambda(a) \ge m\int_{a_m-\alpha}^{a_m}U\overline{I}$ by (A2) and $\overline{I} > 0$ on $(a_1, a_m)$ by (A3).

## Expansion

Compactness of $\Phi$ comes from writing it as compact linear integral operators (Riesz–Fréchet–Kolmogorov) composed with continuous Nemytskii maps. The source's Theorem 4.2 on vanishing fomites ($c_n\to0$ a.e.) is not stated here: with $c_n=n\mathbf 1_{(0,1/n)}$ the fomite term $\Phi_n(0)$ stays bounded away from $0$, a term its proof of Proposition 4.7 drops, and the inequality $\rho(T_n)\ge\rho(T_0)$ of Lemma 4.9 runs the other way, since the next-generation operators $T_n$ with fomites satisfy $T_n\le T_0$ pointwise. With $T_0\psi(a)=\int_0^{a_m}\phi(a,\sigma)\psi(\sigma)\,d\sigma$ the next-generation operator without fomites, $\rho(T_0)$ plays the role of $R_0$ for direct transmission, the age-structured analogue of the [Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md).

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Sources

- Manoj Kumar, Syed Abbas, "Age structured SIR model for the spread of infectious diseases through indirect contacts", arXiv:2007.11911 (2020): Section 2 (model and normalization), Section 4 (steady-state fixed-point equation, assumptions (A1)–(A3), Theorem 4.1). <https://doi.org/10.48550/arXiv.2007.11911>
