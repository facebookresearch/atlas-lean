# Ideal adsorbed solution theory

Ideal adsorbed solution theory predicts mixture loadings from pure-component isotherms by a Raoult-law analogue at equal spreading pressure, whenever its equations have a solution.

Fix one temperature and one adsorbent, with all loadings on a common basis. Let $n \ge 2$ components have
pure-component isotherms $q_i^0$ in the fugacity, with reduced spreading pressures $\Pi_i$, and let a bulk mixture
have partial fugacities $f_i > 0$. An ideal adsorbed solution theory solution consists of adsorbed-phase mole fractions
$x_i \in (0,1]$ and reference pure-component fugacities $P_i^0 > 0$, in the range where each $\Pi_i$ is defined and
$q_i^0(P_i^0) > 0$, satisfying

$$
f_i = P_i^0\,x_i, \qquad \Pi_1(P_1^0) = \Pi_2(P_2^0) = \cdots = \Pi_n(P_n^0), \qquad \sum_{i=1}^n x_i = 1;
$$

its loadings are then

$$
\frac{1}{q_t} = \sum_{i=1}^n \frac{x_i}{q_i^0(P_i^0)}, \qquad q_i = x_i\,q_t .
$$

A solution need not exist: with $q_1^0(f) = 0.2fe^{-f}$, $q_2^0(f) = fe^{-f}$ (so
$\Pi_1 = 0.2(1-e^{-f})$, $\Pi_2 = 1-e^{-f}$) and $f_2 = 1$, every common value of $\Pi$ forces $x_2 > 1$. The theory
assumes that every adsorption site is equally accessible to every component, that the adsorbed mixture is ideal, and
that each guest occupies the same area in the mixture as in its pure state (the basis of the additive inverse-loading
rule); it is expected to fail with molecular clustering, hydrogen bonding or preferential siting. Pressure replaces
fugacity for an ideal-gas bulk.

## Context

Graduate level. IAST is the default prediction of CO2/N2, CO2/CH4 and hydrocarbon selectivities in metal–organic frameworks.

## Depends on

- [Reduced spreading pressure](reduced-spreading-pressure.md)

## Proof depends on

None.

## Expansion

If each $\Pi_i$ is continuous, strictly increasing and unbounded with $\Pi_i(0^+) = 0$, the common value $\Pi$
determines each $P_i^0$, and $\sum_i f_i/P_i^0(\Pi)$ decreases strictly from $+\infty$ to $0$, so the reference
fugacities are uniquely determined. They give a solution in the sense above only if moreover $q_i^0(P_i^0) > 0$ at that
root, which holds for example when $q_i^0(f) > 0$ for every $f > 0$; without it the root can sit where a pure loading
vanishes (both components with $q^0(f) = f(f-1)^2$ and $f_i = 1/2$ force $P_i^0 = 1$). This existence and uniqueness
statement is a separate result, not part of the definition. In practice the equations are solved numerically.

## Sources

- R. Krishna and J. M. van Baten, "How Reliable Is the Ideal Adsorbed Solution Theory for the Estimation of Mixture Separation Selectivities in Microporous Crystalline Adsorbents?", *ACS Omega* 6, 15499–15513 (2021), [doi.org](https://doi.org/10.1021/acsomega.1c02136), Section 2.1, Eqns (2)–(5) and (7), and the stated conditions for applicability.
- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/), section "Theory".
