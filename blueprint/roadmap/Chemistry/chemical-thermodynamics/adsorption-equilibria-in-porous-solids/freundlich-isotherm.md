# Freundlich isotherm

The Freundlich isotherm is the empirical power law $q_e = K_F\,C_e^{1/n}$ for equilibrium uptake on heterogeneous adsorbents.

For an equilibrium solute concentration $C_e \ge 0$ the Freundlich equilibrium capacity is

$$
q_e = K_F\, C_e^{1/n},
$$

with Freundlich constant $K_F > 0$ (units fixed by those of $q_e$ and $C_e$) and exponent $n > 0$; values $1/n < 1$
are read as favourable adsorption. The law has no saturation capacity: $q_e \to \infty$ as $C_e \to \infty$. For
$n > 1$ its slope at $C_e = 0^+$ is infinite, so it does not reduce to Henry's law at low concentration.

## Context

Undergraduate level. Freundlich fits accompany Langmuir fits in most liquid-phase uptake studies of metal–organic frameworks, where a better Freundlich fit at high concentration is read as site heterogeneity.

## Depends on

None.

## Proof depends on

None.

## Expansion

The law is a fitting model, not derived from a site model; the limiting statements follow from the power function.

## Sources

- W. Somda, F. O. Konate, K. R. Koffi, G. Y. Sanou, R. Lingane et al., "Sustainable Au (III) adsorption using greenly Fe-BTC/PpPDA synthesized composite", *Royal Society Open Science* (2026), [doi.org](https://doi.org/10.1098/rsos.251604), Eqn (2.5) and Table 2.
- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/), FAQ on the Freundlich isotherm and Henry's law.
