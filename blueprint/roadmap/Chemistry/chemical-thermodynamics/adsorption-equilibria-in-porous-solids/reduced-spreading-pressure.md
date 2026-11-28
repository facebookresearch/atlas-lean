# Reduced spreading pressure

The reduced spreading pressure of a pure-component isotherm is $\int_0^p q^0(f)/f\,df$, the adsorption analogue of a surface pressure.

Let $q^0(f) \ge 0$ be a pure-component isotherm, loading against bulk fugacity $f > 0$ at fixed temperature, such that
$q^0(f)/f$ is integrable on $(0, p]$. The reduced spreading pressure (surface potential) at fugacity $p$ is

$$
\Pi(p) = \frac{\pi A}{RT} = \int_0^{p} \frac{q^0(f)}{f}\,df,
$$

where $\pi$ is the spreading pressure and $A$ the surface area per unit amount of adsorbent; $\Pi$ has the units of
$q^0$. A finite limit $q^0(f)/f \to K_H$ as $f \to 0^+$ (Henry's law), together with local integrability away from
$0$, suffices for integrability; it is not necessary: $q^0(f) = \sqrt f$ gives $\Pi(p) = 2\sqrt p$. On any range where it
is defined, $\Pi$ is nondecreasing, and strictly increasing if $q^0/f$ has positive integral over every nontrivial
interval. Pressure replaces fugacity for an ideal-gas bulk.

## Context

Graduate level. Spreading pressure is the quantity equalized across components in ideal adsorbed solution theory; as practical advice, pure-component fits used for IAST should obey Henry's law at low loading.

## Depends on

None.

## Proof depends on

None.

## Expansion

The surface area $A$ is not measured directly, so the reduced form $\Pi$, with units of loading, is used. Monotonicity
follows from the nonnegative integrand.

## Sources

- R. Krishna and J. M. van Baten, "How Reliable Is the Ideal Adsorbed Solution Theory for the Estimation of Mixture Separation Selectivities in Microporous Crystalline Adsorbents?", *ACS Omega* 6, 15499–15513 (2021), [doi.org](https://doi.org/10.1021/acsomega.1c02136), Section 2.1, Eqn (4) and the definition of the surface potential.
- C. M. Simon, B. Smit and M. Haranczyk, *pyIAST documentation*, sections "Competitive Langmuir adsorption" and "ModelIsotherm" (model list and `spreading_pressure`), [pyiast.readthedocs.io](https://pyiast.readthedocs.io/en/latest/), `spreading_pressure` and the FAQ on Henry's law.
