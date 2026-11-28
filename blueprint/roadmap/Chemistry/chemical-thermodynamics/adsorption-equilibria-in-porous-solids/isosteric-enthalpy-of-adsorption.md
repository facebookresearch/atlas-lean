# Isosteric enthalpy of adsorption

The isosteric enthalpy of adsorption is $R$ times the slope of $\ln p$ against $1/T$ at fixed loading; two isotherms give a secant estimate of it.

Let $p(n,T) > 0$ be the equilibrium pressure, in a fixed unit, at loading $n$ and temperature $T > 0$, differentiable in
$T$. The isosteric enthalpy of adsorption at loading $n$ and temperature $T$ is

$$
\Delta H_{ads}(n,T) = R\left(\frac{\partial \ln p}{\partial (1/T)}\right)_{n},
$$

and the isosteric heat is $Q_{st}(n,T) = -\Delta H_{ads}(n,T)$. From two isotherms at $T_1 \ne T_2$ with pressures
$p_1, p_2$ at the same loading $n$, the two-point (secant) estimate is

$$
\Delta H^{\mathrm{sec}}_{ads}(n) = -R\,\ln\!\left(\frac{p_2}{p_1}\right)\frac{T_1T_2}{T_2-T_1},
$$

which equals $\Delta H_{ads}(n,T)$ for every $T$ between $T_1$ and $T_2$ when $\ln p$ is affine in $1/T$ at that
loading, and is in general only an average slope. Since adsorption at fixed loading needs a higher pressure at a higher
temperature, $\Delta H_{ads} < 0$ for exothermic physisorption. The source identifies this quantity with the
adsorption enthalpy via the Clausius–Clapeyron relation, assuming an ideal gas phase and a negligible molar volume of the
adsorbed phase; that identification is not derived here.

## Context

Graduate level. Isosteric enthalpies are the standard reported binding-strength metric for H2 and CO2 in metal–organic frameworks, including the open-metal-site frameworks studied by Dincă and Long. In practice both loadings are taken inside the measured range of the two isotherms.

## Depends on

None.

## Proof depends on

None.

## Expansion

The two-point form is the secant of $\ln p$ against $1/T$ at constant $n$; by the mean value theorem it equals the
slope at some intermediate temperature. The Clausius–Clapeyron approximations make the value differ from calorimetry at
high loading.

## Sources

- A. Nuhnen and C. Janiak, "A practical guide to calculate the isosteric heat/enthalpy of adsorption via adsorption isotherms in metal–organic frameworks, MOFs", *Dalton Transactions* 49, 10295–10307 (2020), [doi.org](https://doi.org/10.1039/d0dt01784a), Eqn (1) and the stated approximations (i) and (ii).
- L. J. Murray, M. Dincă and J. R. Long, "Hydrogen storage in metal–organic frameworks", *Chemical Society Reviews* 38, 1294–1314 (2009), [doi.org](https://doi.org/10.1039/b802256a), section "Design principles for an optimal H2 adsorbent" (isosteric heats of H2 in frameworks).
