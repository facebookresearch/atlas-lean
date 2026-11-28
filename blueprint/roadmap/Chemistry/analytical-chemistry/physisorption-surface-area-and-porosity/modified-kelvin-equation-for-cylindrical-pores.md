# Modified Kelvin equation for cylindrical pores

The modified Kelvin equation estimates the relative pressure of pore condensation in a fully wetted cylindrical pore from its radius minus the pre-adsorbed film thickness.

For a cylindrical pore of radius $r_p$ whose walls carry an adsorbed multilayer film of thickness $t_c$ with
$0 \le t_c < r_p$, and a completely wetting condensate (hemispherical-equivalent meniscus), the modified Kelvin
equation estimates the relative pressure $p/p^\circ$ of pore condensation by

$$
\ln\frac{p}{p^\circ} = -\frac{2\gamma V_m}{RT\,(r_p - t_c)},
$$

where $\gamma > 0$ is the surface tension, $V_m > 0$ the molar volume of the bulk liquid, $p^\circ > 0$ its saturation
pressure and $T > 0$ the temperature. Hence $0 < p/p^\circ < 1$, and with the fluid parameters fixed the condensation
pressure increases with the effective radius $r_p - t_c$ (not with $r_p$ when $t_c$ also changes). When $t_c$ is taken
from a thickness curve that itself depends on $p/p^\circ$, the relation is implicit in the pressure. The equation is a
macroscopic estimator: for narrow mesopores (below about 10 nm) Kelvin-based procedures such as BJH were observed to
underestimate the pore size by about 20–30%.

## Context

Graduate level. Kelvin-type analysis underlies the classical mesopore size distributions of porous solids, including mesoporous frameworks used for water capture.

## Depends on

None.

## Proof depends on

None.

## Expansion

The bounds follow from the negative right side; the monotonicity is that of $-c/x$ in $x = r_p - t_c > 0$.

## Sources

- M. Thommes, K. Kaneko, A. V. Neimark, J. P. Olivier, F. Rodriguez-Reinoso, J. Rouquerol and K. S. W. Sing, "Physisorption of gases, with special reference to the evaluation of surface area and pore size distribution (IUPAC Technical Report)", *Pure and Applied Chemistry* 87, 1051–1069 (2015), [doi.org](https://doi.org/10.1515/pac-2014-1117), Section 7.2, Eqn (7).
