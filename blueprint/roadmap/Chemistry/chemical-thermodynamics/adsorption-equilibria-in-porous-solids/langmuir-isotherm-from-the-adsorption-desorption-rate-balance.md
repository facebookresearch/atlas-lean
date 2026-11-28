# Langmuir isotherm from the adsorption–desorption rate balance

If molecular adsorption is first order in vacant sites and in pressure, and desorption first order in occupied sites, equal rates force the Langmuir coverage.

Let reversible molecular adsorption $S_- + M_{(g)} \rightleftharpoons S\!-\!M$ have adsorption rate
$R_{ads} = k_a P (1-\theta)$ and desorption rate $R_{des} = k_d\,\theta$ with constants $k_a, k_d > 0$ at the given
temperature, pressure $P \ge 0$ and fractional coverage $\theta \in [0,1]$. Then $R_{ads} = R_{des}$ holds for exactly
one $\theta \in [0,1]$, namely

$$
\theta = \frac{bP}{1+bP}, \qquad b = \frac{k_a}{k_d}.
$$

Equivalently $P(1-\theta)/\theta = 1/b$ for $P > 0$. At $P = 0$ the only balanced coverage is $\theta = 0$.

## Context

Undergraduate level. This is the kinetic derivation of the Langmuir isotherm taught in physical and surface chemistry.

## Depends on

- [Langmuir isotherm](langmuir-isotherm.md)

## Proof depends on

None.

## Expansion

The balance $k_a P(1-\theta) = k_d\theta$ is linear in $\theta$: $\theta(k_aP + k_d) = k_aP$, and
$k_aP + k_d > 0$, so $\theta = k_aP/(k_aP+k_d)$, which lies in $[0,1)$. Dividing numerator and denominator by
$k_d$ gives the stated form. The cited source writes the rates with Hertz–Knudsen and Arrhenius prefactors absorbed into
$C(T)$; only the coverage dependence $f(\theta) = c(1-\theta)$, $f'(\theta) = c'\theta$ is used, and no temperature
dependence of $b$ is asserted here.

## Sources

- R. Nix, *Surface Science*, LibreTexts Chemistry (Queen Mary, University of London), Section 3.3, "Langmuir Isotherm from a Kinetics Consideration", Assumptions 1 and 2 and the displayed equations $P(1-\theta)/\theta = B(T)$ and $\theta = bP/(1+bP)$, [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Surface_Science_%28Nix%29/03:_The_Langmuir_Isotherm/3.03:_Langmuir_Isotherm_from_a_Kinetics_Consideration).
