# BET specific surface area

The BET specific surface area converts the specific BET monolayer capacity into an area per unit mass: $a_s(\mathrm{BET}) = n_{m}\,L\,\sigma_m$.

Let $n_{m,\mathrm{tot}}$ be the BET monolayer capacity of an adsorbent sample (amount of substance) and $m > 0$ its
mass, so that the specific monolayer capacity of the BET isotherm is $n_m = n_{m,\mathrm{tot}}/m$. With the Avogadro
constant $L$ and the average area $\sigma_m > 0$ occupied by one adsorbate molecule in the complete monolayer, the BET
specific surface area is

$$
a_s(\mathrm{BET}) = n_m\,L\,\sigma_m = \frac{n_{m,\mathrm{tot}}\,L\,\sigma_m}{m} .
$$

Customary values are $\sigma_m(\mathrm{N_2}) = 0.162\,\mathrm{nm}^2$ at 77 K and
$\sigma_m(\mathrm{Ar}) = 0.142\,\mathrm{nm}^2$ at 87 K. When the isotherm is of Type I (micropore filling), the result
is an apparent area, a fingerprint of the adsorbent rather than a probe-accessible area.

## Context

Undergraduate level. BET areas reported for microporous metal–organic frameworks with Type I isotherms are apparent areas in this sense.

## Depends on

- [BET isotherm](bet-isotherm.md)

## Proof depends on

None.

## Expansion

The uncertainty in $\sigma_m(\mathrm{N_2})$ (about 20% on some surfaces, because of the N2 quadrupole) propagates
linearly into $a_s$.

## Sources

- M. Thommes, K. Kaneko, A. V. Neimark, J. P. Olivier, F. Rodriguez-Reinoso, J. Rouquerol and K. S. W. Sing, "Physisorption of gases, with special reference to the evaluation of surface area and pore size distribution (IUPAC Technical Report)", *Pure and Applied Chemistry* 87, 1051–1069 (2015), [doi.org](https://doi.org/10.1515/pac-2014-1117), Section 5.1.2, Eqn (5), Section 5.2.1 and Section 5.2.2.
