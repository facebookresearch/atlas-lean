# Beer–Lambert law

For a collimated monochromatic beam through a homogeneous isotropic medium, the absorbance is proportional to the path length and to the concentration of the absorbing species, and the transmitted radiant power falls geometrically with both.

Let a collimated monochromatic beam of wavelength $\lambda$ pass through a homogeneous isotropic sample of path length $l \ge 0$ containing an absorbing species of amount concentration $c \ge 0$, and let the incident and transmitted spectral radiant powers $P^{0}_{\lambda}, P_{\lambda}$ be positive. The decadic absorbance is

$$
A(\lambda) = \lg \frac{P^{0}_{\lambda}}{P_{\lambda}} ,
$$

and the model asserts

$$
A(\lambda) = \varepsilon(\lambda)\, c\, l ,
\qquad\text{equivalently}\qquad
P_{\lambda} = P^{0}_{\lambda}\, 10^{-\varepsilon(\lambda) c l} ,
$$

with $\varepsilon(\lambda)$ the molar decadic absorption coefficient, of coherent unit $\mathrm{m^{2}\,mol^{-1}}$ and commonly reported in $\mathrm{dm^{3}\,mol^{-1}\,cm^{-1}}$, where $1\,\mathrm{dm^{3}\,mol^{-1}\,cm^{-1}} = 0.1\,\mathrm{m^{2}\,mol^{-1}}$. With natural logarithms the napierian absorbance $A_{\mathrm{e}} = \ln(P^{0}_{\lambda}/P_{\lambda}) = A \ln 10$ and the napierian coefficient replace them.

This is a stipulated model with explicit conditions, not a universal law. Beyond proportionality it assumes the conditions of the Lambert law, which states that the absorbed fraction is independent of the incident spectral radiant power and holds only when that power is small and when scattering, multiphoton processes, excited-state populations and photochemical reactions are all negligible. It further assumes that the species shows no concentration-dependent or pressure-dependent aggregation, and that the bandwidth of the measuring radiation is narrow compared with the spectral linewidths, which is why spectral radiant power is used. Those hypotheses matter wherever transmitted power that is not accounted for is treated as absorbed. Absorbance is dimensionless and adds over absorbing species whose absorption coefficients are independent of one another; the endpoints are immediate, $c = 0$ or $l = 0$ giving $A = 0$ and $P_{\lambda} = P^{0}_{\lambda}$, and $P_{\lambda} > 0$ for every finite $A$.

## Depends on

- [Molarity of a solution](../../solutions-and-aqueous-equilibria/concentration-units-of-solutions/molarity.md)

## Proof depends on

None.

## Expansion

A formal development introduces absorbance as $\lg(P^{0}/P)$ for positive radiant powers, states $A = \varepsilon c l$ as the model hypothesis under the conditions listed, and derives the exponential transmission form, the additivity $A = \sum_i \varepsilon_i c_i l$ for independent species, and the conversion $\varepsilon_{\mathrm{e}} = \varepsilon \ln 10$ between decadic and napierian coefficients. The Lambert-law conditions stay hypotheses; a page stating them in their own right is the natural prerequisite to add.

## Context

Undergraduate foundation of molecular spectroscopy and of optical read-out in an automated laboratory: concentrations, quantum yields and emission spectra in this chapter are measured against it.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “Beer–Lambert law (or Beer–Lambert–Bouguer law)”, p. 307, with its notes on validity and spectral bandwidth, and the entry “Lambert law”, p. 361, whose note lists the conditions it refers to.
- International Union of Pure and Applied Chemistry, *Beer–Lambert law*, IUPAC Compendium of Chemical Terminology (the Gold Book), entry B00626. <https://goldbook.iupac.org/terms/view/B00626>
