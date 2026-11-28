# Mott variable-range hopping law

Mott's three-dimensional variable-range hopping law models the conductance as $G \approx G^\ast\exp[-(T_0/T)^{1/4}]$ for hopping between localized states near the Fermi level.

Consider localized electronic states in three dimensions with localization length $\xi > 0$ and a density of states
$N(0) > 0$ that is approximately constant near the Fermi energy (no Coulomb gap), at low temperature $T > 0$. In Mott's
estimate a hop over distance $R > 0$ requiring energy $W$ contributes a conductance proportional to
$\exp(-2R/\xi)\exp(-W/kT)$, with the typical available energy spacing within a sphere of radius $R$ taken as
$W = 3/(4\pi R^3N(0))$. Optimizing the hop length gives a typical hop $\bar R \propto (\xi/(N(0)kT))^{1/4}$ and the
Mott law

$$
G \approx G^\ast\exp\!\left[-\left(\frac{T_0}{T}\right)^{1/4}\right], \qquad kT_0 \sim \frac{1}{N(0)\,\xi^3},
$$

where $G^\ast$ is a conductance scale with the units of $G$ and the relation for $T_0$ holds up to a model-dependent
numerical factor. The law is a scaling model for strongly disordered systems at low temperature, not a theorem that a
given conductance must obey it.

## Context

Graduate level. Conductive MOF pellets such as Ga9(HOTP)4 have been fitted with the 3D Mott law between 100 and 290 K, and Xie et al. report Mott-type hopping below 200 K for a thin film; such fits are consistent with, but do not prove, variable-range hopping.

## Depends on

None.

## Proof depends on

None.

## Expansion

Minimizing $S(R) = 2R/\xi + 3/(4\pi R^3N(0)kT)$ over $R > 0$ gives $S'(R) = 2/\xi - 9/(4\pi N(0)kTR^4) = 0$, so
$\bar R^4 = 9\xi/(8\pi N(0)kT)$ and $S(\bar R) \propto (N(0)\xi^3kT)^{-1/4}$, the exponent $1/4$. The cited lecture
prints $4\pi$ in place of $8\pi$ in $\bar R^4$; the scaling law does not depend on that constant, and an exact
prefactor does not follow from the estimate.

## Sources

- P. A. Lee, *8.512 Theory of Solids II* (MIT OpenCourseWare, Spring 2009), Lecture 8 "Mott's Variable Range Hopping", Eqs. (5)–(9), [ocw.mit.edu](https://ocw.mit.edu/courses/8-512-theory-of-solids-ii-spring-2009/)
- G. Skorupskii, G. Chanteux, K. N. Le, I. Stassen, C. H. Hendon and M. Dincă, "Electrical conductivity through π–π stacking in a two-dimensional porous gallium catecholate metal–organic framework", *Annals of the New York Academy of Sciences* 1518, 226 (2022), [doi.org](https://doi.org/10.1111/nyas.14906), PMC10092259, the 3D Mott fit of pellet conductivity.
- L. S. Xie, G. Skorupskii and M. Dincă, "Electrically Conductive Metal–Organic Frameworks", *Chemical Reviews* 120, 8536–8580 (2020), [doi.org](https://doi.org/10.1021/acs.chemrev.9b00766), PMC7453401, Section 3.2.1.1 (thin-film transport with Mott VRH behaviour below 200 K).
