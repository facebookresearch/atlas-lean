# Flory–Huggins mixing free energy of a swollen network

The Flory–Huggins model gives the free energy of mixing a polymer network with $C$ solvent molecules per unit dry volume as an entropic logarithm plus an enthalpic term weighted by the interaction parameter $\chi$.

Let $v > 0$ be the volume per solvent molecule, $C > 0$ the number of solvent molecules in the gel per unit volume of dry polymer, $k$ Boltzmann's constant and $T > 0$ the absolute temperature. With molecular incompressibility $1 + vC = \det F$ for the deformation gradient $F$ from the dry state, Hong et al. take the mixing free energy per unit dry volume to be

$$W_m(C) = -\frac{kT}{v}\left[ vC \log\left(1 + \frac{1}{vC}\right) + \frac{\chi}{1 + vC} \right], \qquad C > 0,$$

with dimensionless interaction parameter $\chi$. Its derivative, the mixing part of the solvent chemical potential, is

$$\frac{\partial W_m}{\partial C} = kT\left[\log\frac{vC}{1 + vC} + \frac{1}{1 + vC} + \frac{\chi}{(1 + vC)^2}\right] = kT\left[\log(1-\phi) + \phi + \chi\phi^2\right],$$

where $\phi = 1/(1 + vC)$ is the polymer volume fraction. At fixed composition the $\chi$ term raises this chemical potential when $\chi > 0$ and lowers it when $\chi < 0$, so it disfavours or favours solvent uptake; net solvent motion is decided by the full chemical potential including the elastic and pressure terms.

## Context

Graduate polymer physics. With the network stretching energy it forms the Flory–Rehner free energy of a gel, the starting point for swelling, mesh size and solute transport in hydrogels. Hong et al. give representative values $\chi = 0$–$1.2$. The parameter is treated as concentration-independent; the Hydrogel Design notes record that it can vary with polymer concentration. In this gauge $W_m \to -kT/v$ as $C \to \infty$, and $W_m$ has the continuous extension $-\chi kT/v$ at $C = 0$, where its derivative diverges to $-\infty$.

## Depends on

None.

## Proof depends on

None.

## Expansion

A definition page; missing ingredients: a derivation from the lattice count of placements, whose ideal part reduces to the [binary entropy of mixing](../../../../Chemistry/chemical-thermodynamics/entropy-heat-engines-and-the-third-law/entropy-of-mixing-binary.md) for equal-size molecules; and a lemma that the per-gel-volume form $kT\,v^{-1}[(1-\phi)\log(1-\phi) + \chi\phi(1-\phi)]$ equals $\phi W_m$ plus a term proportional to $\phi$, i.e. a constant per fixed dry volume, which leaves the solvent chemical potential and the swelling equilibrium at fixed polymer content unchanged but can shift a polymer reference chemical potential.

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 3: molecular incompressibility Eq. (16), the decomposition Eq. (20), the mixing free energy Eq. (22) with the explanation of its entropic and enthalpic terms, the chemical potential Eq. (24), and representative values of $\chi$ in Section 5
