# Multiscale model of solute diffusivity in a hydrogel

The multiscale model writes the ratio of hydrogel to free diffusivity as a weighted sum of a free-volume term and an obstruction term for passage through the mesh, with error-function weights in the ratio of void size to solute size.

Let $D_0$ be the free diffusivity of a solute of hydrodynamic radius $r_s > 0$, $\phi \in [0,1)$ the swollen polymer volume fraction, $r_f > 0$ the polymer fibre radius, $r_m > 0$ the mesh radius and $r_{FVW} > 0$ the mean radius of free-volume voids in water. The Hydrogel Design version of the model is

$$\frac{D}{D_0} = \operatorname{erf}\left(\frac{r_{FVW}}{r_s}\right)\exp\left[-\left(\frac{r_s}{r_{FVW}}\right)^{3}\frac{\phi}{1-\phi}\right] + \operatorname{erfc}\left(\frac{r_{FVW}}{r_s}\right)\exp\left[-\frac{\pi}{4}\left(\frac{r_s + r_f}{r_m}\right)^{2}\right].$$

The first exponential is a free-volume (Lustig–Peppas type) factor and the second an obstruction (Amsden type) factor. Axpe et al. introduce the error-function weighting as a model hypothesis, motivated by a Gaussian distribution of free-volume radii, so that the free-volume term carries the larger weight when $r_s$ is small compared with $r_{FVW}$ and the mesh term when $r_s \gg r_{FVW}$. A larger weight does not imply a larger contribution: the weighted terms also depend on $\phi$ and $r_m$ (for example, at $r_s = r_{FVW}$ and $\phi$ close to 1 the free-volume term is negligible).

## Context

Research level. Axpe et al. (2019) proposed the model with the mesh size $\xi$ in the obstruction term and compared it with positron-annihilation free-volume measurements and a literature meta-analysis; the formula above, with $r_m$ in place of $\xi$, is the Hydrogel Design modification following the recommendation of Richbourg et al. (2021), who did not test it experimentally. Limits are conditional: for fixed $r_m$ the formula gives $D/D_0 < 1$ even at $\phi = 0$, and, with $r_s$, $r_f$ and $r_{FVW}$ fixed and positive, $D/D_0 \to 1$ as $\phi \to 0$ together with $r_m \to \infty$. At fixed $\phi$ and $r_m$, the formal ratio limit $r_s \to 0$ also gives 1; it lies outside the continuum regime in which $D_0$ is defined. Typical inputs: $r_{FVW} \approx 0.269$ nm, $r_f \approx 0.51$ nm for PEG.

## Depends on

- [Stokes–Einstein diffusivity of a sphere](stokes-einstein-diffusivity-of-a-sphere.md)
- [Mesh radius of regular lattice networks](mesh-radius-of-regular-lattice-networks.md)

## Proof depends on

None.

## Expansion

A definition page for a semi-mechanistic interpolation. Before any theorem: pages for the Lustig–Peppas free-volume model and the Amsden obstruction model with their own assumptions; a precise statement of Axpe's weighting hypothesis (their Eqs. (5)–(6), with the distribution width), noting that a Gaussian exceedance probability would normally involve $(r_s - \bar r)/\sigma$ rather than a bare ratio; and the conditional limits above as lemmas. Agreement with data is empirical and belongs on a separate evidence page.

## Sources

- E. Axpe, D. Chan, G. S. Offeddu, Y. Chang, D. Merida, H. Lopez Hernandez and E. A. Appel, "A Multiscale Model for Solute Diffusion in Hydrogels", Macromolecules 52, 6889–6897 (2019), <https://doi.org/10.1021/acs.macromol.9b00753>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6764024/>: Model Formulation: Eq. (1) (Stokes–Einstein), Eq. (2) (mutually exclusive routes), Eq. (3) (free-volume term), Eq. (4) (obstruction term), Eqs. (5)–(6) (error-function weighting); the equation images were not machine-readable, so the explicit form is taken from the next source
- Hydrogel Design, "Mesh Transport" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/mesh-transport/>: the displayed modified multiscale diffusion formula and the parameter notes for $r_{FVW}$, $r_f$ and $D$
- N. R. Richbourg, A. Ravikumar and N. A. Peppas, "Solute Transport Dependence on 3D Geometry of Hydrogel Networks", Macromolecular Chemistry and Physics (2021), <https://doi.org/10.1002/macp.202100138>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC8389770/>: the recommendation to replace mesh size by mesh radius in the multiscale model
