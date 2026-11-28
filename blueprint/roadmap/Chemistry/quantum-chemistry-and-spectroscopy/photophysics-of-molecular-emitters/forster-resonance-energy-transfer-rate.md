# Förster resonance energy transfer rate

In the very weak dipole–dipole coupling limit, excitation passes from a donor to an acceptor at a rate falling off as the inverse sixth power of their separation. The distance at which transfer matches the donor's own decay is the Förster radius.

Let an excited donor with intrinsic decay rate constant $k_{\mathrm{D}} = 1/\tau^{0}_{\mathrm{D}} > 0$, the total rate at which it decays without an acceptor, be separated by $r > 0$ from an acceptor, with $r$ considerably larger than the sum of the van der Waals radii. The transfer rate constant is

$$
k_{\mathrm{T}} = \frac{1}{\tau^{0}_{\mathrm{D}}} \left(\frac{R_{0}}{r}\right)^{6} ,
$$

with the Förster radius fixed by

$$
R_{0}^{6} = \mathrm{Const} \cdot \frac{\kappa^{2}\, \Phi^{0}_{\mathrm{D}}\, J}{n^{4}} ,
\qquad
J = \int I_{\lambda}^{\mathrm{D}}(\lambda)\, \varepsilon_{\mathrm{A}}(\lambda)\, \lambda^{4}\, \mathrm{d}\lambda ,
$$

where $\Phi^{0}_{\mathrm{D}} \in [0,1]$ is the donor fluorescence quantum yield without acceptor, $n > 0$ the average refractive index over the overlap region, $I_{\lambda}^{\mathrm{D}} \ge 0$ the donor emission spectral density normalized by $\int I_{\lambda}^{\mathrm{D}} \mathrm{d}\lambda = 1$, $\varepsilon_{\mathrm{A}} \ge 0$ the acceptor's molar decadic absorption coefficient, $J \in [0,\infty)$ the resulting overlap integral and $\mathrm{Const} > 0$ a constant fixed by that normalization and by the units of $\varepsilon_{\mathrm{A}}$ and $\lambda$, for which the source gives a practical convention in nanometres. The orientation factor is

$$
\kappa = \cos\theta_{\mathrm{DA}} - 3\cos\theta_{\mathrm{D}}\cos\theta_{\mathrm{A}} ,
$$

with $\theta_{\mathrm{DA}}$ the angle between the transition dipole moments and $\theta_{\mathrm{D}}, \theta_{\mathrm{A}}$ their angles with the separation vector.

Conventions and limits. Although the source's entry says "emission rate constant", the identity with $1/\tau^{0}_{\mathrm{D}}$ and the efficiency expression use the donor's total intrinsic decay; the two differ whenever $\Phi^{0}_{\mathrm{D}} < 1$, so the notation is fixed here as the total rate. When $R_{0} > 0$, transfer and intrinsic decay are equally probable at $r = R_{0}$, a statement inside the regime where the model applies. Degenerate inputs are possible: $\kappa^{2} = 0$ or $J = 0$ give $R_{0} = 0$ and $k_{\mathrm{T}} = 0$ at every $r > 0$, and the divergence of the expression as $r \to 0$ arises only for $R_{0} > 0$ and lies outside the model, which does not extend to contact distances where exchange mechanisms act. The factor $\kappa^{2}$ ranges over $[0,4]$; it equals $1$ when the two moments are parallel to each other and perpendicular to the separation vector, and $4$ when both lie along the separation axis, which is the geometry the source names for the maximum. The value $2/3$ is the mean of $\kappa^{2}$ when the donor and acceptor orientations are *independent* and each isotropic, as dynamic averaging in fluid solution is taken to provide; it is not the value for a particular static geometry, and dependence between the orientations changes it, as locked parallel moments sharing one uniformly distributed direction show, for which $\kappa = 1 - 3u^{2}$ with $u$ uniform on $[-1,1]$ and the mean of $\kappa^{2}$ is $4/5$. A reported $R_{0}$ is therefore only as good as its orientation model. The overlap integral is written in wavelength with the factor $\lambda^{4}$ and a normalized donor spectrum, which is what ties the constant down.

## Depends on

- [Lifetime of an excited state](excited-state-lifetime.md)
- [Quantum yield of a photophysical process](quantum-yield-of-a-photophysical-process.md)
- [Beer–Lambert law](beer-lambert-law.md)

## Proof depends on

None.

## Expansion

A formal development takes $\tau^{0}_{\mathrm{D}} > 0$, $r > 0$, a nonnegative normalized donor spectral density, a nonnegative acceptor absorption coefficient with finite overlap integral, $n > 0$ and the three angles, and defines $k_{\mathrm{T}}$ and $R_{0}$ by the displays. The characterization of $R_{0}$ as the distance of equal rates solves $k_{\mathrm{T}} = k_{\mathrm{D}}$ under $R_{0} > 0$; the range $0 \le \kappa^{2} \le 4$ with its two named geometries is a trigonometric computation, and the value $2/3$ is the integral of $\kappa^{2}$ over independent isotropic orientations of the two moments. The microscopic dipole–dipole derivation is not part of this page and does not follow from the absorption law, which enters only through the definition of $\varepsilon_{\mathrm{A}}$.

## Context

Graduate. The quantitative model of excitation transfer behind light-harvesting and host–guest emitter design, and the first ingredient of any kinetic scheme in which a designed donor feeds an acceptor.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “Förster-resonance-energy transfer (FRET)”, pp. 342–343, with Notes 1–4 on the overlap integral, the practical constant, the orientation factor, its collinear and perpendicular geometries and its randomly oriented average.
