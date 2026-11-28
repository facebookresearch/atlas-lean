# Fracture energy of a hydrogel: intrinsic and dissipative parts

The fracture energy $\Gamma$ of a hydrogel is the energy required to advance a crack by unit undeformed area; it is commonly estimated with a pure-shear test and decomposed into an intrinsic part $\Gamma_0$ and dissipative parts.

Definition. $\Gamma$ is the mechanical energy consumed per unit area of crack advance, measured in the undeformed configuration (units J/m²).

Pure-shear estimator. Take two identical samples of the gel with undeformed width $W$, height $H$ and thickness $T$, $W \gg H \gg T$, each clamped along its long edges by rigid plates. Cut a notch of length about $W/2$ into the first sample, so that both the notch and the remaining ligament are much longer than $H$, and stretch it until the crack begins to propagate at stretch $\lambda_c$; stretch the unnotched sample uniformly, at a matched loading rate, to $\lambda_c$, recording its nominal stress $s(\lambda) = F/(WT)$. Then under these test conditions

$$\Gamma = H\int_{1}^{\lambda_c} s\,d\lambda .$$

Decomposition. Zhao writes $\Gamma = \Gamma_0 + \Gamma_D$, with $\Gamma_0$ the intrinsic fracture energy (breaking the chains crossing the crack plane) and $\Gamma_D$ the energy dissipated around the crack, which can arise from hysteresis in a process zone or from pull-out of fibres and fillers in a bridging zone. The process-zone contribution is modelled as

$$\Gamma_D^{pz} = 2V\int_{0}^{h} w_D\,dy, \qquad w_D = \sum_{i=1}^{3}\oint s_i\,d\lambda_i ,$$

with $h$ the half-width of the process zone (the factor 2 counts both sides), $V$ the volume fraction of gel in it and $w_D$ the hysteresis-loop area per unit reference volume. Yuk et al. use the same split for the interfacial toughness of hydrogel–solid bonds, a different failure path from bulk fracture.

## Context

Graduate fracture mechanics of soft materials. Unlike fracture stress, $\Gamma$ measured with a dominant notch is insensitive to small defects. As rough literature benchmarks, most hydrogels have $\Gamma \sim 10$ J/m², cartilage about 1000 J/m² and natural rubber about 10,000 J/m² (Sun et al., 2012). It extends the [Griffith energy balance](../../../../Physics/elasticity-and-structures/isotropic-elastic-energy/griffith-energy-balance-for-brittle-fracture.md) to large, dissipative deformation. A zero-hysteresis bulk gel can still dissipate energy at interfaces or in bridging zones.

## Depends on

None.

## Proof depends on

None.

## Expansion

Missing: the Rivlin–Thomas argument that in pure shear the energy released per unit crack advance equals $H$ times the strain-energy density of the unnotched sample at $\lambda_c$, with its geometric and rate conditions (which justifies Eq. (1) as an estimator of $\Gamma$); the steady-state crack argument behind Eq. (5); and a model for bridging-zone dissipation. Each is a separate energy-balance statement.

## Sources

- X. Zhao, "Multi-scale multi-mechanism design of tough hydrogels: building dissipation into stretchy networks", Soft Matter 10, 672–687 (2014), <https://doi.org/10.1039/C3SM52272E>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC4040255/>: Section 2.1 (pure-shear test, Figure 2, Eq. (1); decomposition Eq. (2), Figure 3), Section 2.3 (process-zone and bridging-zone mechanisms) and Section 2.3.1 (Eqs. (5)–(6))
- H. Yuk, T. Zhang, S. Lin, G. A. Parada and X. Zhao, "Tough bonding of hydrogels to diverse non-porous surfaces", Nature Materials 15, 190–196 (2016), <https://doi.org/10.1038/nmat4463>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC4762474/>: Eq. (1) and Figure 1b (interfacial toughness as intrinsic work of adhesion plus bulk dissipation)
- J.-Y. Sun, X. Zhao, W. R. K. Illeperuma, O. Chaudhuri, K. H. Oh, D. J. Mooney, J. J. Vlassak and Z. Suo, "Highly stretchable and tough hydrogels", Nature 489, 133–136 (2012), <https://doi.org/10.1038/nature11409>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC3642868/>: introductory paragraph: fracture energies of hydrogels, cartilage and natural rubber
