# Degradation-controlled release from hydrogels

Diffusion of a payload comparable to or larger than a hydrogel's mesh can be hindered; degradation, swelling or deformation of the matrix can enable or accelerate release when diffusion alone is slow. Degradation can be hydrolytic or enzymatic and, depending on relative rates, concentrated in the bulk or at the surface.

Li and Mooney classify release heuristically by the ratio of mesh size to drug size: when $r_{mesh}/r_{drug} > 1$ release is diffusion-dominated and short (hours to about a day for millimetre gels); as the ratio approaches 1 steric hindrance slows it sharply; when it is below 1 the drug is described as physically entrapped. The scalar ratio is not a hard cutoff: Richbourg et al. note that solutes larger than the nominal mesh radius can pass dynamic, heterogeneous networks, and Cai et al. predict appreciable hopping diffusion for non-sticky particles moderately larger than the mesh. For hindered or entrapped drug, enlarging the mesh by network degradation, swelling or mechanical deformation can enable or accelerate release; drug–polymer affinity and the relative time scales also matter. Degradation can cut backbone or crosslinks by hydrolysis or by enzymes such as matrix metalloproteinases; Li and Mooney note that acidic conditions typically accelerate hydrolysis, a statement that depends on the linkage. If water or enzyme transport into the gel is fast compared with bond cleavage, degradation occurs throughout the bulk; if cleavage is faster, it concentrates at the surface, where mass loss can be fairly linear in time.

## Context

Undergraduate biomaterials exposition. Examples from the review: hydrolytically degradable PEG gels with protein release half-lives up to 17 days, and a PCL–PEG–PCL gel releasing BSA for two weeks; periodate-oxidized polysaccharide gels are cited as typically bulk-eroding with rates set by the degree of oxidation. Chemical scission and measured mass erosion are different quantities. Assigning an erosion regime to a specific formulation, including Artzi's imine-crosslinked dextran-aldehyde gels, requires residence-time, size, transport and erosion data that are not compiled here. Comparisons of size should use matched conventions: the Li–Mooney modulus length is diameter-like, the [mesh radius](../solute-transport-in-gels-and-tissue/mesh-radius-of-regular-lattice-networks.md) is a portal radius.

## Depends on

These are conceptual prerequisites, not a proof:

- [Mesh size of a swollen network](../solute-transport-in-gels-and-tissue/mesh-size-of-a-swollen-network.md)
- [Hopping diffusion of nanoparticles through polymer networks](../solute-transport-in-gels-and-tissue/hopping-diffusion-of-nanoparticles-through-polymer-networks.md)
- [Surface-erosion release from a slab, cylinder or sphere](../drug-release-kinetics/surface-erosion-release-from-slab-cylinder-and-sphere.md)

## Proof depends on

None.

## Expansion

A mathematical model needs: a crosslink cleavage law (the [integrated first-order rate law](../../../../Chemistry/chemical-kinetics/rate-laws/first-order-sol.md) as the simplest case), the resulting time-dependent swelling and mesh size, a hindered-diffusivity law evaluated on the evolving mesh, a connectivity (reverse-gelation) criterion, and the release integral. The surface-versus-bulk criterion is a comparison of reaction and transport times (a Damköhler-type number) to be stated with its assumptions; note that even ideal surface erosion gives non-linear release for shrinking spheres and cylinders.

## Sources

- J. Li and D. J. Mooney, "Designing hydrogels for controlled drug delivery", Nature Reviews Materials 1, 16071 (2016), <https://doi.org/10.1038/natrevmats.2016.71>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC5898614/>: section "Mesh size controls diffusion and release" and Figure 3 (three regimes; release by degradation, swelling or deformation), and the degradation subsection (hydrolysis and enzymes, acid acceleration, bulk versus surface erosion, "fairly linear" mass loss, examples)
- N. R. Richbourg, A. Ravikumar and N. A. Peppas, "Solute Transport Dependence on 3D Geometry of Hydrogel Networks", Macromolecular Chemistry and Physics (2021), <https://doi.org/10.1002/macp.202100138>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC8389770/>: discussion after Figure 4: solutes larger than the structurally estimated mesh can pass through networks
- L.-H. Cai, S. Panyukov and M. Rubinstein, "Hopping Diffusion of Nanoparticles in Polymer Matrices", Macromolecules 48, 847–862 (2015), <https://doi.org/10.1021/ma501608x>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC4325603/>: abstract: appreciable hopping diffusion for particles moderately larger than the mesh
