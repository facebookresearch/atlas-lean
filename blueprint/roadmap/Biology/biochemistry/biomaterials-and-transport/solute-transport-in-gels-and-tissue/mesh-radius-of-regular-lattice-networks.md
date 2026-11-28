# Mesh radius of regular lattice networks

For zero-thickness straight chains of length $\xi$ on the ideal lattices of junction functionality $f = 4, 6, 8$, the inscribed radius of the specified projected mesh portal is $r_m = \tfrac{\sqrt6}{3}\xi$, $\tfrac12\xi$ and $\tfrac{\sqrt2}{4}\xi$ respectively.

Model a network as rigid, zero-thickness straight chains of length $\xi > 0$ joined at junctions arranged on ideal lattices built from regular tetrahedra ($f = 4$, adjacent cells in chair-like orientation), cubes ($f = 6$) or octahedra ($f = 8$). For each lattice take the portal whose plane contains the midpoints of its chains, flatten the chains into that plane by the cosine of their angle to it (passage at the ideal normal angle), and let $r_m$ be the radius of the circle inscribed in the resulting polygon. The portals are a regular hexagon of edge $\tfrac{2\sqrt2}{3}\xi$, a square of edge $\xi$ and a square of edge $\tfrac{\sqrt2}{2}\xi$, so

$$r_{m,4} = \frac{\sqrt6}{3}\,\xi \approx 0.82\,\xi, \qquad r_{m,6} = \frac12\,\xi, \qquad r_{m,8} = \frac{\sqrt2}{4}\,\xi \approx 0.35\,\xi .$$

The portals for $f = 4$ and $f = 8$ also have nonzero depth normal to the plane ($\tfrac13\xi$ and $\tfrac{\sqrt2}{2}\xi$), which the inradius ignores.

## Context

Graduate. Richbourg, Ravikumar and Peppas propose replacing the mesh size by this mesh radius in models of solute diffusivity, so that higher junction functionality, which slightly increases $\xi$ at fixed composition, would restrict transport more. The result is a statement about the specified projected portals only; it is not a maximum over passage directions or paths, it ignores chain thickness and flexibility, and the authors stress that solutes larger than $r_m$ can still pass dynamic, heterogeneous networks.

## Depends on

- [Mesh size of a swollen network](mesh-size-of-a-swollen-network.md)

## Proof depends on

None.

## Expansion

Proof: elementary geometry. From the lattice angles compute the in-plane edge lengths (tetrahedral face–edge–face angle for $f = 4$, no tilt for $f = 6$, a 45° tilt for $f = 8$), then the inradius of a regular hexagon of edge $a$ ($\tfrac{\sqrt3}{2}a$) and of a square of edge $a$ ($a/2$). Checks: $\tfrac{\sqrt3}{2}\cdot\tfrac{2\sqrt2}{3}\xi = \tfrac{\sqrt6}{3}\xi$ and $\tfrac12\cdot\tfrac{\sqrt2}{2}\xi = \tfrac{\sqrt2}{4}\xi$. Whether these portals are maximal among planar sections, and passage for finite-thickness fibres, are separate questions.

## Sources

- N. R. Richbourg, A. Ravikumar and N. A. Peppas, "Solute Transport Dependence on 3D Geometry of Hydrogel Networks", Macromolecular Chemistry and Physics (2021), <https://doi.org/10.1002/macp.202100138>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC8389770/>: section "Mesh Radius and Solute Diffusion in a Network", Figure 4 caption and text (portal shapes, in-plane reductions, plane-normalized depths and the three mesh radii)
- N. R. Richbourg, A. Ravikumar and N. A. Peppas, Supplementary Materials for "Solute Transport Dependence on 3D Geometry of Hydrogel Networks" (public supplement), <https://hydrogeldesign.org/wp-content/uploads/2023/08/NR-Geom-SI.pdf>: pp. 1–2: choice of portal plane through chain midpoints, flattening at the ideal normal angle, in-plane mesh sizes and depths, inscribed-circle calculation
- Hydrogel Design, "Mesh Transport" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/mesh-transport/>: the case formula for $r_m$ at $f = 4, 6, 8$
