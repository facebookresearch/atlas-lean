# Vertex model energy of an epithelial sheet

Represent an epithelium of $N$ cells as a partition of the plane into convex polygons with straight
junctions, where neighbouring cells share an edge and junctions meet at vertices
$\mathbf r_\mu \in \mathbb R^2$. Let $A_i$ and $P_i$ be the area and perimeter of cell $i$, $A_i^0$
its reference area, $K_i > 0$ its area modulus, $\Gamma_i \ge 0$ its perimeter modulus, and
$\Lambda_{\mu\nu}$ the tension of the junction of length $l_{\mu\nu}$ between vertices $\mu$ and
$\nu$. The vertex model energy is

$$E_{\mathrm{VM}} = \sum_{i=1}^{N} \frac{K_i}{2}\big(A_i - A_i^0\big)^2
+ \sum_{i=1}^{N} \frac{\Gamma_i}{2} P_i^2 + 2\sum_{\langle\mu,\nu\rangle} \Lambda_{\mu\nu}\, l_{\mu\nu},$$

where the last sum is over pairs of vertices joined by a junction. Areas and perimeters are
functions of the vertex positions, for a cell with vertices $\mathbf r_1, \dots, \mathbf r_m$ in
counter-clockwise order

$$A_i = \frac12 \sum_{\mu=1}^{m} (\mathbf r_\mu \times \mathbf r_{\mu+1})\cdot \mathbf e_z, \qquad
P_i = \sum_{\mu=1}^{m} |\mathbf r_{\mu+1} - \mathbf r_\mu|, \qquad \mathbf r_{m+1} = \mathbf r_1 .$$

If all junctions of cell $i$ have the same tension, the junction term contributes a multiple of
$P_i$, and with $\Lambda = -\tilde\Gamma P_i^0$ (and $\Gamma_i = \tilde\Gamma$) the energy equals,
up to an additive constant, the preferred-perimeter form
$\sum_i \frac{K_i}{2}(A_i - A_i^0)^2 + \sum_i \frac{\tilde\Gamma}{2}(P_i - P_i^0)^2$. In the
overdamped dynamics each vertex moves as

$$\gamma\, \frac{d\mathbf r_\mu}{dt} = -\nabla_{\mathbf r_\mu} E_{\mathrm{VM}},$$

with a single friction coefficient $\gamma > 0$.

## Expansion

The area term keeps cells near a preferred size (bulk elasticity in the plane), the perimeter
term models contractility of the cortical actomyosin ring, and the junction term models adhesion
(negative tension) or contraction (positive tension) along each cell–cell contact. Expanding
$\frac{\tilde\Gamma}{2}(P_i - P_i^0)^2 = \frac{\tilde\Gamma}{2}P_i^2 - \tilde\Gamma P_i^0 P_i + \frac{\tilde\Gamma}{2}(P_i^0)^2$ shows the equivalence with the preferred-perimeter form: the
linear term is a uniform line tension and the constant does not change forces. The area formula is
the discrete Green (shoelace) formula. Quasi-static versions minimize $E_{\mathrm{VM}}$ directly;
the overdamped equation neglects inertia, which is small at cellular scales. Cell rearrangements
require additional topology-changing (T1) moves.

## Sources

- D. L. Barton, S. Henkes, C. J. Weijer, R. Sknepnek, "Active Vertex Model for cell-resolution
  description of epithelial tissue mechanics", PLoS Computational Biology 13 (2017) e1005569,
  Introduction, "Overview of the Vertex Model" (Eqs. 1-2) and Model, "Force on the cell centre"
  (Eqs. 3-4), <https://doi.org/10.1371/journal.pcbi.1005569> (PMC5493290).
