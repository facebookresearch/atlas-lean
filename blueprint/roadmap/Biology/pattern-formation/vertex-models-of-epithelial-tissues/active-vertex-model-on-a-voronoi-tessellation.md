# Active vertex model on a Voronoi tessellation

Let the degrees of freedom be cell centres $\mathbf r_i \in \mathbb R^2$ and unit polarity vectors
$\mathbf n_i = (\cos\theta_i, \sin\theta_i)$, $i = 1, \dots, N$. The tissue is the Voronoi
tessellation of the centres: cell $i$ is the Voronoi polygon of seed $\mathbf r_i$, and each
polygon vertex $\mathbf r_\mu$ is the circumcentre of a Delaunay triangle with corners
$\mathbf r_i, \mathbf r_j, \mathbf r_k$,

$$\mathbf r_\mu = \frac{\lambda_1 \mathbf r_i + \lambda_2 \mathbf r_j + \lambda_3 \mathbf r_k}
{\lambda_1 + \lambda_2 + \lambda_3},$$

with $\lambda_1, \lambda_2, \lambda_3$ the barycentric coordinates of the circumcentre. Through
this map the [vertex model energy](vertex-model-energy-of-an-epithelial-sheet.md)
$E_{\mathrm{VM}}$ is a function of the centres, and the mechanical force on centre $i$ is
$\mathbf F_i = -\nabla_{\mathbf r_i} E_{\mathrm{VM}}$, which involves only cell $i$ and its
Delaunay neighbours and is not a sum of pairwise forces. The active vertex model is the overdamped
system

$$\gamma\,\frac{d\mathbf r_i}{dt} = f_a\, \mathbf n_i + \mathbf F_i + \boldsymbol\nu_i(t), \qquad
\gamma_r\, \frac{d\theta_i}{dt} = \boldsymbol\tau_i \cdot \mathbf e_z + \nu_i^r(t),$$

with active force strength $f_a \ge 0$ (self-propulsion speed $v_0 = f_a/\gamma$), friction
coefficients $\gamma, \gamma_r > 0$, and independent Gaussian white noises with
$\langle \nu_{i,\alpha}(t)\nu_{j,\beta}(t')\rangle = 2D\,\delta_{ij}\delta_{\alpha\beta}\delta(t-t')$ and
$\langle \nu^r_i(t)\nu^r_j(t')\rangle = 2D_r\,\delta_{ij}\delta(t-t')$. The torque
$\boldsymbol\tau_i = -\mathbf n_i \times \nabla_{\mathbf n_i} E_{\mathrm{align}}$ comes from an
alignment energy such as polar alignment to neighbours,
$E_{\mathrm{align}} = -J_p \sum_{j \sim i} \mathbf n_i\cdot\mathbf n_j$, alignment to the cell's own
velocity, $-J_v\, \mathbf n_i \cdot \hat{\mathbf v}_i$, or alignment to the long axis of the cell
shape, $-J_s\, \mathbf n_i \cdot \mathbf p_i$, with $J_p, J_v, J_s > 0$.

## Depends on

- [Vertex model energy of an epithelial sheet](vertex-model-energy-of-an-epithelial-sheet.md)

## Expansion

Because Voronoi and Delaunay structures are dual, a smooth motion of the centres gives a smooth
change of cell shapes, and neighbour exchanges (T1 transitions) happen automatically when a
Delaunay edge flips, without ad hoc topological rules. Differentiating $E_{\mathrm{VM}}$ with respect
to a centre uses the chain rule through the Jacobian $\partial\mathbf r_\nu/\partial\mathbf r_i$ of
the circumcentre map, which is nonzero only for the triangles incident to $i$, so the force is
local. The active term drives each cell along its polarity; with polarity decorrelation time
$\tau_r = \gamma_r/(2D_r)$, the competition between activity, which fluidizes the tissue, and the
mechanical energy, which favours a jammed solid, produces a fluid–solid transition controlled by
$v_0$, $\tau_r$ and the target shape. Polar alignment between neighbours is a Vicsek-type flocking
interaction.

## Sources

- D. L. Barton, S. Henkes, C. J. Weijer, R. Sknepnek, "Active Vertex Model for cell-resolution
  description of epithelial tissue mechanics", PLoS Computational Biology 13 (2017) e1005569,
  Model, "Force on the cell centre" (Eqs. 5-7), "Cell alignment" (Eqs. 8-12) and "Equations of
  motion" (Eqs. 13-14), <https://doi.org/10.1371/journal.pcbi.1005569> (PMC5493290).
