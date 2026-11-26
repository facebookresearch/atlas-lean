# Beltrami coefficient constraint for topological smoothing

Let the cortical surface patch be conformally parametrized by a planar domain with complex coordinate $u=u^{(1)}+iu^{(2)}$, and let $f=f^{(1)}+if^{(2)}$ be the 2D retinotopic map assigning visual-field coordinates to cortical points. Its **Beltrami coefficient** is

$$\mu_f=\frac{\partial f/\partial\bar u}{\partial f/\partial u}=\frac{\partial_{u^{(1)}}f+i\,\partial_{u^{(2)}}f}{\partial_{u^{(1)}}f-i\,\partial_{u^{(2)}}f}.$$

Since the Jacobian determinant is $J_f=|\partial_uf|^2\bigl(1-|\mu_f|^2\bigr)$, $f$ is an orientation-preserving local homeomorphism (a quasiconformal map) where $|\mu_f|<1$, conformal where $\mu_f=0$, and orientation-reversing (topology violated) where $|\mu_f|>1$. For a piecewise-linear map on a triangulated mesh, $\mu_f$ is constant on each triangle, and $|\mu_f|>1$ on a triangle exactly when its image is flipped (a vertex image crosses the opposite edge).

**Topological smoothing.** Given noisy measured visual coordinates $v$ with confidence weights $w$, the smoothed map solves

$$\hat f=\arg\min_{f}\int w\,|f-v|^2+s\,|\nabla f|^2\,ds\qquad\text{subject to}\qquad\|\mu_f\|_\infty<1,$$

with $s>0$ weighting smoothness; the constraint guarantees that the fitted map is topology-preserving on every triangle.

## Expansion

Writing $\partial_u=\tfrac12(\partial_{u^{(1)}}-i\partial_{u^{(2)}})$ and $\partial_{\bar u}=\tfrac12(\partial_{u^{(1)}}+i\partial_{u^{(2)}})$, the Jacobian of $f$ as a map of $\mathbb R^2$ is $|\partial_uf|^2-|\partial_{\bar u}f|^2$, which gives the sign criterion. On a triangle mapped affinely, $|\mu|=0$ when the image triangle is similar to the source, $0<|\mu|<1$ when it is distorted but keeps its orientation, and $|\mu|>1$ when it is flipped. The paper solves the constrained problem iteratively: compute $\mu$, replace it by $\mu'=\mu/(|\mu|+\epsilon)$ wherever $|\mu|>1$ (topological projection), reconstruct the map from $\mu'$ by a linear Beltrami solver with fixed boundary values (a Beltrami coefficient determines the map up to normalization), apply Laplacian smoothing, and repeat until $\max|\mu|<1$; it is applied to V1–V3 of the Human Connectome Project retinotopy data.

## Sources

- Y. Tu, D. Ta, Z.-L. Lu, Y. Wang, "Topology-preserving smoothing of retinotopic maps", PLOS Computational Biology 17(8) (2021) e1009216, <https://doi.org/10.1371/journal.pcbi.1009216>, PMCID PMC8360528. Eqs. (4)–(5) and the Methods section on the Beltrami coefficient.
