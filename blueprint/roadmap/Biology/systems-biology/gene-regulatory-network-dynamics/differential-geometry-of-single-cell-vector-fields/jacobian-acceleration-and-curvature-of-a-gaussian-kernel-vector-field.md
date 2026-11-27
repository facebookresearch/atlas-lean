# Jacobian, acceleration and curvature of a Gaussian-kernel vector field

**Setting.** Let $f:\mathbb R^k \to \mathbb R^k$ be a vector field written as a finite combination of Gaussian kernels centred at control points $\tilde x_1, \dots, \tilde x_m \in \mathbb R^k$,

$$f(x) = \sum_{j=1}^{m} \Gamma(x, \tilde x_j)\, c_j, \qquad \Gamma(x, \tilde x) = \exp\bigl(-w\,\lVert x - \tilde x\rVert^2\bigr),$$

with bandwidth parameter $w > 0$ and coefficient vectors $c_j \in \mathbb R^k$ (the form produced by kernel regression of velocities in a reproducing kernel Hilbert space).

**Jacobian.** Since $\partial_x \Gamma(x, \tilde x) = -2w\,\Gamma(x, \tilde x)\,(x - \tilde x)^{\top}$,

$$J(x) = \frac{\partial f}{\partial x} = -2w \sum_{j=1}^{m} \Gamma(x, \tilde x_j)\, c_j\, (x - \tilde x_j)^{\top} = -2w\, C^{\top} K D,$$

where $C = [c_1, \dots, c_m]^{\top}$, $K = \operatorname{diag}\bigl(\Gamma(x, \tilde x_1), \dots, \Gamma(x, \tilde x_m)\bigr)$ and $D = [x - \tilde x_1, \dots, x - \tilde x_m]^{\top}$.

**Derived quantities at a point $x$** with velocity $v = f(x) \ne 0$:

- divergence $\nabla \cdot f = \operatorname{tr} J$;
- acceleration along the streamline through $x$, $a = \frac{d}{dt} f(x(t)) = J v$;
- curvature vector of that streamline,

$$\kappa = \frac{1}{\lVert v\rVert}\frac{d}{dt}\frac{v}{\lVert v\rVert} = \frac{J v\,(v \cdot v) - v\,(v \cdot J v)}{\lVert v\rVert^4};$$

- in dimension $3$, the curl $\nabla \times f$ from the antisymmetric part of $J$.

All are pointwise functions of $v$ and $J(x)$, hence define new vector or scalar fields on state space. A hyperbolic attracting fixed point has $\operatorname{tr} J < 0$ there (in general an attracting fixed point has $\operatorname{tr} J \le 0$), but negative divergence does not imply attraction.

**Back to gene space.** If $f$ is learned in coordinates $z = Q^{\top} x$ given by $k$ orthonormal principal axes $Q \in \mathbb R^{d \times k}$ of a $d$-gene space, the gene-space field $x \mapsto Q f(Q^{\top} x)$ has Jacobian $G = Q J Q^{\top}$; $G_{ij}$ approximates the sensitivity of the velocity of gene $i$ to the expression of gene $j$.

## Expansion

The Jacobian formula is the chain rule applied to each kernel term, and the matrix form collects the sum. The acceleration follows from $\dot x = v$ and $\frac{d}{dt}f(x(t)) = J\dot x$. For the curvature, differentiate the unit tangent $v/\lVert v\rVert$: $\frac{d}{dt}\frac{v}{\lVert v\rVert} = \frac{a}{\lVert v\rVert} - \frac{v\,(v\cdot a)}{\lVert v\rVert^3}$, then divide by $\lVert v\rVert$ and substitute $a = Jv$. At a hyperbolic stable fixed point all eigenvalues of $J$ have negative real part, so their sum $\operatorname{tr} J$ is negative (an eigenvalue with positive real part would make the point unstable, so a non-hyperbolic attractor still has $\operatorname{tr} J \le 0$, and $\dot x = -x^3$ shows equality occurs); a saddle with one strongly contracting and one weakly expanding direction also has negative trace, which shows the converse fails. The gene-space Jacobian is again the chain rule, $\partial_x [Q f(Q^{\top} x)] = Q J Q^{\top}$; it is only an approximation of the true gene-level Jacobian because the dynamics orthogonal to the $k$ retained axes are discarded.

## Sources

- X. Qiu, Y. Zhang, J. D. Martin-Rufino, C. Weng, S. Hosseinzadeh, D. Yang, A. N. Pogson, M. Y. Hein, K. H. J. Min, L. Wang, et al., *Mapping transcriptomic vector fields of single cells*, Cell 185 (2022), <https://doi.org/10.1016/j.cell.2021.12.045>, PMCID PMC9332140. STAR Methods, "Differential geometry analysis of the reconstructed single-cell vector field" (analytic Jacobian $J = -2wC^{\top}KD$, divergence, curl, acceleration $a = Jv$, curvature, $G = QJQ^{\top}$) and "Vector Field Reconstruction in the Reproducing Kernel Hilbert Space".
