# Delta-optimal functions as eigenfunctions of the slowness operator

Let the configuration space $V \subset \mathbb{R}^d$ be a bounded domain with piecewise smooth boundary and outward unit normal $n(s)$. An ergodic trajectory $s(t)$ in $V$ has stationary joint density $p_{s,v}(s, v)$ of configuration and velocity; let $p_s(s) > 0$ be the marginal density and

$$K(s) = \int v\, v^{\top}\, p(v \mid s)\, dv$$

the matrix of second moments of the velocity given the configuration. For a function $g : V \to \mathbb{R}$ write $\langle h \rangle = \int_V h\, p_s\, ds$. The **slow feature problem** asks for $J$ functions $g_1, \dots, g_J$ minimizing the **$\Delta$-values**

$$\Delta(g_j) = \langle \dot{g}_j^2 \rangle_t = \int_V \nabla g_j^{\top} K \nabla g_j \; p_s \, ds$$

subject to $\langle g_j \rangle = 0$, $\langle g_j^2 \rangle = 1$, and $\langle g_i g_j \rangle = 0$ for $i < j$ (the time averages are replaced by configuration averages using ergodicity and $\dot g = \nabla g \cdot v$).

Define the operator

$$\mathcal{D} g = -\frac{1}{p_s}\, \nabla \cdot \big( p_s\, K \nabla g \big)$$

on sufficiently smooth functions satisfying the boundary condition $n(s)^{\top} K(s) \nabla g(s) = 0$ on $\partial V$.

**Theorem.** (i) $\mathcal{D}$ is self-adjoint and non-negative with respect to the inner product $(f, g) = \int_V f g\, p_s\, ds$ on functions obeying the boundary condition. (ii) For a normalized eigenfunction $\mathcal{D} f = \Delta f$, the $\Delta$-value of $f$ equals its eigenvalue $\Delta$. (iii) Apart from the constant eigenfunction (eigenvalue $0$), suitably normalized eigenfunctions satisfy the zero-mean, unit-variance and decorrelation constraints. (iv) The $J$ eigenfunctions with the smallest nonzero eigenvalues solve the slow feature problem in the unrestricted function space.

## Expansion

The Euler–Lagrange equation of the Lagrangian with multipliers for the constraints is $\mathcal{D} g_j = \lambda_j g_j + \text{(multiplier terms)}$, with the natural boundary condition coming from the boundary term of the integration by parts. Green's identity gives $(f, \mathcal{D} g) = \int_V \nabla f^{\top} K \nabla g\, p_s\, ds$ when the boundary flux vanishes, which is symmetric in $f, g$ and non-negative when $f = g$ because $K$ is positive semidefinite; this proves (i) and (ii). Eigenfunctions of a self-adjoint operator with distinct eigenvalues are orthogonal in $(\cdot,\cdot)$, which here is the covariance, and orthogonality to the constant gives zero mean, proving (iii). Expanding any admissible $g$ in the eigenbasis shows that the sum of $\Delta$-values of $J$ orthonormal functions is at least the sum of the $J$ smallest nonzero eigenvalues (Ky Fan / Rayleigh–Ritz), proving (iv). The operator has the form of the eigenmode operator of an inhomogeneous membrane, so the optimal slow features are oscillatory, varying slowly where the animal moves fast.

## Sources

- M. Franzius, H. Sprekeler, L. Wiskott, "Slowness and sparseness lead to place, head-direction, and spatial-view cells", PLoS Computational Biology 3(8) (2007) e166, Methods "The modified optimization problem" (Optimization problem 2) and "A differential equation for the optimal functions", Theorems 1–5, <https://doi.org/10.1371/journal.pcbi.0030166>, PMCID PMC1963505.
