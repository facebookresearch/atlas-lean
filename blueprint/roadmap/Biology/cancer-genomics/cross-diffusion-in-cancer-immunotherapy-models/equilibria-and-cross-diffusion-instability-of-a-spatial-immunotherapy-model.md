# Equilibria and cross-diffusion instability of a spatial Kirschner–Panetta immunotherapy model

**Model.** On the unit square with no-flux boundary conditions, let $u$, $v$, $w$ be the nondimensional densities of effector cells, tumor cells and IL-2, and $\mathbf U = (u,v,w)$:

$$\partial_t\mathbf U = \mathbf F(\mathbf U) + \mathcal D\,\Delta\mathbf U, \qquad \mathbf F(\mathbf U) = \begin{pmatrix}cv - \mu_1u + \dfrac{p_1uw}{g_1 + w} + s_1\\[1ex] r_2v(1 - bv) - \dfrac{p_2uv}{g_2 + v}\\[1ex] \dfrac{p_3uv}{g_3 + v} - \mu_3w + s_3\end{pmatrix}, \qquad \mathcal D = \begin{pmatrix}d_{11} & 0 & 0\\ 0 & d_{22} & 0\\ 0 & d_{32} & d_{33}\end{pmatrix}.$$

Here $c$ is tumor antigenicity, $p_1$ IL-2-stimulated effector proliferation, $p_2$ tumor killing by effectors, $p_3$ IL-2 production, $r_2$ and $1/b$ tumor growth rate and carrying capacity, $\mu_1,\mu_3$ decay rates, $g_i$ half-saturation constants, and $s_1, s_3\ge0$ the effector-cell and IL-2 infusions of adoptive cellular immunotherapy ($s_1 = s_3 = 0$ for untreated patients). The off-diagonal entry $d_{32}$ is cross-diffusion of IL-2 driven by tumor gradients.

**Theorem.**

1. (Cancer-free equilibrium.) A positive constant steady state with $v = 0$ exists iff $p_1s_3 - s_3\mu_1 - g_1\mu_1\mu_3 < 0$, and then

$$u_1^\ast = -\frac{s_1(s_3 + g_1\mu_3)}{p_1s_3 - s_3\mu_1 - g_1\mu_1\mu_3}, \qquad w_1^\ast = \frac{s_3}{\mu_3}.$$

It is locally asymptotically stable for the kinetics iff $u_1^\ast > r_2g_2/p_2$: the Jacobian eigenvalues are $-\mu_3$, $\frac{p_1s_3 - s_3\mu_1 - g_1\mu_1\mu_3}{s_3 + g_1\mu_3} < 0$ and $r_2 - \frac{p_2}{g_2}u_1^\ast$, the last being the invasion rate of a small tumor. In particular a cancer-free state requires treatment ($s_1 > 0$).
2. (Cancer-coexistence equilibrium.) A positive steady state with $v = v_2^\ast > 0$ exists iff $v_2^\ast < 1/b$ is a root of an explicit quintic, with

$$u_2^\ast = \frac{r_2(g_2 + v_2^\ast)(1 - bv_2^\ast)}{p_2}, \qquad w_2^\ast = \frac{s_3p_2(g_3 + v_2^\ast) + p_3r_2v_2^\ast(g_2 + v_2^\ast)(1 - bv_2^\ast)}{p_2(g_3 + v_2^\ast)\mu_3}.$$

3. (Diffusion-driven instability.) A kinetically stable constant equilibrium $\mathbf U^\ast$ becomes unstable to spatial modes $e^{\lambda t + i\mathbf k\cdot\mathbf x}$ iff for some wave number the matrix $\mathcal J(\mathbf U^\ast) - |\mathbf k|^2\mathcal D$ has an eigenvalue with positive real part. Writing its characteristic polynomial as $-\lambda^3 + a_2(k)\lambda^2 + a_1(k)\lambda + a_0(k, d_{32})$, when $a_2, a_1 < 0$ (as at the coexistence equilibria for the calibrated parameters, with and without therapy) a Turing instability occurs as soon as $a_0(k, d_{32}) > 0$ for some $k$; $a_0$ is quadratic in $k^2$ with a term linear in $d_{32}k^2$, so the cross-diffusion coefficient controls the onset of patterns.

## Depends on

- [Turing instability with cross-diffusion](../../pattern-formation/turing-instability-with-cross-diffusion/README.md)

## Expansion

Setting $v = 0$ decouples the IL-2 equation ($w = s_3/\mu_3$) and leaves a linear equation for $u$, whose positivity condition is the sign condition in item 1; at this point the tumor direction decouples in the linearization, giving the three eigenvalues explicitly. Setting the tumor equation to zero with $v > 0$ gives $u$ as a function of $v$, then $w$ from the IL-2 equation, and substituting into the effector equation gives a polynomial of degree five in $v$. For the spatial problem, Neumann conditions make the Laplacian eigenmodes Fourier modes, and each mode evolves by $\mathcal J - |\mathbf k|^2\mathcal D$; by the Routh–Hurwitz criterion, a positive constant term $a_0 > 0$ forces a real positive root of the characteristic cubic, so it suffices for instability of that mode, and because $\mathcal D$ is lower triangular the cross-diffusion term $d_{32}$ enters $a_0$ only through the product $d_{32}k^2$ with a kinetic coefficient.

## Sources

- C. F. Munafò, S. Bonfiglio, P. Rogolino, "Turing pattern induced by cross-diffusion in cancer immunotherapy model", arXiv (2025). Section 2 (model, Theorems 1, 2 and 4), Section 3 (diffusion-driven instability for untreated and treated patients). <https://doi.org/10.48550/arXiv.2512.00599>
