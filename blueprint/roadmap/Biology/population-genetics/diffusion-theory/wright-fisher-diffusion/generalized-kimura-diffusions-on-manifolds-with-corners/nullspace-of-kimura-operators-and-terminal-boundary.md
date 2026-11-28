# Nullspace of a generalized Kimura operator and the terminal boundary

Let $P$ be a compact manifold with corners and $L$ a [generalized Kimura diffusion](wf-holder-well-posedness-of-the-kimura-heat-equation.md) on $P$. Let $\{\Sigma_{1,j}\}_{j=1}^{N_1}$ be the hypersurface boundary faces with defining functions $\rho_j$. Call $L$ **tangent** to $\Sigma_{1,j}$ if $L\rho_j|_{\Sigma_{1,j}} = 0$ and **transverse** if $L\rho_j|_{\Sigma_{1,j}} > c$ for some $c>0$. A boundary component is **minimal** if it is an isolated point or a positive-dimensional manifold without boundary.

**Definition (terminal boundary).** $bP_{\mathrm{ter}}(L)$ consists of the minimal components to which $L$ is tangent, together with the boundary strata $\Sigma$ to which $L$ is tangent and whose restricted operator $L_\Sigma$ is transverse to every component of $b\Sigma$.

Let $\mathcal D^2_{\mathrm{WF}}(P) \subset \mathcal C^1(P)\cap\mathcal C^2(\operatorname{Int}P)$ be the functions whose scaled second derivatives $x_i\partial_{x_i}^2 f$, $x_ix_j\partial^2_{x_ix_j}f$, $x_i\partial^2_{x_iy_l}f$, $\partial^2_{y_ky_l}f$ extend continuously to the boundary in every local chart, with $x_ix_j\partial^2_{x_ix_j}f \to 0$ when $x_i$ or $x_j \to 0$ and $x_i\partial_{x_i}^2 f,\ x_i\partial^2_{x_iy_l}f \to 0$ when $x_i \to 0$.

**Theorem.** Suppose $L$ is tangent or transverse to every hypersurface face of $bP$. Then

$$\dim\ker\bigl(L:\mathcal D^2_{\mathrm{WF}}(P)\to\mathcal C^0(P)\bigr)=\dim\ker\overline{L}^{\,*}=\#\,bP_{\mathrm{ter}}(L),$$

where $\overline L$ is the $\mathcal C^0(P)$ graph closure of $L$. The nullspace of $L$ is spanned by smooth non-negative functions, and the nullspace of $\overline L^{\,*}$ by non-negative measures supported on the components of $bP_{\mathrm{ter}}(L)$.

For the neutral $N$-allele Wright–Fisher operator on the simplex (no mutation, tangent to every face) the terminal components are the $N+1$ vertices: the nullspace consists of the fixation probabilities (the barycentric coordinates), and the stationary measures are the point masses at the vertices.

## Depends on

- [Well-posedness of the heat equation for generalized Kimura diffusions](wf-holder-well-posedness-of-the-kimura-heat-equation.md)

## Expansion

The key tool is a Hopf-type maximum principle adapted to the degenerate boundary: a $\mathcal D^2_{\mathrm{WF}}$ solution of $Lu = 0$ cannot attain an interior or transverse-face extremum unless it is constant on the relevant stratum. Restricting $u$ to strata to which $L$ is tangent gives a Kimura operator on a lower-dimensional manifold with corners, and an induction on stratum dimension shows that $u$ is determined by its (arbitrary) values on the terminal components; conversely each terminal component carries a harmonic function equal to $1$ there and $0$ on the others, the probability that the diffusion is absorbed in that component. Dually, the invariant measures of the adjoint semigroup live where the process is trapped, which is exactly $bP_{\mathrm{ter}}(L)$; together with the semigroup this yields the long-time asymptotics of $e^{t\overline L}f$.

## Sources

- Charles L. Epstein, Rafe Mazzeo, "Degenerate Diffusion Operators Arising in Population Biology", Annals of Mathematics Studies 185, Princeton University Press (2013), <https://doi.org/10.23943/princeton/9780691157122.001.0001>; preprint arXiv:1110.0032, <https://doi.org/10.48550/arXiv.1110.0032>. Numbering of the arXiv version: Section 1.4 (Definition 1.4.1 and Theorem 1.4.1), Chapter 4 (maximum principles and uniqueness theorems), Chapter 13 (nullspace of the adjoint and long-time asymptotics).
