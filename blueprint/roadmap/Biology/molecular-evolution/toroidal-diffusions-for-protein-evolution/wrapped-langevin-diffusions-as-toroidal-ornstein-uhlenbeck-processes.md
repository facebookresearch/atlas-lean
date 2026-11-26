# Wrapped Langevin diffusions as toroidal Ornstein–Uhlenbeck processes

**Setting.** Protein backbone conformations are described by dihedral angles $(\phi,\psi)\in\mathbb T^2=[-\pi,\pi)^2$. To model how these angles evolve along a phylogeny one needs ergodic, time-reversible diffusions on the torus $\mathbb T^p$ with a prescribed stationary density. For a density $f$ on $\mathbb R^p$ and diffusion matrix $V=\sigma\sigma^{\top}$, the *Langevin diffusion* has drift
$$b_i(\mathbf x)=\tfrac12\sum_jV_{ij}(\mathbf x)\,\partial_{x_j}\log f(\mathbf x)+\det V(\mathbf x)^{1/2}\sum_j\partial_{x_j}\big(V_{ij}(\mathbf x)\det V(\mathbf x)^{-1/2}\big),$$
which reduces to $d\mathbf X_t=\tfrac12\boldsymbol\Sigma\nabla\log f(\mathbf X_t)\,dt+\boldsymbol\Sigma^{1/2}d\mathbf W_t$ when $V\equiv\boldsymbol\Sigma$.

**Theorem.**

1. *(Uniqueness.)* Let $f$ be a strictly positive $2\pi$-periodic density on $\mathbb T^p$, and let $V$ be $2\pi$-periodic. Assume the second derivatives of $f$ and of the entries of $V$ are Hölder continuous. Then the wrapping $\boldsymbol\Theta_t$ of the Langevin diffusion for $f$ is the unique time-reversible diffusion on $\mathbb T^p$ that is ergodic with stationary density $f$ and diffusion matrix $V$.
2. *(Wrapped normal process.)* Taking $f$ to be the wrapped normal density $\mathrm{WN}(\boldsymbol\mu,\tfrac12\mathbf A^{-1}\boldsymbol\Sigma)$ gives the toroidal analogue of the Ornstein–Uhlenbeck process $d\mathbf X_t=\mathbf A(\boldsymbol\mu-\mathbf X_t)\,dt+\boldsymbol\Sigma^{1/2}d\mathbf W_t$:
$$d\boldsymbol\Theta_t=\mathbf A\Big(\boldsymbol\mu-\boldsymbol\Theta_t-\sum_{\mathbf k\in\mathbb Z^p}2\pi\mathbf k\,w_{\mathbf k}(\boldsymbol\Theta_t)\Big)dt+\boldsymbol\Sigma^{1/2}d\mathbf W_t,\qquad w_{\mathbf k}(\boldsymbol\theta)=\frac{\phi(\boldsymbol\theta-\boldsymbol\mu+2\pi\mathbf k)}{\sum_{\mathbf m}\phi(\boldsymbol\theta-\boldsymbol\mu+2\pi\mathbf m)},$$
where $\phi$ is the $\mathcal N(\mathbf 0,\tfrac12\mathbf A^{-1}\boldsymbol\Sigma)$ density.
3. *(Tractable approximation.)* The transition density $p_t$ of this process is not available in closed form. It is approximated by the density $p_t^{\mathrm{WOU}}$ of the wrapped Ornstein–Uhlenbeck process: wrap the Euclidean OU process started from the winding number $\mathbf m$ drawn with probability $w_{\mathbf m}(\boldsymbol\theta_0)$. This approximation matches the point mass as $t\to0$, has the correct stationary law $\mathrm{WN}(\boldsymbol\mu,\tfrac12\mathbf A^{-1}\boldsymbol\Sigma)$ as $t\to\infty$, and is time-reversible like $p_t$.

## Expansion

Kent's characterization says that an ergodic time-reversible diffusion with prescribed stationary density and diffusion matrix is determined by its Langevin drift. Wrapping preserves reversibility, so the torus inherits the uniqueness. The Euclidean OU process is the unique reversible diffusion with Gaussian stationary law and constant diffusion. Its natural toroidal analogue is therefore the Langevin diffusion for a wrapped normal, whose drift is the OU drift averaged over winding numbers. It is almost linear near $\boldsymbol\mu$ and vanishes at the antipode. Since $p^{\mathrm{WOU}}_t$ is a finite mixture of wrapped Gaussians, it gives fast approximate likelihoods. The evolutionary model ETDBN pairs such dihedral diffusions with amino-acid substitution processes in a hidden-state model of the evolution of aligned protein pairs. This makes it possible to detect evolutionary motifs in which structure and sequence change jointly.

## Sources

- E. García-Portugués, M. Golden, M. Sørensen, K. V. Mardia, "Toroidal diffusions and protein structure evolution", arXiv:1804.00285 (2018): Section 2 (Langevin drift, Proposition 1 on uniqueness, wrapped normal process, Corollary 1 on the WOU approximation), Section 3 (ETDBN evolutionary model), Section 4 (case study). <https://doi.org/10.48550/arXiv.1804.00285>
