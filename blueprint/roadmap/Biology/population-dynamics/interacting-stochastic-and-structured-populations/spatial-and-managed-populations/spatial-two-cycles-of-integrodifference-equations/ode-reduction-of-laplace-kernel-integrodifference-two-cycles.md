# ODE reduction of Laplace-kernel integrodifference two-cycles

**Setting.** Let $F:\mathbb{R}\to\mathbb{R}$ be a growth map and consider the integrodifference equation

$$N_{t+1}(x)=QN_t=\int_{\mathbb{R}}K(x-y)\,F(N_t(y))\,dy$$

with the Laplace dispersal kernel $K(u)=\tfrac{\sigma}{2}e^{-\sigma|u|}$, $\sigma>0$. Suppose the non-spatial map $n\mapsto F(n)$ has a 2-cycle $\{n_-,n_+\}$, $n_-<n_+$. A *spatial 2-cycle* is a pair of functions $N,M:\mathbb{R}\to\mathbb{R}$ with

$$\lim_{x\to\pm\infty}N(x)=n_\pm,\qquad \lim_{x\to\pm\infty}M(x)=n_\mp,\qquad N=Q[M],\quad M=Q[N].$$

**Theorem 2.1.** Let $N,M$ be bounded and continuous. Then $N=Q[M]$ and $M=Q[N]$ hold if and only if $N,M\in C^2$ and

$$\ddot N=\sigma^2\big(N-F(M)\big),\qquad \ddot M=\sigma^2\big(M-F(N)\big).$$

**Theorem 2.2.** With $u=\dot N$, $v=\dot M$, any solution $(N,u,M,v)$ of the first-order system $\dot N=u$, $\dot u=\sigma^2(N-F(M))$, $\dot M=v$, $\dot v=\sigma^2(M-F(N))$ with $u,v\to0$, $N\to n_\pm$ and $M\to n_\mp$ as $t\to\pm\infty$ is a spatial 2-cycle. Spatial 2-cycles are therefore heteroclinic orbits between the equilibria $\tilde x^{(\mp)}=(n_\mp,0,n_\pm,0)$.

**Theorem 2.5.** If $\dot x=f(x)$ is time-reversible with linear reversor $R$ ($Rf(x)=-f(Rx)$) and $\tilde x$ is an equilibrium, then $R\tilde x$ is an equilibrium and $W^u(R\tilde x)=R\,W^s(\tilde x)$. Applied to the reversible system above, this halves the connecting-orbit problem: it suffices to find an orbit from $W^u(\tilde x^{(-)})$ to the fixed set of the reversor.

## Expansion

The Laplace kernel is the Green's function of $\sigma^2-\partial_x^2$ on $\mathbb{R}$: for bounded continuous $g$, $w=K*g$ is the unique bounded solution of $w-\sigma^{-2}\ddot w=g$. Applying this to $N=K*(F\circ M)$ and $M=K*(F\circ N)$ gives the second-order system, and conversely a bounded $C^2$ solution of the ODE recovers the convolution identities. Limits at $\pm\infty$ together with vanishing derivatives give the boundary conditions of a heteroclinic orbit. The linearization at $\tilde x^{(+)}$ has eigenvalues $\pm\sigma\sqrt{1\pm\sqrt{F'(n_-)F'(n_+)}}$ (Lemma 2.7), so when $0<F'(n_-)F'(n_+)<1$ both equilibria are hyperbolic with two-dimensional stable and unstable manifolds, which is the transversality setting used for computer-assisted proofs.

## Sources

- K. Church, K. Constantineau, J.-P. Lessard, "Spatially inhomogeneous two-cycles in an integrodifference equation", *SIAM Journal on Applied Dynamical Systems* 25(4) (2026), 2686–2736, Section 2, Theorems 2.1, 2.2, 2.5 and Lemma 2.7, <https://doi.org/10.1137/25m1814347> (preprint arXiv:2510.21134).
