# Spatially inhomogeneous two-cycle of the logistic integrodifference equation

**Setting.** Take logistic growth $F(u)=(1+\rho)u-\rho u^2$ and the Laplace kernel $K(u)=\tfrac{\sigma}{2}e^{-\sigma|u|}$ in $N_{t+1}=Q[N_t]=K*(F\circ N_t)$. For $\rho>2$ the non-spatial map has the 2-cycle

$$n_\pm=\frac{\rho+2\pm\sqrt{\rho^2-4}}{2\rho}.$$

**Theorem 1.1 (existence).** For $\rho=2.2$ and every $\sigma>0$ there is a 2-cycle $N_t$ of the integrodifference equation with

$$\lim_{x\to-\infty}N_0(x)=\lim_{x\to+\infty}N_1(x)=n_-,\qquad \lim_{x\to+\infty}N_0(x)=\lim_{x\to-\infty}N_1(x)=n_+ .$$

The two spatial halves of the population oscillate in antiphase. The proof is computer-assisted at $\sigma=10$ (Theorem 3 of Section 4 gives explicit approximations $\bar N,\bar M$ with $\|N-\bar N\|_{C(\mathbb{R})},\|M-\bar M\|_{C(\mathbb{R})}\le 4.19\times10^{-13}$), and the rescaling $x\mapsto \sigma x$ transfers the solution to every $\sigma>0$.

**Theorem 1.2 (spectral enclosure).** Let $N_t$ be a 2-cycle, $S=Q\circ Q$ and, without loss of generality, $\sigma=1$. The spectrum of the linearization $\mathcal{M}=DS[N_0]$ lies in the closed disc of radius

$$\mu=\|F'\circ N_0\|_\infty\,\|F'\circ N_1\|_\infty .$$

An eigenfunction $h$ for eigenvalue $\lambda$ solves $\lambda\ddot h=\lambda h-F'(N_1)v$, $\ddot v=v-F'(N_0)h$ with $v=K*(F'(N_0)h)$. If $|\lambda|\ge1$ and $0<F'(n_+)F'(n_-)<1$, the limiting constant-coefficient systems at $\pm\infty$ are hyperbolic with eigenvalues $\xi_{j,k}=(-1)^j\sqrt{1+(-1)^k\sqrt{F'(n_+)F'(n_-)/\lambda}}$, which makes an Evans-function count of unstable eigenvalues possible.

## Depends on

- [ODE reduction of Laplace-kernel integrodifference two-cycles](ode-reduction-of-laplace-kernel-integrodifference-two-cycles.md)

## Expansion

By the ODE reduction, the 2-cycle is a heteroclinic orbit of a reversible four-dimensional system; by reversibility it suffices to connect the unstable manifold of one equilibrium to the reversor's fixed set. The local manifold is enclosed by a validated Taylor parameterization (Theorem 1 of Section 4) and the finite-time orbit by a Chebyshev series boundary-value problem (Theorem 2 of Section 4), each proved through a Newton–Kantorovich radii-polynomial estimate. The spectral bound follows because $DS[N_0]h=K*\big(F'(N_1)\,K*(F'(N_0)h)\big)$ and convolution with a probability kernel has operator norm $1$ on bounded functions.

## Sources

- K. Church, K. Constantineau, J.-P. Lessard, "Spatially inhomogeneous two-cycles in an integrodifference equation", *SIAM Journal on Applied Dynamical Systems* 25(4) (2026), 2686–2736, Theorems 1.1 and 1.2 and Section 4 (Theorems 1–3, Newton–Kantorovich Theorem 4.1), <https://doi.org/10.1137/25m1814347> (preprint arXiv:2510.21134).
