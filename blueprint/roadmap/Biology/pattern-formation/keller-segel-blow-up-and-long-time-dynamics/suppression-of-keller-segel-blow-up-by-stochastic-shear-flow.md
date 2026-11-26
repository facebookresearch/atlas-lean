# Suppression of Keller–Segel blow-up by stochastic shear flow

On the channel $\Omega=\mathbb T\times\mathbb R$ ($\mathbb T=\mathbb R/2\pi\mathbb Z$) consider the planar parabolic–elliptic Keller–Segel model advected by a randomly modulated Couette flow,
$$dn+\sqrt A\,y\,\partial_x n\circ dW_t=\big(\Delta n-\nabla\cdot(n\nabla c)\big)dt,\qquad -\Delta c=n,$$
with Stratonovich noise from a standard real Brownian motion $W_t$, amplitude $A>0$, and deterministic data $n_{\rm in}\ge0$, $n_{\rm in}\in H^2\cap L^\infty$, $(1+y^2)n_{\rm in}\in L^1$ (the zero $x$-mode of $c$ fixed by the normalization $\partial_y c_0=\frac12\int n_0-\int_{-\infty}^y n_0$).

**Theorem.** (i) For each $A$ there is a unique nonnegative, mass-conserving maximal local mild solution $(n^A,\tau^A_*)$, and on $\{\tau_*^A<\infty\}$ one has $\limsup_{t\uparrow\tau^A_*}\|n^A(t)\|_{L^\infty}=\infty$.
(ii) Almost surely there is a finite random threshold $A_*(\omega)$ such that $\tau^A_*(\omega)=\infty$ for every integer $A\ge A_*(\omega)$; moreover, for some $C,c>0$ and $\beta\in(0,\frac14]$,
$$\mathbb P(\tau_*^A=\infty)\ge 1-Ce^{-cA^{\beta}}.$$

The mass is arbitrary: strong stochastic shear prevents chemotactic collapse with probability exponentially close to one, even above the $8\pi$ threshold of the unstirred problem. The randomness of the threshold cannot be removed in general: there is a smooth, compactly supported initial datum of mass $16\pi$ that blows up with positive probability for every deterministic amplitude $A\ge1$.

## Expansion

After the time change $t\mapsto At$ the problem becomes one with small viscosity $\nu=1/A$ and unit noise. The passive-scalar part $df+y\partial_xf\circ dW=\nu\Delta f\,dt$ exhibits enhanced dissipation of nonzero $x$-Fourier modes: the random shear tilts each mode to high $y$-frequency, where diffusion damps it on a time scale much shorter than $1/\nu$. A blockwise contraction estimate for the random solution operator, a modal decomposition of the nonlinearity and a bootstrap then show the nonzero modes stay small long enough for the zero mode, which solves an effectively one-dimensional equation controlled by one-dimensional Nash inequalities, to remain bounded. Since one-dimensional Keller–Segel does not blow up, no concentration occurs. The probability bound comes from the tail of the time the Brownian path needs to produce enough mixing.

## Sources

- F. Kong, K. Tawri, *Suppression of Blow-up in Two-dimensional Keller--Segel Systems by Stochastic Couette Flows* (2026), Theorem 1.1 (local existence), Theorem 1.2 (global existence with high probability), Section 4 (enhanced dissipation and bootstrap) and Appendix A (blow-up with positive probability). <https://doi.org/10.48550/arXiv.2609.25551>
