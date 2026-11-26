# Nonlinear stability of spiky steady states with signal-dependent motility

**Model.** In the half-cylinder $\Omega = \mathbb{R}_+ \times \mathbb{T}^2$ consider the chemotaxis-consumption system with signal-dependent motility $w^p$,

$$u_t = \nabla\cdot\big(w^p\nabla u - (\alpha-1)p\,u\,w^p\nabla\log w\big), \qquad w_t = D\Delta w - wu,$$

where $u \ge 0$ is the cell density, $w > 0$ the consumed chemical, $D > 0$, $p > 0$, $\alpha \ge 2$. Boundary conditions: periodic in $x' = (x_2,x_3)$; no flux $u_{x_1} - (\alpha-1)pu(\log w)_{x_1} = 0$ and $w = b > 0$ at $x_1 = 0$; $(u,w) \to (0,0)$ as $x_1 \to \infty$.

**Spiky steady state.** For each cell mass $\lambda > 0$, with $k = \frac{\lambda(\alpha-1)^2p^2}{2D[(\alpha-1)p+2]}$, the one-dimensional profile

$$U(x_1) = \frac{\lambda^2(\alpha-1)^2p^2}{2D[(\alpha-1)p+2]}(1+kx_1)^{-2}, \qquad W(x_1) = b(1+kx_1)^{-\frac{2}{(\alpha-1)p}}$$

is a steady state, and $V = -(\log W)_{x_1}$ satisfies $U_{x_1} + (\alpha-1)pUV = 0$, $V^2 = \frac{2U}{D[(\alpha-1)p+2]}$ and $DV_{x_1} - DV^2 + U = 0$.

**Theorem.** Fix $p>0$, $\alpha\ge 2$, $D>0$, $b>0$, $\lambda>0$. Let $u_0 \ge 0$ and $w_0 > 0$ with $w_0(0,x') = b$, and suppose the perturbation of $(U,W)$ has zero mass, satisfies the boundary compatibility conditions, and is small in the weighted energy norm $N(0)$ built from the weights $(W^{-p}U^{-1}, U^{-1}, W^pU^{-1})$. Then there is $\varepsilon_0 > 0$ such that $N(0) \le \varepsilon_0$ yields a unique global strong solution with $\sup_{t\ge0}N(t) \le CN(0)$ and

$$\lim_{t\to\infty}\Big(\|u(\cdot,t) - U\|_{L^\infty(\Omega)} + \Big\|\frac{w(\cdot,t)}{W} - 1\Big\|_{L^\infty(\Omega)} + \|-\nabla\log w(\cdot,t) - Ve_1\|_{L^\infty(\Omega)}\Big) = 0.$$

The result holds for arbitrarily large steady mass $\lambda$.

## Expansion

The Hopf-Cole variable $v = -\nabla\log w$ turns the logarithmic sensitivity into a conservation-law structure, at the price of nonlinear boundary conditions at $x_1 = 0$. The main obstacles are that the effective diffusion $W^p \sim (1+x_1)^{-2/(\alpha-1)}$ degenerates algebraically at infinity and that, on the nonzero transversal Fourier modes in $\mathbb{T}^2$, the density perturbation couples to the chemical gradient at order $\lambda$. Weighted energy estimates with derivative-dependent algebraic weights absorb both, closing a bootstrap without smallness of $\lambda$. Spiky profiles of this type model the accumulation of bacteria near an oxygen-supplying boundary.

## Sources

- Lin Chang, Song Xu and Yuling Xu, "Nonlinear Stability of Spiky Patterns for a Three-Dimensional Chemotaxis--Consumption Model with Signal-Dependent Motilities", arXiv:2611.22803 (2026), Section 2, Theorem 2.1, <https://doi.org/10.48550/arXiv.2611.22803>.
