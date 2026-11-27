# Shear-flow reduction of chemotactic target search to one dimension

**Model.** A searching agent (for example a sperm cell seeking an egg in broadcast spawning) moves on the torus $\mathbb T^2 = [0,L)^2$ by

$$d\mathbf X_t = \begin{pmatrix}A\,u(Y_t)\\ 0\end{pmatrix}dt + V(\mathbf X_t)\,dt + \sqrt{2\nu}\,d\mathbf B_t, \qquad V = \varphi(\chi|\nabla c|)\frac{\nabla c}{|\nabla c|},$$

where $Au(y)$ is a shear flow of amplitude $A$, $\chi \ge 0$ is the chemotactic sensitivity, $\varphi \in C^2(\mathbb R_+)$ with $\varphi(0) = 0$ caps the chemotactic speed, and the attractant $c$ released by a target density $n$ solves the advection–diffusion equation $-\Delta c + Au(y)\partial_x c = n - c$. The target is the ball $B((L/2,L/2);\delta)$, which contains the vertical support of $n$. Let $T^{A;\chi}_{2D}$ be the hitting time of the target. Write $\langle c\rangle(y)$ for the horizontal average of $c$ (which solves $\partial_y^2\langle c\rangle = \langle n\rangle - \langle c\rangle$) and $c_\sim = c - \langle c\rangle$. The **effective one-dimensional search** is the vertical motion

$$dY_t = V^{(2)}_{\mathrm{eff}}(Y_t)\,dt + \text{(vertical Brownian noise)}, \qquad V^{(2)}_{\mathrm{eff}} = \varphi(\chi|\partial_y\langle c\rangle|)\,\frac{\partial_y\langle c\rangle}{|\partial_y\langle c\rangle|},$$

with $T^\chi_{1D}$ the hitting time of the strip $[L/2 - \delta, L/2 + \delta]$.

**Theorem.** Let $u \in C^2(\mathbb T)$ have $u(L/2) = 0$ and be strictly monotone near the target level, $\min_{|y - L/2| \le 2\delta}|u'(y)| \ge u_d > 0$, with finitely many critical points, all non-degenerate.

1. (Passive search, $\chi = 0$.) $\displaystyle\lim_{A\to\infty}\mathbb E^{(x_0,y_0)}T^{A}_{2D} = \mathbb E^{y_0}T_{1D}$.
2. (Horizontal homogenization of the attractant.) For $i \in \{0,1,2\}$ and $j \in \{0,1\}$,

$$\|\partial_x^ic_\sim\|_\infty \le \frac{C|\log A|\,\|\partial_x^in_\sim\|_\infty}{A^{2/3}}, \qquad \|\partial_x^j\partial_yc_\sim\|_\infty \le \frac{C|\log A|^2\,\|\partial_x^j\nabla n_\sim\|_\infty}{A^{1/6}},$$

with $C = C(\nu, L)$.

3. (Chemotactic search.) If moreover $n \in C^2(\mathbb T^2)$, then for every starting point

$$\lim_{A\to\infty}\mathbb E^{(x_0,y_0)}T^{A;\chi}_{2D} = \mathbb E^{y_0}T^\chi_{1D},$$

with an explicit rate.

So strong shear turns a two-dimensional search for a small target, whose hitting time grows like $\log(1/\delta)$, into a one-dimensional search for a strip, which stays bounded as $\delta \to 0$. Chemotaxis then acts only through the horizontally averaged gradient.

## Expansion

For large $A$ the agent sweeps horizontally across each level $y$ faster than it diffuses vertically. Near the target level, monotonicity of $u$ makes the flow mix horizontally (relaxation enhancement), so reaching the strip $|y - L/2| \le \delta$ is followed almost immediately by a hit of the ball. The expected hitting times solve elliptic problems $-\nu\Delta T - Au\,\partial_xT - V\cdot\nabla T = 1$ off the target. Hypocoercivity-type estimates for $-\nu\Delta + Au(y)\partial_x$ on functions with zero horizontal mean show that the $x$-dependent part of $T$ (and of $c$) decays with rates $A^{-2/3}$ and $A^{-1/6}$ coming from the non-degenerate shear. What is left is the one-dimensional ODE for $\mathbb E^{y_0}T_{1D}^\chi$, which can be solved by Dynkin's formula with an integrating factor.

## Sources

- Yishu Gong, Siming He, Alexander Kiselev, "Random search in fluid flow aided by chemotaxis", arXiv (2021). Section 2 (model), Section 4: Theorems 1–3, definitions of the one-dimensional and effective hitting times; proofs in Sections 5–7. <https://doi.org/10.48550/arXiv.2107.02913>. Published version: Bulletin of Mathematical Biology 84(7) (2022), article 71, <https://doi.org/10.1007/s11538-022-01024-4>; locators above refer to the arXiv version.
