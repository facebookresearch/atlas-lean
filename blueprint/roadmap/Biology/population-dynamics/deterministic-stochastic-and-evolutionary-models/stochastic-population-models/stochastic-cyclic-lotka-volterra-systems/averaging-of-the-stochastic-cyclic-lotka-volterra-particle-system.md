# Averaging of the stochastic cyclic Lotka–Volterra (rock–paper–scissors) particle system

**Model.** $N$ individuals each occupy one of three cyclically ordered states $i \in \mathbb{Z}_3$. With $x = (x_0, x_1, x_2)$ the vector of state fractions on the grid $S_N = \{x \in \frac1N\mathbb{N}^3 : \sum_i x_i = 1\}$, each individual in state $i$ moves to state $i+1$ at rate $a + N x_{i+1}$ (spontaneous switching at rate $a \ge 0$ plus an extensive interaction with the next state); the generator is

$$L_N f(x) = N\sum_{i \in \mathbb{Z}_3} x_i(a + N x_{i+1})\big(f(x + u_i/N) - f(x)\big), \qquad u_i = v_{i+1} - v_i.$$

For $N \to \infty$ on short time scales $O(1/N)$ the fractions follow the cyclic Lotka–Volterra flow $\dot x_i = x_i(x_{i-1} - x_{i+1})$, which conserves $z(x) = x_0x_1x_2 \in (0, \tfrac1{27})$: the simplex interior is foliated by periodic orbits of period $T(z)$, with $T(z) \to 2\pi\sqrt{3}$ as $z \to \tfrac1{27}$ and $T(z) \sim -3\ln z$ as $z \to 0$.

**Theorem (averaging).** Let $m(z) = -\langle x_{i+1}\dot x_i\rangle_z$ be the orbit average along the loop $\{z(x) = z\}$ (independent of $i$), equivalently $m = -A/T$ with $A(z)$ the signed area of the loop, $A' = T$. Let $Z_N(t) = z(X_N(t))$ and suppose $Z_N(0) \Rightarrow z_0 \in (0, \tfrac1{27})$. If $a \ge 1$ or $a = 0$, then for every $T > 0$, $Z_N$ converges in law on $[0,T]$ to the weak solution of

$$dZ = 3\big(a\,m(Z) - Z\big)\,dt + \sqrt{6\,Z\,m(Z)}\,dW, \qquad Z(0) = z_0,$$

whose generator is $\mathcal{L}_{\mathrm{avg}}f = 3(am - z)f' + 3zm f''$. For $0 < a < 1$ the sequence is tight and every limit point is a weak solution of the same equation. In this SDE the boundary $z = \tfrac1{27}$ (the centre) is entrance for all $a \ge 0$, while $z = 0$ (the boundary of the simplex) is entrance for $a \ge 1$, regular for $0 < a < 1$ and exit for $a = 0$.

**Stationary measures.** For $a > 0$ the chain is ergodic with product-form invariant law $\mu_{N,a}(x) = C_{N,a}\prod_i \Gamma(Nx_i + a)/\Gamma(Nx_i + 1)$, which converges weakly to the symmetric Dirichlet law with density $\propto z(x)^{a-1}$ on the simplex; its image under $z$ is the stationary law of the averaged SDE.

## Proof sketch

The generator splits as $N\mathcal{L}_{\mathrm{fast}} + \mathcal{L}_{\mathrm{slow}} + o(1)$, with $\mathcal{L}_{\mathrm{fast}}$ the Lotka–Volterra vector field and $\mathcal{L}_{\mathrm{slow}}$ containing the spontaneous drift $a\sum_i x_i u_i$ and the demographic diffusion $\tfrac12\sum_i x_ix_{i+1}(u_i,u_i)$. Since $z$ is invariant under the fast flow, only $\mathcal{L}_{\mathrm{slow}}(f\circ z)$ survives, and averaging its coefficients over a period of the fast loop yields the one-dimensional operator. Spontaneous switching ($a$) pushes orbits towards the centre, while demographic noise pushes them outwards; $a = 1$ is where the boundary stops being reachable, matching the uniform Dirichlet law.

## Sources

- Julien Barré, Bastien Fernandez and Grégoire Panel, "Slow-fast dynamics in stochastic Lotka–Volterra systems", *Annales de l'Institut Henri Poincaré, Probabilités et Statistiques* 61 (2025), 1878–1896, <https://doi.org/10.1214/24-aihp1467>. Preprint version: arXiv:2205.04370 (2022), Section 2 (fast dynamics, averaged operator and boundary classification) and Section 3 (main averaging theorem), <https://doi.org/10.48550/arXiv.2205.04370>.
