# Local existence for the free boundary problem of branching Brownian motion with selection

**Setting.** In the Brunet–Derrida selection model ($N$-BBM), $N$ Brownian particles on the line branch independently at rate $1$, and at each branching the leftmost (least fit) particle is removed, so the population size stays $N$. As $N \to \infty$ the empirical density converges, and if the following free boundary problem has a classical solution, that solution is the limit density.

Fix $b > 0$ and $\rho_0 \in C^2_c([b,\infty))$ with $\rho_0(b) = 0$, $\rho_0'(b) = 2$ and $\int_b^\infty \rho_0(x)\,dx = 1$. Find a continuous curve $(L_t)_{t\ge 0}$ with $L_0 = b$ and a function $\rho(x,t)$, $x \ge L_t$, such that

$$\rho_t = \tfrac{1}{2}\rho_{xx} + \rho \quad (x > L_t,\ t > 0), \qquad \rho(L_t,t) = 0 \quad (t \ge 0), \qquad \rho(x,0) = \rho_0(x) \quad (x \ge b),$$

$$\int_{L_t}^{\infty} \rho(x,t)\,dx = 1 \quad (t > 0).$$

A pair $(L,\rho)$ is a **classical solution on $[0,T]$** if $L \in C^1([0,T])$, $L_0 = b$, $\rho \in C(\overline{D_{L,T}}) \cap C^{2,1}(D_{L,T})$ with $D_{L,T} = \{(x,t) : L_t < x,\ 0 < t < T\}$, and the equations above hold.

**Theorem.** There exists $T > 0$ such that the free boundary problem has a classical solution $(L,\rho)$ on $[0,T]$. Moreover $\rho_x(x,t)$ has a limit $\rho_x(L_t,t)$ as $x \downarrow L_t$, and $\rho_x(L_t,t) = 2$ for all $t \in [0,T]$; where $\rho_{xx}(L_t,t)$ exists, the boundary moves with speed $\dot L_t = -\tfrac{1}{4}\rho_{xx}(L_t,t)$. Uniqueness follows from the particle-system limit.

**Equivalent problem.** Setting $v(x,t) = e^{-t}\rho_x(x,t)$, the pair $(L,v)$ solves the Stefan-type problem

$$v_t = \tfrac{1}{2}v_{xx} \quad (x > L_t,\ t > 0), \qquad v(L_t,t) = 2e^{-t}, \qquad v(x,0) = h(x), \qquad \dot L_t = -\tfrac{1}{4}e^{t}v_x(L_t,t),$$

with $h \in C^1_c([b,\infty))$, and there is $T > 0$ and a solution with $L \in C^1([0,T])$, $L_0 = b$, $v \in C^{2,1}(D_{L,T})$.

## Expansion

The mass constraint $\int_{L_t}^\infty \rho = 1$ is non-local, but differentiating it in time and using the PDE with $\rho(L_t,t) = 0$ gives $\tfrac{1}{2}\rho_x(L_t,t) = 1$, i.e. the Neumann value $2$ at the boundary. Passing to $v = e^{-t}\rho_x$ converts the problem into a one-phase Stefan problem for the heat equation with Dirichlet data on the moving boundary and a velocity law. For a candidate boundary $L$ in a Lipschitz class $\Sigma(A,T)$ the solution $v$ is represented with heat potentials (initial-data term plus a double-layer potential with density $\varphi$ solving a Volterra equation); the velocity law then defines a map $L \mapsto \tilde L$, and Cannon's estimates show it is a contraction for small $T$ (Fasano's strategy). The fixed point yields $(L,v)$, and $\rho$ is recovered by integrating $v$.

## Sources

- Jimyeong Lee, "Free boundary problems and biological systems with selection rules", *Arch. Math.* 114(1) (2020), 85–95. <https://doi.org/10.1007/s00013-019-01362-1>
- Preprint version (the locators in this item follow its numbering): Jimyeong Lee, "A free boundary problem in biological selection models", arXiv:1707.01232 (2017), Theorems 1 and 2 and Proposition 1, <https://doi.org/10.48550/arXiv.1707.01232>.
