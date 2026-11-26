# Classification of radial equilibria of the Jäger–Luckhaus system on the disk

**Model.** On the unit disk $\Omega=B_1(0)\subset\mathbb R^2$ consider the Jäger–Luckhaus (parabolic–elliptic Keller–Segel) chemotaxis system with no-flux boundary conditions
$$u_t=\Delta u-\nabla\cdot(u\nabla v),\qquad 0=\Delta v-\mu+u,\qquad \partial_\nu u=\partial_\nu v=0\ \text{on }\partial\Omega,$$
where $u\ge0$ is the cell density, $v$ the chemical signal normalized by $\int_\Omega v=0$, $M=\int_\Omega u_0>0$ is the conserved total mass and $\mu=M/\pi$. Let $j_{1,1}\approx 3.8317$ be the first positive zero of the Bessel function $J_1$ and set $\Lambda=j_{1,1}^2$.

**Theorem.** For every $M>0$ the unique constant equilibrium is $(\mu,0)$. Nonconstant, nonnegative classical radial equilibria are classified by mass:

1. if $0<M\le 8\pi$, there are none;
2. if $8\pi<M<\Lambda\pi$, there is exactly one, and it is strictly decreasing in $r=|x|$ (central aggregation);
3. if $M=\Lambda\pi$, there are none;
4. if $M>\Lambda\pi$, there is exactly one monotone one, and it is strictly increasing in $r$ (peripheral enrichment);
5. non-monotone radial equilibria exist if and only if $M\ge M_{\mathrm{nm}}$ for a threshold $M_{\mathrm{nm}}>\Lambda\pi$.

**Shape criterion.** For a nonconstant radial equilibrium, $M<\Lambda\pi$ holds if and only if $u'(r)<0$ on $(0,1)$, and $M>\Lambda\pi$ holds if and only if $u'(r_0)>0$ for some $r_0\in(0,1)$. The value $\Lambda\pi$ is where the constant state $\mu=\Lambda$ meets the first nonconstant radial Neumann eigenfunction $J_0(j_{1,1}r)$ of $-\Delta$ on the disk.

## Expansion

Radial equilibria satisfy $u=\lambda e^{v}$ with $\Delta v=\mu-\lambda e^{v}$, a Liouville-type equation with a constant source. Passing to the cumulative mass $F(\xi)=\int_{|x|<\sqrt\xi}u\,dx$ turns the equilibrium problem into a second-order ODE on $[0,1]$, whose shooting parameter $\beta$ generates all solutions. Small-amplitude analysis shows that as $\beta\to0$ the equilibria bifurcate from $u\equiv\Lambda$ (the mode $J_0(j_{1,1}r)$ with Neumann condition $J_0'(j_{1,1})=-J_1(j_{1,1})=0$); one sign of $\beta$ gives the decreasing family, which terminates as $M\downarrow 8\pi$ (the critical mass for radial collapse in two dimensions), and the other gives increasing equilibria for every $M>\Lambda\pi$. The sign of $(M-\Lambda\pi)$ controls the sign of $F(\xi)-M\xi$, which gives the shape criterion.

## Sources

- Xuan Mao, Wanwan Wang, "Unstable radial equilibria as sharp concentration thresholds for the Jäger–Luckhaus model on the unit disk", arXiv:2610.39209 (2026), Theorem 1.1, Corollary 2.5 and Proposition 2.7, <https://doi.org/10.48550/arXiv.2610.39209>.
