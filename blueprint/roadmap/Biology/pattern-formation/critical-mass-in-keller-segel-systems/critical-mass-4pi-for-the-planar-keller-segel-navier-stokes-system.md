# Critical mass $4\pi$ for the planar Keller–Segel–Navier–Stokes system

**Model.** Let $\Omega \subset \mathbb{R}^2$ be a bounded domain with smooth boundary and outward normal $\nu$. Cells of density $n$ respond chemotactically to a signal $c$ and are transported by an incompressible fluid of velocity $u$ and pressure $P$, which is in turn forced by buoyancy through a gravitational potential $\phi$:
$$
\begin{cases}
n_t + u\cdot\nabla n = \Delta n - \nabla\cdot(n\nabla c), & x\in\Omega,\ t>0,\\
c_t + u\cdot\nabla c = \Delta c - c + n, & x\in\Omega,\ t>0,\\
u_t + (u\cdot\nabla)u = \Delta u - \nabla P + n\nabla\phi, \quad \nabla\cdot u = 0, & x\in\Omega,\ t>0,\\
\partial_\nu n = \partial_\nu c = 0,\quad u = 0, & x\in\partial\Omega,\ t>0.
\end{cases}
$$
Assume $\phi \in W^{2,\infty}(\Omega)$, $n_0 \in C^0(\overline\Omega)$ with $n_0 \ge 0$, $n_0 \not\equiv 0$, $c_0 \in W^{1,\infty}(\Omega)$ with $c_0 \ge 0$, and $u_0 \in D(\mathcal{A})$, where $\mathcal{A}$ is the Stokes operator with Dirichlet conditions on the solenoidal space $L^2_\sigma(\Omega)$.

**Theorem.** If the total cell mass satisfies
$$ m := \int_\Omega n_0 < 4\pi, $$
then the problem has a unique global classical solution $(n,c,u)$ (with a pressure $P \in C^{1,0}(\Omega\times(0,\infty))$), and it is uniformly bounded in time: for every $q > 2$ there is $C > 0$ with
$$ \|n(\cdot,t)\|_{L^\infty(\Omega)} + \|c(\cdot,t)\|_{W^{1,q}(\Omega)} + \|u(\cdot,t)\|_{L^\infty(\Omega)} \le C \qquad \text{for all } t > 0. $$

Since the fluid-free fully parabolic Keller–Segel system on a simply connected planar domain has unbounded solutions for suitable data of every mass $m \in (4\pi,\infty)\setminus 4\pi\mathbb{N}$, the threshold $4\pi$ is the same with and without fluid coupling: the Navier–Stokes feedback does not lower the critical mass below the classical value (previous fluid-coupled results required $m < 2\pi$).

## Depends on

- [Gagliardo–Nirenberg inequality with leading constant $2/\pi$ on planar domains](gagliardo-nirenberg-inequality-with-leading-constant-2-over-pi-on-planar-domains.md)

## Expansion

The fluid destroys the monotonicity of the classical free energy $\mathscr{E}(n,c) = \int n\ln n - \int nc + \tfrac12\int(|\nabla c|^2 + c^2)$, because the transport terms in the $c$-equation create cross terms between $\nabla c$ and $\nabla u$. The proof builds a quasi-energy inequality coupling $\log \mathscr{E}$ with the fluid kinetic energy $\tfrac12\int|u|^2$, whose growth is controlled through $\int n\nabla\phi\cdot u$. The sharp mass enters through two inequalities with explicit constants: an entropy–interaction bound with coefficient $(1+\varepsilon)a/(8\pi)$ that lower-bounds $\mathscr{E}$ when $m<4\pi$ (the boundary halves the planar $8\pi$), and the domain Gagliardo–Nirenberg inequality with constant $2/\pi$, obtained from relative isoperimetry and rearrangement. Together they give an $L\log L$ bound on $n$, then $L^2$ and finally $L^\infty$ bounds by standard parabolic and Stokes regularity, and extensibility yields global existence.

## Sources

- Lili Du, Yulan Wang and Yichen Zhang, "On the optimal mass threshold for the two-dimensional Keller-Segel system coupled to the Navier-Stokes equations", arXiv:2611.09160 (2026), Section 1.3, Theorem 1.1; Section 3 (quasi-energy argument), <https://doi.org/10.48550/arXiv.2611.09160>.
