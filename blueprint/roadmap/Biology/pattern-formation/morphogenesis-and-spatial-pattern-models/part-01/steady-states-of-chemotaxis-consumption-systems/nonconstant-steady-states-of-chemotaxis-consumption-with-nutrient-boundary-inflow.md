# Nonconstant steady states of chemotaxis–consumption with nutrient boundary inflow

**Setting.** Let $\Omega\subset\mathbb{R}^n$ be a bounded domain with $\partial\Omega\in C^{2,\alpha}$, let $\bar v>0$ be a constant inflow rate of nutrient through the boundary, and let $M>0$ be the total bacterial mass. The stationary chemotaxis–consumption problem with nutrient inflow is

$$
0=\nabla\cdot(\nabla U-U\nabla V),\quad 0=\Delta V-UV\ \text{ in }\Omega,\qquad \partial_\nu U-U\partial_\nu V=0,\quad \partial_\nu V=\bar v\ \text{ on }\partial\Omega,
$$

with the mass constraint $\int_\Omega U=M$. A solution $(U,V)\in(C^2(\bar\Omega))^2$ is *positive* if $U>0$ and $V>0$ on $\bar\Omega$.

**Theorem.** There is a constant $L^\star\ge 0$ such that for every $M>L^\star$ the problem has a unique positive classical solution $(U,V)\in(C^{2,\alpha}(\bar\Omega))^2$. It has the Boltzmann form

$$
U=M\,\frac{e^{V}}{\int_\Omega e^{V}},
$$

where $V$ solves the nonlocal Neumann problem $\Delta V=\frac{M}{\int_\Omega e^V}\,V e^V$ in $\Omega$, $\partial_\nu V=\bar v$ on $\partial\Omega$. If $\Omega=B_R(0)$ is a ball, then $L^\star=0$, so a positive steady state exists for every mass $M>0$; it is radially symmetric, and $U(r)$ and $V(r)$ are increasing and convex in $r\in[0,R)$.

## Expansion

The zero-flux condition forces $\nabla U=U\nabla V$, so $U$ is a multiple of $e^V$ and the system collapses to one nonlocal equation for $V$. Replacing the nonlocal coefficient by a parameter $\lambda>0$ gives the local problem $\Delta V_\lambda=\lambda V_\lambda e^{V_\lambda}$, $\partial_\nu V_\lambda=\bar v$, which has a unique positive solution for every $\lambda$ (sub- and supersolutions plus a maximum principle with Neumann sign condition). The mass is then recovered as $M=F(\lambda):=\lambda\int_\Omega e^{V_\lambda}$. Differentiating in $\lambda$ shows $V_\lambda$ decreases while $\lambda V_\lambda$ grows, so $F$ is $C^1$, strictly increasing, tends to $\infty$ as $\lambda\to\infty$, and has a finite limit $L^\star$ as $\lambda\downarrow 0$; this gives existence and uniqueness for $M>L^\star$. Unlike Dirichlet or Robin data, $\|V_\lambda\|_\infty$ blows up as $\lambda\downarrow 0$, which is why $L^\star$ is only identified (as $0$) in the radial case, where $0<V_\lambda'<\bar v$ gives the needed control.

## Sources

- Frederic Heihoff, Piotr Knosalla, "A chemotaxis-consumption model with boundary inflow of a nutrient, steady states", arXiv:2607.08916: Theorem 1 (main result); Lemmas 4, 5, 8, 10 and 12 (local problem, monotonicity in the parameter, the mass function and its radial limit). <https://doi.org/10.48550/arXiv.2607.08916>
