# Uniqueness of positive steady states on a two-patch interval

**Problem.** On $[-L^-,L^+]$ with $L^\pm>0$, find $u>0$ with

$$0=d^-u_{xx}+f^-(u)\ \ (x\in(-L^-,0)),\qquad 0=d^+u_{xx}+f^+(u)\ \ (x\in(0,L^+)),$$

$$u(0-)=u(0+),\qquad d^-u_x(0-)=d^+u_x(0+),\qquad u_x(-L^-)=u_x(L^+)=0,$$

with diffusion rates $d^\pm>0$.

**Standing assumptions (SA).** $f^\pm$ are $C^1$ on $[0,\infty)$ and $C^2$ on $(0,\infty)$, $f^\pm(0)=0<(f^\pm)'(0)$, and there are carrying capacities $K^-<K^+$ with $f^\pm>0$ on $(0,K^\pm)$ and $f^\pm<0$ on $(K^\pm,\infty)$. Let $F^\pm(u)=\frac1{d^\pm}\int_0^uf^\pm(s)\,ds$ be the potentials of the Hamiltonians $H^\pm(u,v)=\frac12v^2+F^\pm(u)$.

**Necessary shape.** Under SA every positive solution is strictly increasing, takes values in $(K^-,K^+)$, and satisfies $u(-L^-)>K^-$, $u(L^+)<K^+$.

**Theorem.** Assume SA together with

- $\mathbf M^-$: $(f^-)'<0$ on $[K^-,K^+]$, or alternatively $\mathbf{C1}^-$, $\mathbf{C2}^-$ (the mirror conditions on the left);
- $\mathbf{C1}^+$: $(\sqrt{F^+})''\le0$ on $(K^-,K^+)$;
- $\mathbf{C2}^+$: $\big(F^+/((F^+)')^2\big)''\ge0$ on $(K^-,K^+)$.

Then the problem has a unique positive solution.

**Generalized logistic growth.** For Richards growth $f^\pm(u)=r^\pm u\big(1-(u/K^\pm)^{p^\pm}\big)$ with $K^-<K^+$, SA, $\mathbf M^-$ and $\mathbf{C1}^+$ always hold, and $\mathbf{C2}^+$ holds for all $K^-\in(0,K^+)$ iff $p^+\ge1$. So logistic growth ($p^\pm=1$) gives a unique positive steady state.

## Depends on

- [Logistic growth equation](../../../logistic-growth-equation/README.md)

## Expansion

On each side the steady-state equation is the Hamiltonian system $u'=v$, $v'=-f^\pm(u)/d^\pm$. Shoot from the left end with $u(-L^-)=\alpha$, $v=0$, and from the right end with $u(L^+)=\beta$, $v=0$; a solution is a pair $(\alpha,\beta)$ for which the two orbits match the interface conditions $u^-(0,\alpha)=u^+(0,\beta)$ and $d^-v^-(0,\alpha)=d^+v^+(0,\beta)$. Condition $\mathbf M^-$ makes the left interface values monotone in $\alpha$, and $\mathbf{C1}^+$, $\mathbf{C2}^+$, the hypotheses of Chicone's monotonicity theorem for period functions of potential systems, make the time to travel along the right orbits monotone, so the matching curves cross exactly once.

## Sources

- P. de Leenheer, J. S. MacDonald, S. Patel, "Unique steady states for population models in a heterogeneous environment", *Discrete and Continuous Dynamical Systems - B* 34 (2026), 275–291, problem (pde)–(neumann), standing assumptions, Corollary 1, Theorems 1 and 2, Lemma on Richards growth, <https://doi.org/10.3934/dcdsb.2025172> (preprint arXiv:2505.03984).
