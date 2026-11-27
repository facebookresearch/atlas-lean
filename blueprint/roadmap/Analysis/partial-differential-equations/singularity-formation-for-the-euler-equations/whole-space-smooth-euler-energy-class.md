# Whole-space smooth Euler energy class

A datum $u_0\colon\mathbb R^3\to\mathbb R^3$ has rapid initial decay when it is smooth, divergence-free and for each $m\in\mathbb N$ and $K\in\mathbb R$ there is a real $C$ such that $\|D_x^m u_0(x)\|\le C/(1+\|x\|)^K$ for every $x$. A global solution in the smooth energy class for this datum is a jointly smooth pair $(v,p)$ on $\mathbb R^3\times[0,\infty)$, with $v(x,0)=u_0(x)$, satisfying for all $x,t$ in that domain

$$\partial_t v+D_xv\,v=-\nabla_x p,\qquad\operatorname{div}_x v=0.$$

The time derivative at zero is taken within the time domain. Each velocity slice is square integrable, and there is one real $E$ with $\int\|v(x,t)\|^2dx<E$ for all $t\ge0$. This does not impose continuity in higher Sobolev norms.

## Depends on

- [Divergence](div.md)


## Background

- [Local solutions of the incompressible Euler equations](is-local-euler-equation-solution.md) use related spatial operators, but do not give this joint smoothness and uniform-energy class.

## Expansion

Reuse the pointwise spatial Euler operators after checking the time boundary and product smoothness conventions. Add the joint regularity and uniform whole-space energy predicates without imposing pressure normalization or Sobolev-jet continuity.

## Sources

- [Pinned global Euler problem definitions](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L47-L81)
