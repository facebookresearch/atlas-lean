# Forced Navier–Stokes breakdown on the flat three-torus

For every real viscosity $\nu>0$ there exist a smooth divergence-free initial velocity $u_0$ and a force $f$ on $\mathbb R^3\times[0,\infty)$, with $u_0$ and each $f(\cdot,t)$ invariant under every $x\mapsto x+e_i$. The force is jointly smooth up to $t=0$, and for every integer $m\ge0$ and real $K$ there is a real $C$ such that $\|D^m_{x,t}f(x,t)\|\le C/(1+t)^K$ for all $x$ and $t\ge0$ (derivatives within the time half-space).

For these same $u_0,f$ there is no global smooth velocity–pressure pair in the periodic solution class, in particular with spatially periodic pressure. The velocity and pressure are periodic in space, not required to be periodic in time. This is the forced alternative (D), not the unforced periodic regularity question.

## Depends on

- [Smooth forced Navier–Stokes solution classes](forced-navier-stokes-solution-classes.md)

## Expansion

Formalize the periodization and viscosity rescaling of the singular construction, verify periodic velocity and pressure and rapid temporal decay of the force, and prove comparison in the periodic solution class. Merely periodizing a witness on Euclidean space without checking the pressure equation does not suffice.

## Sources

- [OpenAI, *Finite time blowup for Navier–Stokes*, Corollary 10.6](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Pinned periodicity and force definitions](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L116-L205)
- [Pinned source: `navier_stokes_breakdown_periodic`](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L280-L283)
