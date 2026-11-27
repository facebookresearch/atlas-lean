# Forced Navier–Stokes breakdown on Euclidean three-space

For every real viscosity $\nu>0$ there exist a smooth divergence-free initial velocity $u_0$ on $\mathbb R^3$ and a jointly smooth force $f$ on $\mathbb R^3\times[0,\infty)$ with the following decay. For every integer $m\ge0$ and every real $K$, there is a constant $C$ bounding $\|D^m u_0(x)\|$ by $C/(1+\|x\|)^K$ uniformly in $x$. For each such $m,K$ there is a possibly different $C$ bounding $\|D^m_{x,t} f(x,t)\|$ by $C/(1+\|x\|+t)^K$ uniformly in $x,t\ge0$ (time boundary derivatives within the half-space).

For these same $u_0,f$ there is no global smooth velocity–pressure pair in the whole-space energy class. This is the forced alternative (C); the quantified force is not set to zero. The manuscript constructs more restrictive witnesses than this formulation requires.

## Depends on

- [Smooth forced Navier–Stokes solution classes](forced-navier-stokes-solution-classes.md)

## Expansion

Isolate the forced finite-time singular construction, prove that its zero initial velocity and smooth compactly supported force obey these decay hypotheses, then formalize the smooth comparison argument excluding a global solution in the energy class. This does not supply a result about existence for zero forcing.

## Sources

- [OpenAI, *Finite time blowup for Navier–Stokes*, Theorem 1.1](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Pinned data and forcing definitions](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L124-L191)
- [Pinned source: `navier_stokes_breakdown_R3`](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L273-L276)
