# Compact smooth Euler data with a finite singular lifespan

There are a nonzero, compactly supported smooth divergence-free datum $u_0$ of rapid initial decay, a time $0<T_*\le1$, and a velocity–pressure pair $(v,p)$ solving unforced Euler in the all-orders Sobolev class on $[0,T_*)$. A single real $E$ satisfies $\int\|v(x,t)\|^2dx<E$ for every $t\in[0,T_*)$. For every real $T>0$, a solution for that same datum in the Sobolev class on the closed interval $[0,T]$ exists if and only if $T<T_*$.

Write $N(t)=\sup_x\|v(x,t)\|+\sup_x\|D_xv(x,t)\|_{\rm op}$ and $W(t)=\sup_x\|\nabla_x\times v(x,t)\|$, using extended nonnegative real suprema. For every $0<T<T_*$, $\sup_{t\in[0,T]}N(t)<\infty$ and $\int_{[0,T)}W(t)\,dt<\infty$. But $\limsup_{t\uparrow T_*}N(t)=\infty$ and $\int_{[0,T_*)}W(t)\,dt=\infty$, with the integrals taken as nonnegative Lebesgue integrals. The same datum admits no global solution in the separately defined smooth energy class.

The data here are smooth and compactly supported; this is not the $C^{1,\alpha}$ singularity statement for odd-symmetric data.

## Depends on

- [All-orders Sobolev Euler solutions on a time interval](local-euler-sobolev-class.md)
- [Whole-space smooth Euler energy class](whole-space-smooth-euler-energy-class.md)
- [Vorticity](vorticity.md)

## Expansion

Separate construction of the smooth compact datum, existence and comparison for the Sobolev path, and the endpoint C¹ and vorticity-integral divergence. Prove the separate obstruction to global smooth finite-energy solutions by the comparison argument, not by assuming they are all Sobolev-smooth.

## Sources

- [OpenAI, *Finite time blowup for the Euler equation*, Theorem 1.1 and its pinned alternate formulation](https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf)
- [Pinned definitions of the suprema](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L149-L162)
- [Pinned source: `exists_compact_smooth_euler_singularity`](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L170-L183)
