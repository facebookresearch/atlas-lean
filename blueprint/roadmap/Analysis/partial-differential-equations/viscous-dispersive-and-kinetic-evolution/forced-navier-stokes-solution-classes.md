# Smooth forced Navier–Stokes solution classes

For viscosity $\nu>0$, initial velocity $u_0:\mathbb R^3\to\mathbb R^3$ and force $f(x,t)$, a smooth solution on $t\ge0$ consists of velocity $v$ and scalar pressure $p$ jointly smooth up to $t=0$, with $v(x,0)=u_0(x)$ and, for every $x,t$ in the domain,

$$\partial_t v+D_xv\,v=\nu\Delta_xv-\nabla_xp+f,\qquad \operatorname{div}_x v=0.$$

The time derivative at $t=0$ is taken within the nonnegative half-line. In the whole-space energy class the scalar function $x\mapsto\|v(x,t)\|$ belongs to $L^2$ at every time, and there is one real $E$ with $\int_{\mathbb R^3}\|v(x,t)\|^2\,dx<E$ for all $t\ge0$. In the periodic class both $v(\cdot,t)$ and $p(\cdot,t)$ are invariant under $x\mapsto x+e_i$ for each coordinate vector; do not impose the whole-space energy condition on their periodic lifts.

## Depends on

- [Divergence](../singularity-formation-for-the-euler-equations/div.md)

## Expansion

Build the joint smoothness and pointwise operators on the half-space of space–time, with a within-time derivative at zero. Verify the spatial Laplacian and advection conventions and preserve the separate periodic-pressure and uniform-energy requirements.

## Sources

- [Pinned solution-class definitions](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/NavierStokes.lean#L207-L269)
