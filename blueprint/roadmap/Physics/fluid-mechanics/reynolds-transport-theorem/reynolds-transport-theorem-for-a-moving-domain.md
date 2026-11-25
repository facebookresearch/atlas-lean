# Reynolds transport theorem for a moving domain

This node covers the Reynolds transport theorem. Let $w$ be a continuously differentiable velocity field on $\mathbb{R}^3 \times [0, T]$
with flow map $\phi_t$, let $\Omega_0$ be a bounded open set with Lipschitz boundary and $\Omega(t) = \phi_t(\Omega_0)$, and let $f$ be a continuously
differentiable scalar field. Then, for $0 < t < T$,

$$\frac{d}{dt}\int_{\Omega(t)} f\,dV = \int_{\Omega(t)} \frac{\partial f}{\partial t}\,dV + \int_{\partial\Omega(t)} f\,(w\cdot n)\,dA,$$

where $n$ is the outward unit normal. Equivalently the derivative equals $\int_{\Omega(t)} \big(\partial_t f + \nabla\cdot(f w)\big)\,dV$.

## Expansion

A good expansion proves the volume form by changing variables to $\Omega_0$ and differentiating the Jacobian of the flow map,
using $\partial_t \det D\phi_t = (\nabla\cdot w)\det D\phi_t$, and then obtains the boundary form from the divergence theorem. The engineering
control-volume balances for mass, momentum and energy are consumers of this node, as are the one-dimensional moving-interval cases.

## Sources

- R. L. Panton, *Incompressible Flow*, 4th edition, Wiley, 2013, for the transport theorem and integral balances.
