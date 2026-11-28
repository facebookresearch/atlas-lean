# Primer-vector conditions for minimum-fuel bounded-thrust transfer

This node covers Lawden's necessary conditions for optimal bounded-thrust transfers. Consider $\dot r = v$,
$\dot v = g(r) + (T/m)\,u$, $\dot m = -T/c$, with smooth gravity field $g$, constant exhaust speed $c > 0$, unit thrust direction $u$ and thrust
magnitude $0 \le T \le T_{\max}$, initial mass $m(0) = m_0 > 0$ and a fuel budget that keeps $m(t) \ge m_{\mathrm{dry}} > 0$ on every admissible trajectory, steering from given initial to given final position and velocity in fixed time while maximizing the final mass.
Along a normal extremal given by the Pontryagin maximum principle, with costates $\lambda_r, \lambda_v, \lambda_m$, the primer vector
$p = \lambda_v$ satisfies $\ddot p = G(r)^{\mathsf T} p$, where $G = \partial g/\partial r$ (so $\ddot p = G(r)\,p$ when $g$ is the gradient of a potential); on thrusting arcs ($T > 0$) with $p \ne 0$ the optimal direction is $u = p/|p|$, while on coast arcs ($T = 0$) the direction does not affect the dynamics and any unit vector is optimal; and the
thrust is $T = T_{\max}$ where the switching function $S = |p|/m - \lambda_m/c$ is positive and $T = 0$ where it is negative.

## Expansion

A good expansion states the optimal-control problem with its admissible controls and the existence assumption, applies the
Pontryagin maximum principle, and derives the primer equation and the switching structure. Existence of optimal controls, singular arcs
($S \equiv 0$) and sufficiency are separate nodes.

## Sources

- D. F. Lawden, *Optimal Trajectories for Space Navigation*, Butterworths, 1963.
- J. E. Prussing and B. A. Conway, *Orbital Mechanics*, 2nd edition, Oxford University Press, 2013, for primer-vector theory.
