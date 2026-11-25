# Lagrange-multiplier form of holonomically constrained motion is well posed

This node covers the equivalence of the multiplier form and the reduced form of constrained mechanics. Let $M(q)$ be a continuously
differentiable symmetric positive-definite $n \times n$ matrix field, $F(q, \dot q, t)$ continuously differentiable, and $g : \mathbb{R}^n \to \mathbb{R}^m$
three times continuously differentiable with $Dg(q)$ of rank $m$ on $\mathcal{M} = g^{-1}(0)$. Consider

$$M(q)\ddot q = F(q, \dot q, t) + Dg(q)^{\mathsf T}\lambda, \qquad g(q) = 0 .$$

For consistent data $q_0 \in \mathcal{M}$ and $\dot q_0 \in \ker Dg(q_0)$, the multiplier is a unique locally Lipschitz function
$\lambda = \Lambda(q, \dot q, t)$, obtained by differentiating the constraint twice, and the system has a unique local solution, which stays on
$\mathcal{M}$. In any local chart of $\mathcal{M}$ this solution is exactly the solution of the reduced second-order equation obtained from the
virtual-work (Lagrange-d'Alembert) principle with the constraint forces eliminated.

## Expansion

A good expansion derives $\Lambda$ from the invertible matrix $Dg\,M^{-1}Dg^{\mathsf T}$, proves invariance of $\mathcal{M}$ and of the
velocity constraint for the resulting ODE, and compares it with the chart reduction. Global existence, nonholonomic constraints and numerical
index reduction are separate nodes.

## Sources

- D. T. Greenwood, *Principles of Dynamics*, 2nd edition, Prentice-Hall, 1988, for Lagrange multipliers and holonomic constraints.
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, for index reduction of constrained mechanical systems.
