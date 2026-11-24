# Round-off versus truncation in time stepping

Let $\Psi_h$ be a one-step method that is consistent of order $p \ge 1$ on a set $K$ with constant $C$ (local defect at most $C h^{p+1}$ for $0 < h \le h_0$) and
Lipschitz with constant $1 + Lh$ ($L \ge 0$) on $K$. Suppose it is executed in floating point so that each computed step adds a rounding defect of norm at most
$\delta$, and that the exact and computed trajectories stay in $K$ up to time $T = nh$. Then the global error satisfies

$$\lVert \tilde x_n - x(T) \rVert \le e^{LT} \bigl( \lVert \tilde x_0 - x(0) \rVert + T (C h^{p} + \delta / h) \bigr).$$

With $\delta = c\,u$ for the unit roundoff $u$, the bound $C h^p + c u/h$ is minimized at $h_\ast = (c u/(pC))^{1/(p+1)}$, so the certified error is of order
$u^{p/(p+1)}$; reducing $h$ below $h_\ast$ increases the bound, because the rounding term grows like $u/h$ while the truncation term shrinks like $h^p$.

## Proof

Write $x_k = x(kh)$, so that $x_{k+1} = \Psi_h(x_k) + d_k$ with $\lVert d_k \rVert \le C h^{p+1}$, and $\tilde x_{k+1} = \Psi_h(\tilde x_k) + e_k$ with $\lVert e_k \rVert \le \delta$. Since both
points lie in $K$, $\varepsilon_k = \tilde x_k - x_k$ satisfies $\lVert \varepsilon_{k+1} \rVert \le (1 + Lh) \lVert \varepsilon_k \rVert + C h^{p+1} + \delta$, and the induction of the discrete
Gronwall bound with $1 + Lh \le e^{Lh}$ gives $\lVert \varepsilon_n \rVert \le e^{Lnh}(\lVert \varepsilon_0 \rVert + n(C h^{p+1} + \delta))$, where $nh = T$. Minimizing $C h^p + c u h^{-1}$ over
$h > 0$ gives $p C h^{p-1} = c u h^{-2}$.

## Depends on

- [Sampling a continuous-time flow into discrete dynamics](sampling-a-continuous-time-flow-into-discrete-dynamics.md)

## Proof depends on

- [Discrete Gronwall error propagation for perturbed iterations](discrete-gronwall-error-propagation-for-perturbed-iterations.md)

## Related topics

- [The relative error bound](../../../ComputerScience/algebraic-and-numerical-algorithms/floating-point-rounding/abs-fl-sub-le.md)

## Sources

- D. Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1) (1991), Section 1 (the rounding error of the basic arithmetic operations and its measurement). Background reference. <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of Oxford, Sections 2.2 and 2.3 (the global error of Euler's method and of general explicit one-step methods by the recurrence $\lvert e_{n+1}\rvert \le (1 + hL)\lvert e_n\rvert + hT$ and $1 + hL \le e^{hL}$, pp. 8 and 10). Background reference. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
