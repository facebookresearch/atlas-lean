# Local attraction in a scalar energy-balance model

Let a scalar energy-balance model $C\,T' = F(T)$ with heat capacity $C > 0$ have $F$ continuously differentiable near an equilibrium
$T^*$, $F(T^*) = 0$ and $F'(T^*) < 0$, for one fixed parameter value. Then there are $\delta, K, \alpha > 0$ such that every initial value
with $\lvert T(0) - T^*\rvert < \delta$ has a unique solution for all $t \ge 0$, which satisfies
$\lvert T(t) - T^*\rvert \le K e^{-\alpha t}\lvert T(0) - T^*\rvert$. Existence for all time follows because $F(T)$ has the sign of
$T^* - T$ near $T^*$, so a small interval around $T^*$ is forward invariant; the decay is the scalar case of Lyapunov's indirect method.
Discontinuous albedo needs a piecewise analysis, and bifurcations need further nondegeneracy conditions.

## Depends on

## Proof depends on

- [A negative derivative near an equilibrium gives the restoring sign](local-sign.md)
- [Pointwise decay of the quadratic energy about a reference value](quadratic-energy-decay-about-reference.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- Derived on this page by specializing the linked conditional decay form of Lyapunov's indirect method to a scalar equation, together with the forward-invariance argument stated above; the general theorem's sources are on its page. No further external source is followed.
