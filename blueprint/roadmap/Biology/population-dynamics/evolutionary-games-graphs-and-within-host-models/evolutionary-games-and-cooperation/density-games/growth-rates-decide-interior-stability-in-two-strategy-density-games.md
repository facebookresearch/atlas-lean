# Growth rates decide the stability of the interior equilibrium of a two-strategy density game

Consider the two-strategy density game $\dot x_i = r_i x_i (1 - x_T/K_i)$, $K_1 = a y_1 + b y_2$, $K_2 = c y_1 + d y_2$, with positive payoffs $a, b, c, d$ and arbitrary growth rates $r_1, r_2 > 0$. Assume an interior equilibrium $\hat x$ exists, i.e. $\operatorname{sgn}(a - c) = \operatorname{sgn}(d - b) \ne 0$. Let $J$ be the Jacobian at $\hat x$ and set

$$\alpha_1 = ad - bc + (a - c)(b - a), \qquad \alpha_2 = ad - bc + (d - b)(c - d).$$

Then

$$\operatorname{tr} J = -\frac{(d - b)\,\alpha_1 r_1 + (a - c)\,\alpha_2 r_2}{(a - c + d - b)(ad - bc)}, \qquad \det J = -\frac{(a - c)(d - b)\, r_1 r_2}{ad - bc}.$$

**Proposition.**

1. *(Determinant)* The sign of $\det J$ does not depend on $r_1, r_2$: it is positive if $a < c$ and $d < b$, and negative (a saddle) if $a > c$ and $d > b$.
2. *(Trace)* If $\alpha_1 \alpha_2 > 0$, then $\operatorname{tr} J < 0$ for all $r_1, r_2 > 0$. If $\alpha_1 \alpha_2 < 0$, then $\operatorname{tr} J < 0$ when $(d - b)\alpha_1 r_1 + (a - c)\alpha_2 r_2 > 0$ and $\operatorname{tr} J > 0$ when this quantity is negative.

Hence, by the Routh–Hurwitz criterion ($\operatorname{tr} J < 0$, $\det J > 0$), in the coexistence case $a < c$, $d < b$ where the replicator equation has a globally stable interior point, the density game's interior equilibrium is stable for some pairs of growth rates and unstable for others when $\alpha_1 \alpha_2 < 0$; the paper reports that the unstable case produces a limit cycle.

## Proof sketch

The trace is linear in $(r_1, r_2)$ and vanishes at the origin, with constant partial derivatives

$$\frac{\partial \operatorname{tr} J}{\partial r_1} + \frac{\partial \operatorname{tr} J}{\partial r_2} = -\frac{b(a - c) + c(d - b)}{ad - bc} < 0,$$

so the trace is negative on the diagonal $r_1 = r_2$, recovering the replicator result. If both partial derivatives have the same sign they must both be negative, giving the case $\alpha_1\alpha_2 > 0$ (the combinations in which both would be positive contradict the displayed sum). If they have opposite signs, the zero line $(d - b)\alpha_1 r_1 + (a - c)\alpha_2 r_2 = 0$ passes through the positive quadrant and separates stable from unstable growth-rate pairs. Payoffs alone thus no longer determine the outcome: a fast-growing phenotype can destabilize coexistence, illustrating the interplay between $r$-selection (growth rates) and $K$-selection (payoff-determined carrying capacities).

## Depends on

- [Equal growth rates reduce a two-strategy density game to a time-rescaled replicator equation](equal-growth-rate-density-game-is-a-time-rescaled-replicator-equation.md)
- [Equilibria and monomorphic stability of density games coincide with the replicator equation](density-game-equilibria-coincide-with-replicator-dynamics.md)

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [The spectrum of a real 2 × 2 matrix is its set of characteristic roots](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/mem-spectrum-iff-is-char-root.md)
- [Characteristic roots have positive real part when τ > 0 and Δ > 0](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/re-pos.md)
- [Trace–determinant classification of a planar linearization](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/linear-type-2.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- S. Novak, K. Chatterjee and M. A. Nowak, "Density games", *Journal of Theoretical Biology* (2013), Section 4.2, Eqs. (6)–(7) and Proposition 1, <https://doi.org/10.1016/j.jtbi.2013.05.029> (PMC3753514).
