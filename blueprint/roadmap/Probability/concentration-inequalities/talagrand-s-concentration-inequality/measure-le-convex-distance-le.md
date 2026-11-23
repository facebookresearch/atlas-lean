# Tail form of the convex-distance inequality

Under the hypotheses of the convex-distance inequality, for every $t \ge 0$,

$$P\big(f_c(A, \cdot) \ge t\big) \le \frac{e^{-t^2/4}}{P(A)}$$

(Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*, Publ.
Math. IHÉS 81 (1995), Theorem 4.1.1, (4.1.3)). If $P(A) \ge 1/2$, the set of points at convex
distance at least $t$ has probability at most $2e^{-t^2/4}$, whatever the dimension. The
superlevel set need not be measurable; its measure is the outer measure, as in the source.

## Informally uses

- [Talagrand's convex-distance inequality](lintegral-exp-convex-distance-sq-le.md): Markov's
  inequality applied to $\exp(f_c^2/4)$. When the superlevel set is not measurable and its outer
  measure is meant, Markov's inequality is applied to the source's stronger version of that
  inequality, for the upper integral, which the linked page discusses.
