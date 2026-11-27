# Unconditional exponential stability of chemostat washout

For the chemostat with $D, y, \mu_m, K_s > 0$, feed substrate $S_f > 0$ and $D > D_c = \mu(S_f)$, there are
$\delta, C, \alpha > 0$ such that every solution whose initial value lies in the closed quadrant $X \ge 0$, $S \ge 0$ and
within distance $\delta$ of the washout state $(0, S_f)$, in the maximum norm, exists for all $t \ge 0$ and satisfies

$$\bigl\lVert (X(t), S(t)) - (0, S_f) \bigr\rVert \le C e^{-\alpha t}\,\bigl\lVert (X(0), S(0)) - (0, S_f) \bigr\rVert
\qquad (t \ge 0).$$

This removes the hypothesis "defined for all $t \ge 0$" from the exponential attraction to washout: the global
existence result supplies it for every initial value in the quadrant. The Jacobian at washout is triangular with
eigenvalues $\mu(S_f) - D < 0$ and $-D < 0$, so no general $2 \times 2$ criterion is needed.

## Depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md), for the washout state and $D_c$

## Proof depends on

- [Exponential attraction to chemostat washout above the critical dilution rate](exponential-attraction-to-chemostat-washout.md), for the decay estimate
- [Forward invariance and global existence for the chemostat](chemostat-invariance-and-global-existence.md), for existence on $[0, \infty)$

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, Equations 10.18–10.19 and the washout steady state (pp. 596–597).
