# Probabilistic completeness of RRT

Let the free space $F$ be a subset of $[0,1]^d$, let samples be i.i.d. uniform on $[0,1]^d$, let the steering parameter be $\eta > 0$, and let the goal region be the ball
$B_{\delta_{\mathrm{goal}}}(x_{\mathrm{goal}})$. Suppose there is a valid path from $x_{\mathrm{init}}$ to $x_{\mathrm{goal}}$ of length $L$ with
clearance $\delta_{\mathrm{clear}} > 0$ (the ball of radius $\delta_{\mathrm{clear}}$ around each of its points lies in $F$), and let $\delta = \min(\delta_{\mathrm{clear}}, \delta_{\mathrm{goal}})$ and $\nu = \min(\delta, \eta)$. Then the
probability that the geometric RRT has not reached the goal region after $k$ iterations is at most $a e^{-bk}$ for constants
$a, b > 0$ depending on the problem (Kleinbort et al., Theorem 1; Karaman and Frazzoli state the result as their Theorem 16, attributed to LaValle and Kuffner). The proof covers the path by
$m = \lceil 5L/\nu \rceil$ balls of radius $\nu/5$ and uses a bound for Bernoulli trials with success probability the volume of
such a ball. The kinodynamic case and its erratum are separate.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Robust feasibility, probabilistic completeness and asymptotic optimality.

## Sources

- Probabilistic completeness of RRT for geometric and kinodynamic planning with forward propagation — M. Kleinbort, K. Solovey, Z. Littlefield, K. E. Bekris, D. Halperin, arXiv:1809.07051v2 (31 May 2022), Sec. III.B, Lemma 1 and Theorem 1; corrigendum note on the kinodynamic Theorem 2 and Lemma 3. <https://arxiv.org/pdf/1809.07051>
- Sampling-based Algorithms for Optimal Motion Planning — S. Karaman, E. Frazzoli. <https://people.eecs.berkeley.edu/~pabbeel/cs287-fa15/optreadings/rrtstar.pdf> Theorem 16 (probabilistic completeness of RRT, attributed to LaValle and Kuffner, 2001).
