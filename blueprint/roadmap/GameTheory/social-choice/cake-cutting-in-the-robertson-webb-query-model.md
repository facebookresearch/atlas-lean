# Cake cutting in the Robertson-Webb query model

The cake is $[0,1]$. Each of $n \ge 1$ agents has a valuation $V_i$, a nonatomic measure on $[0,1]$ with $V_i([0,1]) = 1$, absolutely
continuous with respect to length or at least assigning zero value to points. Robertson–Webb queries are evaluation queries
$\mathrm{eval}_i(x, y) = V_i([x, y])$ and cut queries $\mathrm{cut}_i(x, \alpha) =$ the least $y \ge x$ with $V_i([x, y]) = \alpha$, defined for
$0 \le \alpha \le V_i([x, 1])$ (such $y$ exists by continuity). An allocation assigns to each agent a finite union $A_i$ of intervals, with
disjoint interiors; it is proportional if $V_i(A_i) \ge 1/n$ for every $i$ and envy-free if $V_i(A_i) \ge V_i(A_j)$ for all $i, j$. The query
complexity of a protocol is the worst-case number of queries.

## Expansion

This node states a precise definition. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: the query-counting cost model.
- Statement prerequisite: valuations with piecewise-constant densities given by rational breakpoints and rational
  nonnegative densities, as a finite representation on which queries with rational arguments are answered exactly: an
  evaluation with rational endpoints is a finite sum of products of rational lengths and densities, and a cut with rational
  start $x$ and rational target $\alpha$ returns the least point reaching $\alpha$, which is rational (for $\alpha = 0$ it is
  $x$; across a zero-density stretch it is the left end of that stretch).

## Sources

- Cake Cutting Algorithms — Ariel D. Procaccia (CMU course docs). <http://www.cs.cmu.edu/~arielpro/15896s16/docs/paper10.pdf> Sections 13.2 (the model: normalization, divisibility, nonnegativity) and 13.4 (Robertson–Webb queries).
- CS269I Lecture #20: Fair Division — Tim Roughgarden, Stanford University (2016). <http://theory.stanford.edu/~tim/f16/l/l20.pdf> Definitions 1.1–1.2.
