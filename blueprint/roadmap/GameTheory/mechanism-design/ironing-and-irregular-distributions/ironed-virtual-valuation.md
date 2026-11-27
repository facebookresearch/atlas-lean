# Ironed virtual valuation

For a value distribution with density $f$ on $[0, h]$ and virtual valuation $\varphi(v) = v - (1 - F(v))/f(v)$, an *ironed virtual valuation* is a nondecreasing function $\bar\varphi$ such that the tail integrals satisfy $\int_v^h \bar\varphi\, dF \ge \int_v^h \varphi\, dF$ for all $v$, with equality at $v = 0$, and $\bar\varphi$ is locally constant wherever the inequality is strict. For a prior on finitely many values $v_1 < \cdots < v_m$, let $q_j = \Pr[v \ge v_j]$ and $q_{m+1} = 0$; the *revenue curve* is the piecewise-linear function on $[0, 1]$ through the points $(0, 0)$ and $(q_j, v_j q_j)$, and the *ironed virtual value* of $v_j$ is the slope of the least concave majorant of the revenue curve on $[q_{j+1}, q_j]$.

## Depends on

- [Virtual valuation](../optimal-auctions-and-virtual-valuations/virtual-value.md)

## Sources

- Roger B. Myerson, "Optimal Auction Design", Mathematics of Operations Research, 1981.
- Jason D. Hartline and Anna R. Karlin, "Profit Maximization in Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
