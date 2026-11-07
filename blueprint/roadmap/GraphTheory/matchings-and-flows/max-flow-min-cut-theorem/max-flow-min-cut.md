# Max-flow min-cut theorem

Let $V$ be a finite set, $c : V \times V \to \mathbb{R}$ a capacity
function with $c(u, v) \ge 0$ for all $u, v \in V$, and $s, t \in V$ with $s \ne t$. Then there is
a feasible $s$-$t$ flow $f$ for $c$ whose value is at least the value of every feasible $s$-$t$
flow for $c$ and at most the capacity of every $s$-$t$ cut, and there is an $s$-$t$ cut whose
capacity equals the value of $f$. In other words, the maximum value of a feasible $s$-$t$ flow
equals the minimum capacity of an $s$-$t$ cut.

## Sources

- L. R. Ford and D. R. Fulkerson, Canad. J. Math. 8 (1956), 399-404, DOI 10.4153/CJM-1956-045-5.
