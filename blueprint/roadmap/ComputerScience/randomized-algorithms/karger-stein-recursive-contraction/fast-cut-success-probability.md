# Success probability of FastCut

A fixed minimum cut survives random contraction from $n$ down to $t = \lceil 1 + n/\sqrt{2}\,\rceil$ super-vertices with probability at least $1/2$. Consequently, for a recursion tree of depth at most $d$, FastCut returns a given minimum cut with probability at least $2/(d + 30)$; since the depth is $O(\log n)$, the success probability is $\Omega(1/\log n)$.

## Proof sketch

Survival from $n$ to $t$ is at least $\frac{t(t-1)}{n(n-1)} \ge \frac12$. If $p_d$ lower-bounds success at depth $d$, then $p_{d+1} \ge 1 - (1 - p_d/2)^2 = p_d - p_d^2/4$, and the quadratic potential $1/p_d \le d/2 + O(1)$ follows by induction.

## Depends on

- [The Karger-Stein FastCut recursion](fast-cut-recursion.md)

## Proof depends on

- [Each minimum cut survives with probability at least $2/(n(n-1))$](../karger-s-algorithm/survive-prob-ge.md)

## Sources

- D. R. Karger and C. Stein, "A New Approach to the Minimum Cut Problem", Journal of the ACM 43(4), 1996.
