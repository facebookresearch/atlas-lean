# Greedy breakpoint algorithm for sorting by reversals

This node covers the following result. Let $\pi = (\pi_1, \dots, \pi_n)$ be an unsigned permutation of $\{1, \dots, n\}$, framed by $\pi_0 = 0$ and $\pi_{n+1} = n + 1$. A breakpoint of $\pi$ is a pair of adjacent positions $(i, i+1)$ with $0 \le i \le n$ and $|\pi_{i+1} - \pi_i| \ne 1$, and $\Phi(\pi)$ is the number of breakpoints; the identity is the only permutation with $\Phi = 0$. A strip is a maximal interval of positions $[i, j]$ containing no breakpoint, that is, $(i-1, i)$ and $(j, j+1)$ are breakpoints (where these pairs exist) and none lies between them. A strip is decreasing if $\pi_i, \dots, \pi_j$ is decreasing; a one-element strip counts as decreasing, except that the frame elements $\pi_0$ and $\pi_{n+1}$ always lie in increasing strips. A reversal reverses a block $\pi_k, \dots, \pi_l$ with $1 \le k \le l \le n$; it removes $m$ breakpoints if it lowers $\Phi$ by $m$. Consider the greedy algorithm that, while $\pi$ has a breakpoint, applies a reversal removing the most breakpoints, resolving ties among reversals that remove one breakpoint in favour of reversals that leave a decreasing strip. It sorts every $\pi$ into the identity using at most $\Phi(\pi)$ reversals.

## Expansion

A good expansion replaces this node by planned pages beside it, each citing the source below:

1. Framed unsigned permutations, breakpoints, strips and decreasing strips, and reversals with their effect on the number of breakpoints.
2. The greedy algorithm with its tie-breaking rule.
3. The bound of at most $\Phi(\pi)$ reversals.

Nothing beyond the statement above is claimed here.

## Sources

- J. Kececioglu and D. Sankoff, Exact and approximation algorithms for sorting by reversals, with application to genome rearrangement, Algorithmica 13 (1995), 180–210. <https://doi.org/10.1007/BF01188586>
