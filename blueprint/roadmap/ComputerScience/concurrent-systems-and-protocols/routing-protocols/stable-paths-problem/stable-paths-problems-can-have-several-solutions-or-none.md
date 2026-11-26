# Stable paths problems can have several solutions or none

A [stable paths problem](the-stable-paths-problem.md) need not have exactly one solution.

1. (DISAGREE) On the triangle with nodes $0, 1, 2$, let node $1$ permit $(1\,2\,0)$ ranked above $(1\,0)$ and node $2$ permit $(2\,1\,0)$ ranked above $(2\,0)$. Then $((1\,2\,0), (2\,0))$ and $((1\,0), (2\,1\,0))$ are both stable, and no other path assignment is.
2. (A cyclic gadget) On the wheel with hub $0$ and rim nodes $1, 2, 3$, let each rim node $i$ permit its direct path $(i\,0)$ and the path $(i\,j\,0)$ through its clockwise neighbour $j = i + 1 \bmod 3$, ranked above the direct path. Then no path assignment is stable.

**Proof of 2.** In a stable assignment no rim node gets $\epsilon$, since its direct path is always available. If no rim node used its direct path, every node would use $(i\,j\,0)$, which needs $\pi(j) = (j\,0)$. So some $i$ has $\pi(i) = (i\,0)$; its counter-clockwise neighbour $h$ then has its preferred path $(h\,i\,0)$ available and uses it; the third node $g$ cannot use $(g\,h\,0)$, so $\pi(g) = (g\,0)$; but $g$ is the clockwise neighbour of $i$, so $(i\,g\,0)$ is available and preferred by $i$, contradicting $\pi(i) = (i\,0)$.

## Depends on

- [The stable paths problem](the-stable-paths-problem.md)

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section III, Fig. 3 (DISAGREE and its two solutions) and Fig. 2(d) (BAD GADGET, a four-node instance with the same cyclic preferences, stated there to have no solution).
