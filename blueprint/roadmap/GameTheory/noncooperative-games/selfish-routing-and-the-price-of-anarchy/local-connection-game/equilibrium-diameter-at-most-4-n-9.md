# Equilibrium diameter at most 4α/√n + 9

Every pure Nash equilibrium of the local connection game with $\alpha \ge 0$ on $n$ vertices forms a graph of diameter at most $4\alpha/\sqrt n + 9$ (Tardos and Wexler, proof of Theorem 19.6). Combined with the $O(d)$ bound on the social cost of a diameter-$d$ equilibrium, the price of anarchy is $O(1 + \alpha / \sqrt n)$, hence constant for $\alpha = O(\sqrt n)$ (Tardos and Wexler, Theorem 19.6).

## Proof sketch

Let $u, v$ be at distance $d$ and let $B$ be the ball of radius $d' = (d - 1)/4$ around $u$. If $v$ buys the edge $vu$ it saves at least $(d - 1)|B|/2$, so $(d - 1)|B|/2 \le \alpha$; if $u$ buys an edge to a suitable vertex on the boundary of $B$ it saves enough to force $|B| \ge n(d' - 1)/(2\alpha)$. Together these give $\alpha^2 \ge n(d' - 1)^2$, hence the diameter bound.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Proof depends on

- [Social cost of a diameter-d equilibrium is at most 3d times optimal](social-cost-of-a-diameter-d-equilibrium-is-at-most-3d-times-optimal.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007, Lemma 19.4 and Theorem 19.6.
- Susanne Albers et al., "On Nash Equilibria for a Network Creation Game", Proceedings of the Seventeenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2006.
