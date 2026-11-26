# Equilibrium diameter at most 4α/√n + 9

Every pure Nash equilibrium of the local connection game with $\alpha \ge 0$ on $n$ vertices forms a graph of diameter at most $4\alpha/\sqrt n + 9$, and its social cost is at most $(12\alpha/\sqrt n + 27)$ times the social cost of every profile. In particular the price of anarchy is $O(1 + \alpha / \sqrt n)$, hence constant for $\alpha = O(\sqrt n)$.

## Proof sketch

Balls of radius about $2\alpha/\sqrt n$ around a vertex must contain many vertices, otherwise buying an edge to a far vertex is profitable; a counting argument over disjoint balls along a long shortest path bounds the diameter.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Proof depends on

- [Social cost of a diameter-d equilibrium is at most 3d times optimal](social-cost-of-a-diameter-d-equilibrium-is-at-most-3d-times-optimal.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Susanne Albers et al., "On Nash Equilibria for a Network Creation Game", Proceedings of the Seventeenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2006.
