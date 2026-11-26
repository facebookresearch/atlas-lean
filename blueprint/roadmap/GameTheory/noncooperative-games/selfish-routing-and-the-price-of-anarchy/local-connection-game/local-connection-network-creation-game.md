# Local connection (network creation) game

In the *local connection game* with edge price $\alpha \ge 0$ on a finite vertex set $V$, each vertex $u$ chooses a set $s_u$ of other vertices to which it buys edges. The formed graph $G(s)$ joins $u$ and $v$ if $v \in s_u$ or $u \in s_v$. Vertex $u$ pays $\alpha |s_u| + \sum_{v \in V} d_{G(s)}(u, v)$, with distance $+\infty$ for disconnected pairs. The social cost is the sum of all players' costs, $\alpha \cdot |\text{bought edges}| + \sum_{u, v} d(u, v)$; for a graph $H$ the network cost is $\alpha |E(H)| + \sum_{u,v} d_H(u,v)$, ordered pairs counted.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Pure Nash equilibrium of a finite game](../../potential-games/is-pure-nash-2.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
