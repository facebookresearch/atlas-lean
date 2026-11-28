# Stars and complete graphs as equilibria of the local connection game

For $\alpha \ge 1$, every profile in which each edge is bought by exactly one endpoint and the formed graph is a star is a pure Nash equilibrium. For $\alpha \le 1$, every profile forming the complete graph with no edge bought twice is a pure Nash equilibrium (Tardos and Wexler, Lemma 19.2). For $\alpha < 1$ every pure Nash equilibrium forms the complete graph and is socially optimal, and for $\alpha < 2$ every pure Nash equilibrium has diameter at most $2$. In every equilibrium, distances are at most $\alpha + 1$.

## Proof sketch

In a star, a leaf buying an extra edge saves exactly $1$ in distance at price $\alpha$, and the center cannot drop edges without disconnecting. In the complete graph, dropping an edge saves $\alpha$ and, with at least $3$ players, raises the distance to its other endpoint from $1$ to $2$; hence, as derived here and not stated by the cited chapter, with at least $3$ players such a profile is a pure Nash equilibrium only if $\alpha \le 1$. If two vertices are at distance $d > \alpha + 1$, buying the edge between them saves at least $d - 1 > \alpha$.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007, Lemma 19.2.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
