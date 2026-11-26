# Social optima of the local connection game

Let $n = |V|$. For $\alpha \ge 2$ the star minimizes network cost, with cost $\alpha (n-1) + 2(n-1)^2$; for $0 \le \alpha \le 2$ the complete graph minimizes network cost. More precisely, a connected graph attains the lower bound $\alpha|E| + 2n(n-1) - 2|E|$ iff its diameter is at most $2$; hence for $0 \le \alpha < 2$ the complete graph is the unique optimum, for $\alpha > 2$ the optima are exactly the stars, and for $\alpha = 2$ the optima are exactly the connected graphs of diameter at most $2$.

## Proof sketch

In a connected graph every pair at distance $1$ is an edge and every other pair is at distance at least $2$, giving the lower bound; equality holds iff all distances are at most $2$. Minimizing $(\alpha - 2)|E|$ over diameter-$2$ graphs gives the complete graph or the star.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
