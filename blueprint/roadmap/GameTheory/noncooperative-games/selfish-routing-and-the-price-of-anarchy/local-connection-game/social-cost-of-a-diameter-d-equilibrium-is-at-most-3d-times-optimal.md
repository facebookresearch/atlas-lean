# Social cost of a diameter-d equilibrium is at most 3d times optimal

If $s$ is a pure Nash equilibrium of the local connection game with $\alpha \ge 0$ and the formed graph has diameter $d$, then the social cost of $s$ is at most $3d$ times the social cost of every connected profile (and every profile, in extended reals).

## Proof sketch

Distance costs are at most $d\, n(n-1)$, and $n(n-1)$ is a lower bound on the distance cost of every connected profile. Bridge edges number at most $n-1$ and cost at most $\alpha(n-1)$. A non-bridge edge bought by $u$ is critical for a set of targets whose distances would grow without it; these sets are disjoint across $u$'s edges and the equilibrium condition bounds their total price by $2d(n-1)$.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
