# Equilibrium diameter O(√α) and price of anarchy O(√α)

Every pure Nash equilibrium of the local connection game with $\alpha \ge 0$ forms a graph of diameter at most $\sqrt{4\alpha + 1} \le 2\sqrt{\alpha} + 1$, and its social cost is at most $(6\sqrt\alpha + 3)$ times the social cost of every profile.

## Proof sketch

If $d(u, v) = d$, buying the edge $uv$ shortens $u$'s distances to the vertices on the far half of a shortest path by $0 + 2 + \dots$, a total of about $(d^2 - 1)/4$; equilibrium forces this to be at most $\alpha$. Plug the diameter bound into the $3d$ bound.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Proof depends on

- [Social cost of a diameter-d equilibrium is at most 3d times optimal](social-cost-of-a-diameter-d-equilibrium-is-at-most-3d-times-optimal.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
