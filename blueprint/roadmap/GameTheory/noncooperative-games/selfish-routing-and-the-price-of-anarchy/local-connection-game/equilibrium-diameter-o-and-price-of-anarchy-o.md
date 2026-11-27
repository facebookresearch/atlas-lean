# Equilibrium diameter O(√α) and price of anarchy O(√α)

Every pure Nash equilibrium of the local connection game with $\alpha \ge 0$ forms a graph of diameter $O(1 + \sqrt\alpha)$, and the price of anarchy is $O(1 + \sqrt\alpha)$ (Tardos and Wexler, Theorem 19.5, which states $O(\sqrt\alpha)$ for the nontrivial range $\alpha \ge 1$).

## Proof sketch

If $d(u, v) = d$, buying the edge $uv$ shortens $u$'s distances to the vertices on the far half of a shortest path by $0 + 2 + \dots$, a total of at least $(d^2 - 1)/4$; equilibrium forces this to be at most $\alpha$, so $d = O(1 + \sqrt\alpha)$. Plug the diameter bound into the $O(d)$ bound on the social cost.

## Depends on

- [Local connection (network creation) game](local-connection-network-creation-game.md)

## Proof depends on

- [Social cost of a diameter-d equilibrium is at most 3d times optimal](social-cost-of-a-diameter-d-equilibrium-is-at-most-3d-times-optimal.md)

## Sources

- Eva Tardos and Tom Wexler, "Network Formation Games and the Potential Function Method", Algorithmic Game Theory, Cambridge University Press, 2007, Lemma 19.4 and Theorem 19.5.
- Alex Fabrikant et al., "On a Network Creation Game", Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing, 2003.
