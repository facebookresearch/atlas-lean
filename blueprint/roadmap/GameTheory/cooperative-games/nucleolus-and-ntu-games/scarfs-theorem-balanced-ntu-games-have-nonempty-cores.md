# Scarf's theorem: balanced NTU games have nonempty cores

Every balanced NTU game in which each $V(S)$ is closed, comprehensive (closed under decreasing coordinates in $S$) and nonempty, each $V(\{i\})$ is bounded above in coordinate $i$, so that $v_i = \max\{x_i : x \in V(\{i\})\}$ is finite, and each $V(S)$ has bounded $S$-coordinates on the individually rational region $\{x : x_i \ge v_i \text{ for all } i \in S\}$ has a nonempty core.

## Proof sketch

Shapley's proof applies a KKMS-type covering lemma on the simplex: label each point of a scaled simplex by the coalitions that can achieve it, use balancedness to find a point in the intersection of the sets indexed by a balanced family, and conclude that this point is feasible for the grand coalition and unblocked.

## Depends on

- [Nontransferable-utility cooperative game and its core](nontransferable-utility-cooperative-game-and-its-core.md)

## Sources

- Herbert E. Scarf, "The Core of an N Person Game", Econometrica, 1967.
- Lloyd S. Shapley, "On Balanced Games Without Side Payments", Mathematical Programming, Academic Press, 1973.
