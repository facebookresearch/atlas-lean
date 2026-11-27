# Monderer–Shapley cycle characterization of exact potential games

Let $G$ be a game with finitely many players and arbitrary strategy sets. The following are equivalent:

1. $G$ admits an exact potential;
2. $I(\gamma) = 0$ for every closed unilateral path $\gamma$;
3. $I(\gamma) = 0$ for every simple closed unilateral path;
4. $I(\gamma) = 0$ for every simple closed unilateral path of length $4$;
5. for all distinct players $i \ne j$, all profiles $s$ and all $a, a' \in S_i$, $b, b' \in S_j$, the four-cycle $(a, b) \to (a', b) \to (a', b') \to (a, b') \to (a, b)$ (others fixed at $s$) has zero path integral.

## Proof sketch

An exact potential makes every path integral telescope. Conversely, fix a base profile and define $\Phi(s)$ as the integral of any unilateral path from the base to $s$; vanishing integrals on four-cycles allow any two such paths to be transformed into each other by local swaps, so $\Phi$ is well defined and is an exact potential.

## Depends on

- [Unilateral deviation paths and their path integral](unilateral-deviation-paths-and-their-path-integral.md)
- [Exact potential](../is-exact-potential.md)

## Sources

- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior, 1996.
