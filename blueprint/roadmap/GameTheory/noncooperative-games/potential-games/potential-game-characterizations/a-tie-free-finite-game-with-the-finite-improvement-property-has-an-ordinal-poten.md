# A tie-free finite game with the finite improvement property has an ordinal potential

Let $G$ be a game with finitely many strategy profiles that has the finite improvement property and has no unilateral cost ties: for every player $i$, profile $s$ and distinct $a, b \in S_i$, $c_i(a, s_{-i}) \ne c_i(b, s_{-i})$. Then $G$ admits an ordinal potential.

## Proof sketch

Let $\Phi(s)$ be the number of profiles reachable from $s$ by improvement paths; well-foundedness makes this finite and strictly decreasing along improvements. Absence of ties makes every unilateral change either an improvement or the reverse of one, so $\Phi$ is an ordinal potential.

## Depends on

- [Ordinal, generalized ordinal and weighted potentials](ordinal-generalized-ordinal-and-weighted-potentials.md)
- [Finite improvement property](../well-founded-improving-move.md)

## Proof depends on

- [Generalized ordinal potentials give the finite improvement property](generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior, 1996.
