# Totally mixed equilibria of the Horner-chain game encode the zero set

Let $F_1, \dots, F_r$ be real polynomials in $n$ variables and let $G$ be the associated Horner-chain game with $m$ strategies for the third player. The totally mixed Nash equilibria of $G$ are exactly the profiles in which the first player's weight vector $x$ lies in the open simplex and satisfies $F_j(x) = 0$ for all $j$ (after the fixed rescaling), the second player's weights are the rescaled Horner values of $x$, and the third player's weights are fixed at $1/m$, apart from $\max(m - n, 0)$ coordinates that are unconstrained.

## Proof sketch

By block-affine realization the indifference conditions of each player are exactly the prescribed equations; solving the chain equations step by step expresses the second and third players' weights in terms of $x$.

## Depends on

- [Datta's three-player Horner-chain game](dattas-three-player-horner-chain-game.md)
- [Totally mixed Nash equilibrium](totally-mixed-nash-equilibrium.md)

## Proof depends on

- [Any block-affine polynomials are realized as expected pure-strategy costs](any-block-affine-polynomials-are-realized-as-expected-pure-strategy-costs.md)
- [Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs](totally-mixed-nash-equilibria-are-the-positive-profiles-with-equal-pure-strategy.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
