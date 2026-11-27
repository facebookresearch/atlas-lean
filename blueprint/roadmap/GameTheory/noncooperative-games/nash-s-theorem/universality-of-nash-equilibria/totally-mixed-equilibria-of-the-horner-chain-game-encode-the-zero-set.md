# Totally mixed equilibria of the Horner-chain game encode the zero set

Let $F_1, \dots, F_r$ be real polynomials in $n$ variables, not all constant, whose common zeros lie in the open simplex, and let $G$ be the associated Horner-chain game, in which the third player has $D + 1$ strategies. The totally mixed Nash equilibria of $G$ are exactly the profiles in which the first player's weights $x = (a_1, \dots, a_n)$ satisfy $F_j(x) = 0$ for all $j$, the second player's weights are the rescaled Horner values of $x$, and the third player's weights $c_1, \dots, c_D$ equal $1/(D + 1)$ except for $\max(r - n, 0)$ of them, which are constrained only by positivity and the simplex constraint $c_0 + \sum_{i \ge 1} c_i = 1$ with $c_0 > 0$.

## Proof sketch

By block-affine realization the indifference conditions of each player are exactly the prescribed equations. The third player's conditions are the chain equations and $F_j(x) = 0$; solving the chain equations step by step expresses the second player's weights in terms of $x$. The first two players' conditions pin $\min(D, n + D - r)$ of the third player's weights to $1/(D + 1)$; these pinned weights sum to less than $1$, so total mixing remains possible.

## Depends on

- [Datta's three-player Horner-chain game](dattas-three-player-horner-chain-game.md)
- [Totally mixed Nash equilibrium](totally-mixed-nash-equilibrium.md)

## Proof depends on

- [Any block-affine polynomials are realized as expected pure-strategy costs](any-block-affine-polynomials-are-realized-as-expected-pure-strategy-costs.md)
- [Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs](totally-mixed-nash-equilibria-are-the-positive-profiles-with-equal-pure-strategy.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
