# Any block-affine polynomials are realized as expected pure-strategy costs

Let $I$ be a finite player set with finite strategy sets $S_i$. For every player $i$ and $a \in S_i$ let $g_{i,a}$ be a real polynomial in the variables $(x_{j,b})$ that is affine in each block $(x_{j,b})_{b \in S_j}$ and does not involve player $i$'s block. Define a game by $c_i(s) = g_{i, s_i}(e_s)$, where $e_s$ is the vertex with $x_{j,b} = 1$ if $b = s_j$ and $0$ otherwise. Then for every (possibly signed) weight vector $x$ whose blocks each sum to $1$, the expected cost of the pure strategy $a$ for player $i$ equals $g_{i,a}(x)$. Consequently the totally mixed Nash equilibria of this game are exactly the positive solutions of $g_{i,a}(x) = g_{i,b}(x)$ with block sums $1$.

## Proof sketch

A polynomial affine in each block is determined by its values at the vertices of the product of simplices, and both sides are multi-affine functions that agree at every vertex, hence everywhere on the affine hull.

## Depends on

- [Expected-cost and deviation-cost polynomials of a finite game](expected-cost-and-deviation-cost-polynomials-of-a-finite-game.md)
- [Totally mixed Nash equilibrium](totally-mixed-nash-equilibrium.md)

## Proof depends on

- [Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs](totally-mixed-nash-equilibria-are-the-positive-profiles-with-equal-pure-strategy.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
