# Mixed and totally mixed Nash equilibrium sets are semialgebraic

Let $G$ be a finite game, viewed as a point set in $\mathbb{R}^{\sum_i |S_i|}$. The set of mixed Nash equilibria of $G$ equals the common nonnegativity set of finitely many polynomials: $x_{i,a} \ge 0$, $\pm(\sum_a x_{i,a} - 1) \ge 0$ and $D_{i,a}(x) - E_i(x) \ge 0$ for all $i, a$. Hence it is a basic closed semialgebraic set. The set of totally mixed Nash equilibria is cut out by the strict inequalities $x_{i,a} > 0$ together with the polynomial equations $\sum_a x_{i,a} = 1$ and $D_{i,a}(x) = D_{i,b}(x)$, so it is semialgebraic.

## Proof sketch

A mixed profile is a Nash equilibrium iff no pure deviation lowers cost, i.e. $D_{i,a} \ge E_i$ on the simplex product; these are polynomial inequalities by the definition of the cost polynomials. The totally mixed case uses the indifference characterization.

## Depends on

- [Expected-cost and deviation-cost polynomials of a finite game](expected-cost-and-deviation-cost-polynomials-of-a-finite-game.md)
- [Totally mixed Nash equilibrium](totally-mixed-nash-equilibrium.md)
- [Semialgebraic set](../../../../Logic/model-theory/wilkie-s-conjecture/is-semialgebraic.md)

## Proof depends on

- [Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs](totally-mixed-nash-equilibria-are-the-positive-profiles-with-equal-pure-strategy.md)
- [Pure deviations suffice to check a mixed Nash equilibrium](../pure-deviations-suffice-for-mixed-nash-equilibrium.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
