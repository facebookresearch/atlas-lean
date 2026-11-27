# The irrationality exponent of pi is two

Among positive real numbers $\nu$, consider those for which infinitely many rationals $r$, in
reduced form with positive denominator $\operatorname{den}(r)\ge2$, satisfy

$$
0<|\pi-r|<\operatorname{den}(r)^{-\nu}.
$$

The supremum of these $\nu$ is $2$. There is no assertion that an exponent exactly $2$ is excluded,
and this is not a convergence claim about the Flint–Hills series.

## Proof depends on

- [Eventual lower bound](pi-rational-approximation-eventual-lower-bound.md)

## Expansion

Use the integer-denominator upper-exponent bound to rule out an infinite set of reduced approximants for any $\nu>2$: handle bounded denominators and finitely many numerators at each such denominator. For the other direction use the infinitely-many-approximants theorem for irrational numbers and irrationality of $\pi$.

## Sources

- [PiExponent.lean — `main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PiExponent.lean#L7-L16)
