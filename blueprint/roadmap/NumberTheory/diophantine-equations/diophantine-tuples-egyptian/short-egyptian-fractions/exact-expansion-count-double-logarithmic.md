# Double-logarithmic growth of the number of exact expansions

Let $F(k)$ be the natural cardinality (`Set.ncard`, zero for an infinite set) of the set of strictly
increasing positive denominator $k$-tuples with rational reciprocal sum one. There exist real constants $c,C>0$ and a natural $k_0$ such that for all natural $k\ge k_0$,

$$
ck\le\log\log F(k)\le Ck.
$$

## Proof depends on

- [Worst-case minimum length](worst-case-minimum-length.md)
- [Finiteness and cardinal upper bound](finite-count-of-exact-expansions.md)

## Expansion

Use the finite box bound for the upper side. Obtain sufficiently many distinct exact expansions by grouping those with a prescribed denominator, injecting the short fraction expansions, or the equivalent counting construction; verify that a single expansion accounts for only finitely many of the counted markers.

## Sources

- [EgyptianFractions.lean — `counting_double_log_order`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L71-L77)
- [Source exact-one expansion and count](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L25-L33)
