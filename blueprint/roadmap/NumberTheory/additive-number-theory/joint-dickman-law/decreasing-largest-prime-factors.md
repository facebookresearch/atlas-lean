# Natural density of the decreasing largest-prime-factor ordering

Let $P^+(n)$ be the greatest prime factor of $n\ge2$. For real $X\to+\infty$,

$$
\frac{\#\{2\le n\le\lfloor X\rfloor:\ P^+(n+1)<P^+(n)\}}{X}\longrightarrow\tfrac12.
$$

The comparison is strict and uses the primes themselves, not their normalized logarithms.

## Depends on

- [Natural density](../natural-and-logarithmic-density/has-density.md)

## Proof depends on

- [Joint Dickman law](joint-density.md)

## Expansion

Pass from the joint rectangle limits to the ordering region. Control the shrinking diagonal strip using continuity of the limiting law and check that changing the normalization base from $n+1$ to $n$ does not move mass across that region.

## Sources

- [JointDickman.lean — `decreasing_order`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/JointDickman.lean#L57-L62)
