# The least denominator missing from exact-length expansions

Let $D(k)$ be the set of all natural $m\ge2$ appearing among the denominators of some strictly
increasing positive $k$-tuple with reciprocal sum $1$. Let $v(k)$ be the infimum of the natural
numbers $m\ge2$ not in $D(k)$. For every natural $k$, $D(k)$ is finite, a missing denominator exists,
$v(k)\ge2$, $v(k)\notin D(k)$, and every $m$ with $2\le m<v(k)$ belongs to $D(k)$. For $k\ge1$,

$$
v(k)\le 1+k^{2^{k-1}}.
$$

## Proof depends on

- [Denominator bound for exact expansions](../denominator-le-pow-in-expansion-one.md)

## Proof outline

Use the uniform denominator bound to bound $D(k)$ for positive $k$, and handle $k=0$ with the empty expansion set. Identify the first missing integer in a nonempty subset of the naturals; a bound on individual denominators gives the bound on $v(k)$.

## Sources

- [EgyptianFractions.lean — `missing_denominator_semantics`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L98-L106)
