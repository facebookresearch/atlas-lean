# Positive lower density of increases of the normalized prime sequence

Let $p_n$ be the $n$th prime with $p_1=2$ and $S=\{n\ge1:p_n/n<p_{n+1}/(n+1)\}$, with real
quotients. The supremum of real $d$ for which

$$
\frac{\#(S\cap\{1,\ldots,N\})}{N}\ge d
$$

for all sufficiently large natural $N$ is positive. Thus the lower natural density of $S$ is
positive. The formulation does not assert that its natural density exists.

## Depends on

- [Lower density](../../../additive-number-theory/natural-and-logarithmic-density/lower-density.md)

## Proof depends on

- [Density of large gaps](positive-lower-density-of-large-gaps.md)

## Expansion

Convert the ratio inequality to $n(p_{n+1}-p_n)>p_n$. Use the prime-number theorem to bound $p_n/(n\log p_n)$ for large $n$, then match the initial-segment counts after removing finitely many indices.

## Sources

- [PrimeGaps.lean — `large_gaps_and_ratio_density`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PrimeGaps.lean#L36-L42)
