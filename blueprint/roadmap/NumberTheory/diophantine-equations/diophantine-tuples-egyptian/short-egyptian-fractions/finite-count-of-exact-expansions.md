# Finiteness and an upper bound for the exact expansion count

For each natural $k$, let $\mathcal E_k$ be the set of strictly increasing $k$-tuples of positive
integer denominators with reciprocal sum $1$ in $\mathbb Q$. Then $\mathcal E_k$ is finite, and
its cardinal $F(k)$ satisfies

$$
F(k)\le k^{2^k-1}.
$$

The case $k=0$ is allowed: there is no empty expansion of $1$ and $0^0=1$ in the bound.

## Proof depends on

- [Denominator bound in a fixed-length expansion](../denominator-le-pow-in-expansion-one.md)

## Proof outline

Embed the set into the product of the finite intervals $[1,k^{2^i}]$ indexed by $0\le i<k$. Check the empty product and compute the sum of the exponents $\sum_{i<k}2^i=2^k-1$.

## Sources

- [EgyptianFractions.lean — `one_expansions_finite_and_bounded`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L64-L70)
