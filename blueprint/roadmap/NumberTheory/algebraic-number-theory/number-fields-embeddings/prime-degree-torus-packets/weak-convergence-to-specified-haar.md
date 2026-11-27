# Prime-degree torus packets converge to any specified Haar probability

Fix a prime $n\ge5$ and a sequence of totally real degree-$n$ number fields $K_i$, full $\mathbb Z$-lattices $M_i$ spanning $K_i$ over $\mathbb Q$, and orderings $\sigma_i$ of all real embeddings.
Assume the multiplier discriminants of $M_i$ tend to $+\infty$. Given any right-invariant Haar
probability $m$ on $X_n$, each complete volume-weighted packet measure $\mu_i$ is a probability and
$\int f\,d\mu_i\to\int f\,dm$ for every bounded continuous real $f$ on $X_n$.

## Depends on

- [Complete packet measure and multiplier discriminant](complete-packet-measure.md)

## Proof depends on

- [Existence of a Haar limit and tightness](weak-convergence-and-tightness.md)

## Expansion

Prove uniqueness of the normalized invariant measure on this quotient and identify the Haar witness in the convergence theorem with the specified probability. Do not impose that the $K_i$, orders, or local homothety types are fixed.

## Sources

- [DukePrimeDegree.lean — `prime_degree_packet_measures_tendsto_haar_unconditional`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DukePrimeDegree.lean#L213-L228)
