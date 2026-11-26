# Uniformly bounded components of the bounded-step Gaussian-prime graph

For each real $D$, form the graph on all irreducible elements of $\mathbb Z[i]$, joining distinct
$z,w$ when $|z-w|\le D$. There is a natural $B$ depending only on $D$ such that every connected
component is finite with at most $B$ vertices. With the same $B$, if
$z_0,\ldots,z_{n-1}$ are distinct irreducibles and every successive distance is at most $D$,
then $n\le B$. Primes on axes and all associates are included.

## Expansion

Derive a bound uniform in the starting vertex from the finite lattice-step sieve: record the dyadic prime batches, smoothing bounds and accumulated sieve rate that exceeds the logarithm of the number of allowed steps. Transfer the resulting bound for injective paths to finite graph components via finite local degree, treating $D<1$ separately.

## Sources

- [GaussianMoat.lean — `fullMain`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianMoat.lean#L36-L38)
