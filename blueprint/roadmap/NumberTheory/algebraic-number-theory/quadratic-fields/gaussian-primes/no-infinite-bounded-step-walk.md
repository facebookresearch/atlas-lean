# No injective bounded-step walk through Gaussian primes

For every real $D$, there is no injective sequence $(z_t)_{t\ge0}$ of irreducibles of $\mathbb Z[i]$
with $|z_{t+1}-z_t|\le D$ for every natural $t$. All associates and primes on axes are allowed.

## Proof depends on

- [Uniform bounds for finite walks](bounded-components-of-gaussian-prime-graph.md)

## Proof outline

Restrict any proposed infinite walk to a length exceeding the uniform bound for finite injective walks at the same step size. Do not replace irreducible elements by their associate classes.

## Sources

- [GaussianMoat.lean — `fullMain`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianMoat.lean#L36-L38)
