# EFX with high Nash welfare by donating items

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. There always exists a partial allocation $X$, leaving some goods unallocated (donated to charity), that is EFX and whose Nash welfare is at least half of the maximum Nash welfare over all complete allocations; moreover no agent envies the set of donated goods. Such an allocation can be computed from any maximum Nash welfare allocation by removing goods.

## Proof sketch

Start from a maximum Nash welfare allocation and, for each agent $j$ whose bundle causes an EFX violation, shrink $X_j$ to a minimal subset that some agent still values more than her own bundle, using an envy-graph argument to keep shrinking consistent. The local swap inequality of maximum Nash welfare allocations bounds how much each agent loses when shrinking, and a careful matching between shrunk bundles and original bundles shows the product of values decreases by at most a factor $2^n$, i.e. the geometric mean by at most $2$.

## Depends on

- [Partial EFX allocation with an unallocated pool](../efx-allocations-charity-and-counterexamples/partial-efx-allocation-with-pool.md)
- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)
- [Envy-cycle rotation preserves EFX and weakly improves every agent](../efx-allocations-charity-and-counterexamples/envy-cycle-rotation-preserves-efx.md)

## Sources

- I. Caragiannis, N. Gravin, X. Huang, "Envy-Freeness Up to Any Item with High Nash Welfare: The Virtue of Donating Items", EC 2019, arXiv:1902.04319.
