# Edge count of simplified forward-time tree sequences

Consider a haploid Wright–Fisher population of size $N$ with chromosome length $1$ in Morgans, recorded with [forward-time tables](valid-node-and-edge-tables.md) for $T$ generations and then [simplified](tree-sequence-simplification.md) to the current generation.

- **Unsimplified:** the tables hold $NT$ nodes and $2NT$ edges, so storage grows like $O(N^2)$ over $T \asymp N$ generations.
- **Simplified, $T$ large:** if all marginal trees have coalesced, the expected number of edges is heuristically at most

$$2N + 8N\log N,$$

so storage is $O(N\log N)$.
- **Simplified, general $T$:** with $r(T) = 2N/(T+2)$ the expected number of roots of a marginal tree cut $T$ generations back, the expected number of edges is heuristically at most

$$2N\Big(1 + 4\log\min\Big(N, \tfrac{T+2}{2}\Big)\Big),$$

which grows like $O(N\log T)$.
- **Mutations:** neutral mutations that survive simplification lie on the marginal trees, so their expected number is about $\mu$ times the total tree-sequence area, about $2\mu N\log N$, rather than the $\mu NT$ generated forward in time. A simulation with $M$ mutations is stored in $O(N\log N + M)$ space.

## Depends on

- [Tree sequence simplification](tree-sequence-simplification.md)

## Proof depends on

- [Total branch length of a coalescent genealogy](../../kingman-s-coalescent-and-watterson-s-estimator/total-length.md)

## Expansion

The leftmost marginal tree needs at most $2N - 2$ edges. Each later change of marginal tree ends at most four edges and starts at most four. A change between $x$ and $x + dx$ needs a crossover in one of the $|T_x|$ meioses on the tree, so the expected number of changes is at most the **area**: the sum over edges of segment length times branch length, which equals the mean marginal tree length on a unit chromosome. Under the coalescent approximation the tree has $k$ lineages for an expected $2N/(k(k-1))$ generations and contributes $2N/(k-1)$ to the length. Summing from $k = r(T) + 1$ to $N$ gives about $2N\log(N/r(T))$, or $2N\log N$ when fully coalesced. Inverting $\sum_{k>n} 2N/(k(k-1)) \approx 2(N/n - 1)$ gives $r(T)$. The bounds are crude: they count the root branch and ignore Wright–Fisher discreteness, but the paper reports that they hold well in simulations (its Figure 7).

## Sources

- J. Kelleher, K. R. Thornton, J. Ashander and P. L. Ralph, "Efficient pedigree recording for fast population genetics simulation", *PLoS Computational Biology* 14(11) (2018), e1006581, <https://doi.org/10.1371/journal.pcbi.1006581> (PMC6233923), section "Computational complexity", Equation (1) and Figure 7.
