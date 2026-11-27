# Slab storage with hysteresis has amortized constant reorganization cost

Let a bucket store its $c = qK + r$ items as $q$ full slabs of $K$ items and $r < 2K$ tail items (with $r \ge 1$ whenever $q > 0$), promoting $K$ tail items into a new full slab when $r$ reaches $2K$ and demoting one full slab into the tail when $r$ drops to $0$ with $q > 0$. Then every slab promotion or demotion moves $O(K)$ items, and with the potential $\Phi(q, r) = \alpha \cdot |r - K|$ for any constant $\alpha$ at least the cost of moving one item each insertion and deletion has amortized cost $O(1)$, deterministically and for every hash seed. No slot of a full slab is ever empty.

## Proof sketch

After a promotion or demotion the tail holds exactly $K$ items, where the potential vanishes; reaching the next reorganization requires $K$ single-item operations, each raising the potential by $\alpha$, which pays for the $O(K)$ moves.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)
- [Amortized cost of an operation](../../../amortized-analysis/amortized-cost.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
