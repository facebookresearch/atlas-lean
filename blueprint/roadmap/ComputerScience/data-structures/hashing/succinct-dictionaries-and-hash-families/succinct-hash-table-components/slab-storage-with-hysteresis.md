# Slab storage with hysteresis has amortized constant reorganization cost

Let a bucket store its $c = qK + r$ items as $q$ full slabs of $K$ items and $r < 2K$ tail items (with $r \ge 1$ whenever $q > 0$), promoting $K$ tail items into a new full slab when $r$ reaches $2K$ and demoting one full slab into the tail when $r$ drops to $0$ with $q > 0$. Then every slab promotion or demotion moves $O(K)$ items, and with the potential $\Phi(q, r) = \alpha \cdot |r - K|$ for any constant $\alpha$ at least the cost of moving one item each insertion and deletion, reorganization included, has amortized cost at most $1 + \alpha$, deterministically and for every hash seed. Since $\Phi \ge 0$ and an empty bucket has potential $\alpha K$, any $t$ operations starting from an empty bucket cost at most $(1 + \alpha) t + \alpha K$ in total. No slot of a full slab is ever empty.

The slab layout follows the slab decomposition of resizable arrays (Lemma 2.3 of Bender, Farach-Colton, J. Kuszmaul and W. Kuszmaul), and the hysteresis is the standard potential argument for dynamic tables (Cormen et al., Section 17.4); the combination is a variant that is not in the cited papers.

## Proof sketch

After a promotion or demotion the tail holds exactly $K$ items, where the potential vanishes; reaching the next reorganization requires $K$ single-item operations, each raising the potential by at most $\alpha$, and the potential $\alpha K$ released by the reorganization pays for its $K$ moves.

## Depends on

- [Partition hash table with fingerprint-indexed buckets](../succinct-hash-tables/partition-hash-table.md)
- [Amortized cost of an operation](../../../amortized-analysis/amortized-cost.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), pp. 363-373, 2024 (Lemma 2.3).
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009 (Sections 17.3 and 17.4).
