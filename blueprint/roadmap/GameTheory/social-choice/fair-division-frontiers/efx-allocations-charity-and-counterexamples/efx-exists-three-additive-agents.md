# Complete EFX allocations exist for three additive agents

For every instance with three agents having additive valuations $v_i(g) \ge 0$ on a finite set of goods, there exists a complete allocation that is EFX: $v_i(X_i) \ge v_i(X_j \setminus \{g\})$ for all $i, j \in \{1, 2, 3\}$ and $g \in X_j$.

## Proof sketch

Starting from the empty allocation, repeatedly apply the lexicographic improvement step while the pool is nonempty. Each step strictly increases the valuation vector in a fixed lexicographic order, and only finitely many partial allocations exist, so the process ends with an empty pool, i.e. a complete EFX allocation.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Proof depends on

- [Lexicographic improvement step for partial EFX allocations of three agents](efx-three-agents-lexicographic-improvement.md)

## Sources

- B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX Exists for Three Agents", EC 2020; Journal of the ACM 71(1) (2024), arXiv:2002.05119.
