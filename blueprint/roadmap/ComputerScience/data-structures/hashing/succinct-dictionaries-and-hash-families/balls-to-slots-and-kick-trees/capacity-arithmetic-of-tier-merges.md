# Capacity arithmetic of tier merges

In the multi-tier cubby layout with tier capacities $r_{j+1} = t_j r_j$, merging $t_j$ full $j$-tiered cubbies produces exactly one full $(j+1)$-tiered cubby, and splitting one full $(j+1)$-tiered cubby produces exactly $t_j$ full $j$-tiered cubbies; closing a full tail turns it into one more full 1-tiered cubby and opens an empty tail; and refilling a slot vacated by a deletion with an item moved from the tail keeps every non-tail cubby full while the total number of items drops by exactly the one deleted. Consequently, at every time, all cubbies except the tail are completely full, and the number of empty slots in a facility is at most $r_1$ (the capacity of the tail).

## Proof sketch

Each statement is a conservation identity on item counts: a merge or split redistributes $t_j r_j = r_{j+1}$ items, closing the tail relabels its $r_1$ items, and a refill moves one item from the tail into the vacated slot. Every operation preserves the saturation invariant, so only the tail can have empty slots, and it has at most $r_1$ of them.

## Depends on

- [Multi-tier full cubbies with a tail cubby](multi-tier-cubbies.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 5.2).
