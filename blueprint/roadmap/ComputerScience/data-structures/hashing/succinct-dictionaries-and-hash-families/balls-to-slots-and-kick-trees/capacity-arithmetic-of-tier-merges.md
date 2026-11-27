# Capacity arithmetic of tier merges

In the multi-tier cubby layout with tier capacities $r_{j+1} = t_j r_j$, merging $t_j$ full tier-$j$ cubbies produces exactly one full tier-$(j+1)$ cubby, promoting a full tail cubby adds one full base-tier cubby and opens an empty tail, and replacing an item deleted from a full cubby by an item popped from the tail preserves the total number of items and keeps every non-tail cubby full. Consequently, at every time, all but one cubby is completely full and the number of empty slots is less than $r_1$.

## Proof sketch

Each statement is a conservation identity on item counts: a merge concatenates $t_j r_j = r_{j+1}$ items, promotion relabels a tail of $r_1$ items, and replacement moves one item from the tail into the vacated slot.

## Depends on

- [Multi-tier full cubbies with a tail cubby](multi-tier-cubbies.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
