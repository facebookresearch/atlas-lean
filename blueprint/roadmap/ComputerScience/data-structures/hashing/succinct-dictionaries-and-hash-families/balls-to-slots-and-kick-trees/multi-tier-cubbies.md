# Multi-tier full cubbies with a tail cubby

In the $k$-kick tree dictionary, keys are stored in *cubbies*: fixed-size groups of slots. All cubbies except one *tail cubby* are completely full (no empty slot), arranged in tiers with capacities $r_0 < r_1 < \dots$ where $t_j r_j = r_{j+1}$ for tier ratios $t_j$, and $t_j$ full tier-$j$ cubbies merge into one tier-$(j+1)$ cubby. Insertions go to the tail cubby, which is promoted to a full cubby when it fills; a deletion from a full cubby is refilled by moving an item from the tail cubby, keeping every non-tail cubby full and the total item count unchanged.

## Depends on

- [k-kick tree balls-to-slots scheme](k-kick-tree.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
