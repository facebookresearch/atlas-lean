---
article_id: af_ec4342a38e9496a452abce0e
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.LadderAdj
---

# Ladder Adj

Ladder adjacency: perimeter-neighbour edges plus all vertical rung pairs.
   `v_i` sits at index `i - 1` and `u_i` at index `2 * n - i`, so rung pairs
   satisfy `i.val + j.val = 2 * n - 1`. The two corner rungs are also
   perimeter edges.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.ConsecutiveCyclicPrimeLabeling](../../../../../sources/v2/MathlibExt.md)
