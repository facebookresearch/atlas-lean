---
article_id: af_3654908535465dfdaa386681
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsConsecutiveCyclicPrimeLabeling
---

# Is Consecutive Cyclic Prime Labeling

A consecutive cyclic prime labeling of `P_n x P_2`: `0 < n` and the rotation
   of the labels `1, ..., 2 * n` by `offset` along the perimeter order gives
   relatively prime labels to every adjacent pair. If 1 is on `v_i` the order
   runs `v_i, ..., v_n, u_n, ..., u_1, v_1, ..., v_{i - 1}` (and analogously
   from `u_i`); here `offset` is the rotation placing the labels cyclically.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ladder Adj](ladder-adj.md)
- [Cyclic Label](cyclic-label.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.ConsecutiveCyclicPrimeLabeling](../../../../../sources/v2/MathlibExt.md)
