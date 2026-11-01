---
article_id: af_a3d69157c129f277dceceb83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.mesh_partition_congruence_lift
---

# Mex Partition Congruence Lift

Lifting of partition congruences to mex partition functions.

If `m ∣ p (a*n+b)` for all `n` (with `p` the ordinary partition number),
then for every `t ≥ 1` the same congruence holds for the mex partition
functions `p_{at,at}` and `p_{2at,at}`: `μ` encodes the `mex_{A,a}` value
(smallest positive integer `≡ a (mod A)` missing from the parts) and the
filter keeps partitions with `mex ≡ a (mod 2A)`. The offset `b` is taken in
`ℕ` with `b < a`, so `hbase` covers the whole residue class of `b` mod `a`;
for `b ≥ a` the lift needs `p` at arguments below `b`, which `hbase` does not
cover.

This is the general lift; the same paper's Ramanujan corollary for
`p = 5, 7, 11` (label ramanujan-cong) is a separate module.

Proof: Following the Andrews-Newman mex decomposition used by Barman and Singh, remove one copy
of every forced earlier mex candidate. The exact-mex fibers then telescope, while every removed
prefix sum remains a multiple of `a`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift](../../../../../../../sources/v2/MathlibExt.md)
- Rupam Barman and Ajit Singh, "Mex-Related Partition Functions of Andrews and Newman," Journal of Integer Sequences 24 (2021), Article 21.6.3, Theorem (label thm2), lines 172–182, https://cs.uwaterloo.ca/journals/JIS/VOL24/Barman/barman3.tex
