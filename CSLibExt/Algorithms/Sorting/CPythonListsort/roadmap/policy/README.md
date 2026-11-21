# Comparator-independent merge policy

This chapter proves safety properties of the transcribed PowerSort policy. No
node in this chapter may assume transitivity, irreflexivity, totality, or any
other ordering law about the comparator. At the steady-state point immediately
after a push, the newest run has no computed node power; the powered prefix
excludes that top run and increases strictly in C array order. Each stored
label is additionally tied to the current geometry: it is exactly the
transcribed `powerloop` result for that run and its right neighbor.
`found_new_run` temporarily computes the former top's power before the caller
pushes the next unpowered run. On the top-level domain
`listlen.toNat ≤ PY_LIST_MAX`, its proof must show adjacent boundary powers
cannot tie, and the top-merge proof must show that absorbing a higher-power
internal boundary preserves the lower surrounding boundary label on the
enlarged geometry. During those merges the candidate power is a ghost value:
the merged top physically retains its stale internal-boundary power, which the
powered-prefix invariant deliberately leaves unconstrained. Exact labels on
the virtual list formed by appending the prospective run are required only at
the `ReadyToPush` stop point, after `setTopPower` stores that candidate. On the
first iteration the pending stack is empty, so
`found_new_run` takes its explicit no-op branch and the pre-push invariant
holds directly. On that selected input domain every computed power lies in
`1 .. 60`; hence there are at most 60 powered runs, and including the unique
unpowered top gives depth at most `61 < MAX_MERGE_PENDING = 64`.
The Lean pending array itself remains unbounded and every push succeeds; these
numbers are derived invariants and trace bounds, never capacity checks in the
definition.

- [Pending-run layout invariant](pending-layout.md)
- [Power range bound](power-range.md)
- [Boundary-power geometry for three consecutive runs](boundary-power-geometry.md)
- [Powered-prefix invariant](stack-powers.md)
- [merge_at preserves pending layout](merge-at-preservation.md)
- [Top merge preserves the powered prefix](merge-top-power-preservation.md)
- [`found_new_run` preserves policy invariants](found-new-run-preservation.md)
- [`MAX_MERGE_PENDING` depth bound](stack-depth.md)
- [Pushing the new run restores the steady-state invariant](push-run-preservation.md)
- [`merge_force_collapse` preserves layout](force-collapse-preservation.md)
