---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeForceCollapse_preserves_pendingLayout
---

# `merge_force_collapse` preserves layout

Quantify a nonempty state with `PendingLayout state scanned` and a result such
that `mergeForceCollapse? state = some result`, `result.returnCode = 0`, and
`result.fuelExhausted = false`. Prove that `result.state` still satisfies
`PendingLayout` for the same scanned prefix and that its pending stack contains
exactly one run covering that prefix. No ordering hypothesis is used.

This is conditional policy preservation, not fuel adequacy: the separate
[`merge_force_collapse` safety](../assembly/safety/merge-force-collapse-safe.md)
node proves that such a successful non-fuel-exhausted result exists and that
every delegated access is safe.

## Depends on

- [Pending-run layout invariant](pending-layout.md)
- [merge_force_collapse](../transcription/merge-force-collapse.md)

## Proof depends on

- [merge_at preserves pending layout](merge-at-preservation.md)

## Sources

- [Verbatim `merge_force_collapse`](../../sources/listobject-excerpts.md#merge-force-collapse)
