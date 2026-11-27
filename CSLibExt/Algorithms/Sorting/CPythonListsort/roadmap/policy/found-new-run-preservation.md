---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.foundNewRun_preserves_readyToPush
---

# `found_new_run` preserves policy invariants

Quantify `state`, `scanned`, a prospective `newRun`, and a result. Assume
`state.listlen.toNat ≤ PY_LIST_MAX`, `PendingLayout state scanned`, and
`PoweredPrefix state`, together with every fact used by `ReadyToPush` about the
prospective run:

- `newRun.base = state.basekeys + scanned`;
- `newRun.len.Nonnegative` and `0 < newRun.len.toNat`;
- `scanned + newRun.len.toNat ≤ state.listlen.toNat`; and
- `newRun ∉ state.pending.toList`, with `newRun.power` unconstrained.

If `foundNewRun? state newRun.len.toNat = some result`,
`result.returnCode = 0`, and `result.fuelExhausted = false`, prove
`ReadyToPush result.state scanned newRun`. This node is the policy-preservation
theorem, not the fuel-adequacy theorem: existence of such a successful result,
including safety of every delegated `merge_at`, is discharged by the separate
[`found_new_run` safety](../assembly/safety/found-new-run-safe.md) node. Keeping
that direction avoids a policy/safety dependency cycle.

On an empty stack the conclusion follows from the C function's no-op branch.
On a nonempty stack, the initial candidate `q` is the exact transcribed power
of the current top against `newRun` and remains a fixed ghost value through
every successful top merge. The power-policy portion of the merge-loop
invariant is `PoweredPrefix` plus that ghost equality; the induction also
carries `PendingLayout`, the list-size bound, and the prospective-run frame
facts needed to justify each next call. The current top's physical stored
power may remain stale.

At the stop point, a preceding internal power `pInternal` and the fixed `q`
are powers of adjacent boundaries. The false strict guard gives
`pInternal ≤ q`; use the boundary-power geometry theorem, rather than stored
field assumptions, to obtain `pInternal ≠ q` and hence
`pInternal < q`. Only then does `setTopPower` write `q` on the current top,
establishing exact labels on the virtual list
`result.state.pending.toList ++ [newRun]` and the full `ReadyToPush` result.
The explicit list-length premise supplies the quotient-bit, no-wrap, and power
range domains. No property of the comparator is assumed.

## Depends on

- [Pending-run layout invariant](pending-layout.md)
- [Powered-prefix invariant](stack-powers.md)
- [found_new_run](../transcription/found-new-run.md)

## Proof depends on

- [powerloop terminating-result characterization](../bit-equivalence/powerloop-result.md)
- [Power range bound](power-range.md)
- [Top merge preserves the powered prefix](merge-top-power-preservation.md)
- [Boundary-power geometry for three consecutive runs](boundary-power-geometry.md)

## Sources

- [Verbatim `found_new_run`](../../sources/listobject-excerpts.md#found-new-run)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Verbatim `list_sort_impl`](../../sources/listobject-excerpts.md#list-sort-impl)
- [Verbatim list-allocation guard](../../sources/listobject-excerpts.md#list-resize)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
