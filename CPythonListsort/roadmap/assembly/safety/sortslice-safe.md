---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.SortSlice.sortslice_primitives_safe
---

# `sortslice` primitive safety

For valid key/value slices, prove that every copy, increment, decrement,
`memcpy`, `memmove`, and advance event emitted by the transcribed movement
primitives stays within both synchronized arrays and preserves their common
extent invariant.

Define the traced movement primitives here from the typed access interface and
prove exact erasure to the transcription. Thread the values-present mode
explicitly: a synchronized-values event is emitted exactly when the C
`values` pointer is present, never inferred from the payload stored at an
individual entry. A global `ValuesModeInvariant` ties that explicit mode to
every entry in each valid slice and is preserved by every successful movement;
in particular, unkeyed mode cannot silently carry a `some` payload while
omitting values-array trace events. Compound operations preserve the source
operation's event order.

The cursor-copy contracts cover distinct destination and source stores, not
only the shared-store specialization: they prove exact erasure, key-before-
values event order, synchronized values-mode preservation, extent preservation,
and separate destination/source cursor bounds. The traced and untraced
`memcpy` evaluators share an explicit provenance/admissibility gate.
Overlapping same-backing calls are outside the modeled C domain and erase to
`none` with no access events; distinct backing remains distinguishable even
when the arrays have equal contents. For admitted calls, exact erasure,
key-before-values phase order, bounds, extent, and values-mode preservation
hold. All main-to-temporary and temporary-to-main merge call sites establish
distinct backing through the
[merge `memcpy` call-site provenance theorem](merge-memcpy-provenance.md),
rather than through an implicit appeal to their C pointer construction.

The `memmove` contract also covers the C helper's full two-slice domain.
Distinct backing has a general two-store traced copy contract; same backing
specializes to the direction-sensitive overlap-safe evaluator. Both branches
prove exact erasure, source-order traces, range safety, values-mode
preservation, and destination extent preservation.

This node also owns the representation boundary needed by the later top-level
assembly. The formalized proof-carrying `ListSortInput` representation has
smart constructors for the two modeled C modes: `ListSortInput.unkeyed` uses
the canonical phantom payload type `PUnit`, `ListSortInput.unkeyedAs` permits
an explicitly selected phantom payload type, and `ListSortInput.keyed` accepts
key/payload pairs. Unkeyed inputs contain only `none` payloads, while keyed
inputs contain a `some` payload at every entry. The public `listSort?` wrapper
delegates exactly to raw `listSortImpl?`, as stated by
`listSort_eq_listSortImpl`, and the formalized theorem
`initialMergeState_valuesMode` transports the validated input fact to
`SortSlice.ValuesModeInvariant state.a.hasValues state.data`; in particular,
the `hasKeyfunc` argument and every payload agree. The `lean:` field above
continues to name this node's unique main primitive-safety declaration;
preservation through the helper and top-level safety nodes is recorded in those
downstream formalized statements rather than claimed here.

Consequently, the generalized raw `listSortImpl?` interface remains available
for transcription and testing, but a safety theorem about an arbitrary raw
`SortSlice` must take `ValuesModeInvariant hasKeyfunc input` explicitly. The
public `listSort?` entry point instead consumes the proof-carrying input built
by an array smart constructor, so that premise is discharged by construction
rather than exposed to callers or silently inferred from individual payloads.

Cursor safety is stated separately from dereference safety. `CursorInRange`
admits the ordinary half-open storage range plus its one-past endpoint.
Incrementing copies prove their returned cursors satisfy it; decrementing
copies require positive starting cursors so they cannot manufacture a
one-before-beginning result. Pure `advance` emits no indexed access, but its
contract takes the actual slice and an explicit start/end range premise and
returns the resulting cursor-range fact for the caller.

## Depends on

- [Array-access trace model](access-trace.md)
- [sortslice model and movement primitives](../../transcription/sortslice-primitives.md)
- [list_sort_impl](../../transcription/list-sort-impl.md)

## Sources

- [Verbatim `sortslice` primitives](../../../sources/listobject-excerpts.md#sortslice-primitives)
