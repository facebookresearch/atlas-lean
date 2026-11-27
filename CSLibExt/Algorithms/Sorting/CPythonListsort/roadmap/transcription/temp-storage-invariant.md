---
declaration: def
origin: bridged
statement: formalized
lean: CPythonListsort.TempStorageInv
---

# Temporary-storage representation invariant

Define `TempStorageInv storage alloced` beside the raw `MergeState`
transcription. One logical Lean cell represents a temporary key together with
its optional value, while CPython's `temparray` and heap allocation count raw
pointer slots. The invariant therefore records all of the following:

- if `backing = .inline`, then `cells.size = alloced.toNat` and
  `(if hasValues then 2 else 1) * alloced.toNat ≤ MERGESTATE_TEMP_SIZE`;
- if `backing = .heap`, then `cells.size = alloced.toNat`, with the same
  one-or-two-slot multiplier exposing the physical allocation size used by
  `merge_getmem`;
- if `backing = .released`, then the payload-cell array is empty, but there is
  deliberately no relationship between `alloced` and the payload capacity.
  This matches `merge_freemem`, which clears `a.keys` but leaves `alloced` and
  the values-mode metadata stale.

Also define `TempStorage.Live storage` as `backing ≠ .released`. The
representation invariant and liveness are intentionally separate: the
released clause describes a real cleanup state, while the liveness theorem
rules out payload access in that state.

## Depends on

- [`MergeState` and pending runs](merge-state.md)

## Human transcription review

Check that the inline clause counts the fixed 256 raw pointer slots, that keyed
logical cells consume two of them, that the heap clause mirrors
`merge_getmem`'s `multiplier`, and that the released clause does not infer live
capacity from stale `alloced`.

## Sources

- [Verbatim `MergeState`](../../sources/listobject-excerpts.md#merge-state)
- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `merge_freemem`](../../sources/listobject-excerpts.md#merge-freemem)
- [Verbatim `merge_getmem`](../../sources/listobject-excerpts.md#merge-getmem)
