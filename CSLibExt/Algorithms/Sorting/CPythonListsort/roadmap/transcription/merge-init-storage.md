---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeInitTemp
---

# `merge_init` temporary-storage setup

Transcribe the temporary-storage projection of `merge_init`. Fresh payload
cells are uninitialized. Both branches select inline backing. In keyed mode,
execute `(list_size + 1).sdiv 2` and the comparison with 128 as signed 64-bit
`Py_ssize_t` operations before capping the logical capacity; set
`hasValues = true`. In unkeyed mode, set `hasValues = false` and the logical
capacity to the 64-bit word for `MERGESTATE_TEMP_SIZE = 256`. The clean keyed
formula `min ((list_size.toNat + 1) / 2) 128` is proved only under the admitted
`list_size.toNat ≤ PY_LIST_MAX` bound in the separate validity node.

This is distinct from the existing adaptive-minrun projection of the same C
constructor. It transcribes field setup only; establishment of
`TempStorageInv` is a separate proof node.

## Depends on

- [Finite-width implementation model](word-model.md)
- [`MergeState` and pending runs](merge-state.md)

## Human transcription review

Check that the keyed addition, signed division, and cap comparison remain
64-bit word operations; then check the ceiling at half of the 256-slot inline
array, the unkeyed full-array capacity, the values-mode flag, and the fact that
both branches initially point into inline storage.

## Sources

- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
