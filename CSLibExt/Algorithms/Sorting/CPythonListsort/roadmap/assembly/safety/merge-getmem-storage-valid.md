---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeGetmem_storage_valid
---

# `merge_getmem` establishes live temporary capacity

Under the version-one successful-allocation abstraction, prove the two
non-rejecting `merge_getmem` paths from a state satisfying `TempStorageInv` and
`TempStorage.Live`:

- a request with `need ≤ alloced` reuses the live backing unchanged;
- given a larger nonnegative request and the explicit premise
  `need.toNat ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / multiplier`, releases
  old heap backing (while inline backing remains inline during
  `merge_freemem`), allocates `multiplier * need.toNat` raw pointer slots, and
  returns live heap backing with
  `cells.size = alloced.toNat = need.toNat` and `TempStorageInv`
  re-established.

The internal released state between the free and successful allocation may
read the mode metadata needed to compute or apply `multiplier`, but it may not
read or write a payload cell and is not observable across a merge-operation
boundary. Requiring live input is essential: stale `alloced` in a released
state must not make the reuse branch appear valid.

The formal result exports the exact intermediate `merge_freemem` state on the
growth path.  Inline backing remains unchanged; live heap backing becomes
released with an empty payload while `alloced` and values mode remain stale,
and `TempStorageInv` still holds.  It also frames every non-storage
`MergeState` field.  A concrete regression exhibits a fabricated released
state whose stale capacity makes raw `mergeGetmem` report `.reused`; that state
satisfies `TempStorageInv` but not `TempStorage.Live`, machine-checking why the
live-input premise is indispensable.

The allocation inequality is a premise of this function-local theorem, not a
consequence of `TempStorageInv` or liveness. For valid `merge_at` executions it
is discharged, with the exact list-size and multiplier constants, by the
[`merge_getmem` call-site request bound](merge-getmem-request-bound.md).

## Depends on

- [The `merge_getmem` transcription](../../transcription/merge-getmem.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)

## Proof depends on

- [`merge_freemem` preserves temporary-storage validity](merge-freemem-storage-valid.md)

## Sources

- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `MERGE_GETMEM`](../../../sources/listobject-excerpts.md#merge-getmem-macro)
- [Modeling boundary](../../../sources/toplevel-theorems.md#explicit-scope-boundary)
