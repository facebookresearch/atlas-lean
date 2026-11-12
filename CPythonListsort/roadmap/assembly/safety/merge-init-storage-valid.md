---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeInitTemp_inv
---

# `merge_init` establishes temporary-storage validity

For `list_size.toNat ≤ PY_LIST_MAX`, prove that both branches of the
temporary-storage constructor establish `TempStorageInv`, and bridge its exact
signed 64-bit computation to the sharper source facts needed by consumers:

- keyed initialization has inline backing, `hasValues = true`, and
  `alloced.toNat = min ((list_size.toNat + 1) / 2) 128`;
- unkeyed initialization has inline backing, `hasValues = false`, and
  `alloced.toNat = 256`.

The supporting regression theorem
`CPythonListsort.impossibleInlineKeyed255_not_inv` proves that the deliberately
exhibited state `backing = .inline`, `hasValues = true`, and `alloced = 255`
violates `TempStorageInv`. This pins the reason for the invariant and prevents
the inline-capacity clause from being weakened silently.

## Depends on

- [`merge_init` temporary-storage setup](../../transcription/merge-init-storage.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [Finite-width implementation model](../../transcription/word-model.md)

## Sources

- [Verbatim `merge_init`](../../../sources/listobject-excerpts.md#merge-init)
