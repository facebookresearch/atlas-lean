---
declaration: def
origin: cited
statement: formalized
lean: CPythonListsort.mergeGetmem
---

# `merge_getmem`

Transcribe all deterministic control paths of temporary-storage growth. The
signed `need <= alloced` branch reuses the entire state unchanged. Otherwise,
compute the C multiplier—two physical pointer slots per logical cell when
values are present, one otherwise—call `merge_freemem`, and then apply the
unsigned `(size_t) need` allocation guard. An oversized request is rejected
with the post-free state; equality at the guard limit is admitted. A permitted
request installs fresh, uninitialized heap cells, discards the old payload,
and updates `alloced` to `need` while retaining keyed/unkeyed mode.

The v1 definition models a guard-admitted `PyMem_Malloc` as successful; the
nondeterministic null-return branch remains outside scope. It does not add a
liveness check before the source's reuse test, so an artificial released state
with stale sufficient `alloced` still reuses. The separate safety theorem must
exclude that unreachable input.

The companion theorem `mergeGetmem_keyed_boundary_regression` machine-checks
the selected-platform fencepost on the allocation path: keyed
`need = 2^59 - 1` grows successfully, while `need = 2^59` takes the deterministic
guard-rejection branch.

## Depends on

- [Finite-width implementation model](word-model.md)
- [MergeState and pending runs](merge-state.md)
- [Temporary-storage representation invariant](temp-storage-invariant.md)
- [merge_freemem](merge-freemem.md)

## Human transcription review

Check the signed reuse comparison, multiplier capture before freeing, free
before unsigned guard, equality-at-limit behavior, exact one-versus-two-slot
accounting, destructive rejection state, and the explicitly omitted allocator
null-return branch.

## Sources

- [Verbatim `merge_getmem`](../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `MERGE_GETMEM`](../../sources/listobject-excerpts.md#merge-getmem-macro)
- [CPython merge-memory explanation](../../sources/listsort.md#merge-memory)
