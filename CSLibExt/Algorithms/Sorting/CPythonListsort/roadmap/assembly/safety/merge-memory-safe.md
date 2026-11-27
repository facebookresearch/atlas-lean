---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSort_mergeMemory_safe
---

# Temporary merge-memory safety

The completed aggregate theorem is `listSort_mergeMemory_safe` at
`Assembly/MergeMemorySafety.lean:208`. Its public premises are
exactly a Boolean comparator, `reverse`, a validated `ListSortInput`, and
`input.slice.entries.size ≤ PY_LIST_MAX`; there is no caller-supplied temporary
invariant, live-backing, values-mode, history, or allocation premise. The raw
counterpart `listSortImpl_mergeMemory_safe` at
`Assembly/MergeMemorySafety.lean:167` has exactly the size bound
and the explicit `SortSlice.ValuesModeInvariant hasKeyfunc input` needed by the
raw entry point. Its existential conclusion is
`ListSortImplMergeMemorySafetyPost`, stated at
`Assembly/MergeMemorySafety.lean:51`; it exports the same
execution, trace, lifecycle, storage, physical-bound, and provenance facts at
the raw evaluator boundary, with the retained mode bit equal to the explicit
`hasKeyfunc` (`Assembly/MergeMemorySafety.lean:55`,
`Assembly/MergeMemorySafety.lean:72`,
`Assembly/MergeMemorySafety.lean:89`,
`Assembly/MergeMemorySafety.lean:96`,
`Assembly/MergeMemorySafety.lean:101`,
`Assembly/MergeMemorySafety.lean:104`, and
`Assembly/MergeMemorySafety.lean:108`). The ordinary
unkeyed-array specialization is
`listSort_unkeyedArray_mergeMemory_safe` at
`Assembly/MergeMemorySafety.lean:244`.

The public conclusion is the existential
`ListSortMergeMemorySafetyPost`, defined at
`Assembly/MergeMemorySafety.lean:111`. It pins, on the real
`listSortTraced?` execution, successful result and return code
(`Assembly/MergeMemorySafety.lean:115` and `:117`), no result or
trace fuel exhaustion (`Assembly/MergeMemorySafety.lean:119`
and `:121`), exact erasure to
`listSort?` (`Assembly/MergeMemorySafety.lean:123`), ordinary
access bounds (`Assembly/MergeMemorySafety.lean:128`), no
released temporary-payload access
(`Assembly/MergeMemorySafety.lean:131`), the stack-depth bound
(`Assembly/MergeMemorySafety.lean:134`), the concrete initial
physical bound (`Assembly/MergeMemorySafety.lean:140`), the
exact lifecycle (`Assembly/MergeMemorySafety.lean:145`), final
`TempStorageInv`, values-mode, and mode bit
(`Assembly/MergeMemorySafety.lean:152`,
`Assembly/MergeMemorySafety.lean:154`, and
`Assembly/MergeMemorySafety.lean:157`), the final physical bound
(`Assembly/MergeMemorySafety.lean:160`), and the closed
merge-`memcpy` provenance contract
(`Assembly/MergeMemorySafety.lean:163`).

The lifecycle conjunct is the definition at
`Assembly/MergeMemoryLifecycle.lean:1034`: the trace is exactly
one initial event, a continuous list of real directional-call events, and one
terminal cleanup. It requires `ActiveCore` at initialization, `Valid` and
`Bounded` for every call, and `CleanupValid` at exit. `ActiveCore` is defined at
`Assembly/MergeMemoryLifecycle.lean:69`; it contains the raw
snapshot form of `TempStorageInv`, live backing, exact logical capacity, and
the concrete keyed/unkeyed values mode. `CleanupValid` is defined at
`Assembly/MergeMemoryLifecycle.lean:826`; it deliberately
permits released storage's stale metadata while retaining the representation
and values-mode facts. These are definitions; their inhabitance for the actual
execution is what the two aggregate theorems above prove.

Every call's `Valid` record is defined at
`Assembly/MergeMemoryLifecycle.lean:432`. It contains the exact
minimum request, shrink-only trimming and source-run/list-length chain, the
smaller-half bound, the keyed multiplier-two limit `2^59 - 1`, the unkeyed
limit `2^60 - 1`, `requestWithinLimit`, `outcome ≠ .guardRejected`, request-fit
and key/value physical-slot inequalities, and preservation of the physical
bound. Actual lo and hi records satisfy the whole record by
`mergeLoMemoryCallEvent_valid` and `mergeHiMemoryCallEvent_valid` at
`Assembly/MergeMemoryLifecycle.lean:534` and
`Assembly/MergeMemoryLifecycle.lean:628`; the
optional intermediate free and all three active snapshots satisfy the physical
ceiling through the bounded projections at
`Assembly/MergeMemoryLifecycle.lean:788` and
`Assembly/MergeMemoryLifecycle.lean:805`.

The storage frame consumed on each directional path is anchored to the exact
machine state returned by that call's named `merge_getmem`: the lo and hi
`allocationPost`/`postGetmemStorageFrame` fields are stated at
`Assembly/MergeLoSafety.lean:3363` and
`Assembly/MergeLoSafety.lean:3367`, and
`Assembly/MergeHiSafety.lean:3888` and
`Assembly/MergeHiSafety.lean:3892`. The downstream
semantic machine invariants refer to those same `mergeLoAllocated` and
`mergeHiAllocated` states definitionally at
`Correctness/MergeLoInvariant.lean:158` and
`Correctness/MergeHiInvariant.lean:152`; they do not silently
rebase the correctness machine on the pre-allocation state.

Consequently the theorem covers the physical bound at all three levels: the
initializer field is exported at
`Assembly/MergeMemorySafety.lean:140`, every call is `Bounded`
through the lifecycle's all-call quantifier at
`Assembly/MergeMemoryLifecycle.lean:1045`, and the post-cleanup
final state is bounded by the public post field at
`Assembly/MergeMemorySafety.lean:160`.

The aggregate's `memcpyProvenance` field is at
`Assembly/MergeMemorySafety.lean:163`; it is discharged by the
closed call-site theorem `mergeMemcpyCallsiteProvenance` at
`Assembly/MergeMemcpyProvenance.lean:67`. That theorem covers
all six temp/main `memcpy` tags and retains the same-backing-overlap rejection
regression in its contract, rather than relying on an implicit C pointer fact.

Whole-trace temporary-payload liveness is a direct public post field at
`Assembly/MergeMemorySafety.lean:131`, and final
`TempStorageInv`, values-mode, exact `hasValues` bit, and physical bound are the
fields at `Assembly/MergeMemorySafety.lean:152`,
`Assembly/MergeMemorySafety.lean:154`,
`Assembly/MergeMemorySafety.lean:157`, and
`Assembly/MergeMemorySafety.lean:160`. In particular, the
mode-bit equation is separate from the entrywise values-mode invariant, which
can be vacuous on an empty slice.

## Anti-vacuity pins

- A raw snapshot with a fabricated physical-slot count cannot satisfy
  `StorageInv`: `storageInv_rejects_phantomPhysicalSlots` is theorem-pinned at
  `Assembly/MergeMemoryLifecycle.lean:87`.
- A raw call claiming `.guardRejected` cannot satisfy the signed `Valid`
  contract: `valid_rejects_guardRejected` is theorem-pinned at
  `Assembly/MergeMemoryLifecycle.lean:478`. This is contract
  exclusion, not by itself evidence that the modeled rejection branch exists.
- The guard fencepost is observably reachable in the model:
  `mergeGetmem_keyed_boundary_regression` proves that keyed
  `need = 2^59 - 1` grows while `need = 2^59` returns `.guardRejected` at
  `Transcription/MergeMemory.lean:213`.
- A two-call trace with a discontinuous boundary cannot satisfy the call chain:
  `MergeMemoryCallChain.rejects_two_call_gap` is theorem-pinned at
  `Assembly/MergeMemoryLifecycle.lean:916`.
- Exact empty unkeyed and keyed executions contain only initialization followed
  by cleanup; the keyed witness also pins the retained mode bit to `true`.
  These are kernel-checked regressions at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:88` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:117`.
- The aggregate post is kernel-inhabited on a nontrivial two-run lo fixture by
  `listSort_mergeMemory_lo_aggregate_regression` at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:157`.
- Exact lo and hi direction lists for actual top-level traces are asserting
  `IO Unit` runtime regressions at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:149` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:168`. They are review
  witnesses, not premises of the aggregate theorem.
- Reuse and repeated growth are exercised by an asserting `IO Unit` runtime
  regression at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:177`: its exact summaries
  include an inline-to-heap allocation of 129 cells, reuse of 129 cells, and a
  `.released` intermediate snapshot followed by heap growth to 258 cells. It
  is not consumed by any theorem.

The version-one successful-allocation abstraction remains in force; allocator
failure behavior is outside scope.

## Depends on

- [Merge-memory event validity and continuous-segment support](merge-memory-event-validity.md)
- [MergeState and pending runs](../../transcription/merge-state.md)
- [Temporary-storage representation invariant](../../transcription/temp-storage-invariant.md)
- [Array-access, push-depth, and merge-memory trace model](access-trace.md)
- [sortslice primitive safety](sortslice-safe.md)
- [Merge `memcpy` call-site provenance](merge-memcpy-provenance.md)

## Proof depends on

- [`list_sort_impl` fuel adequacy and actual traced evaluator](termination.md)
- [`merge_init` establishes temporary-storage validity](merge-init-storage-valid.md)

## Sources

- [Verbatim `merge_init`](../../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `merge_freemem`](../../../sources/listobject-excerpts.md#merge-freemem)
- [Verbatim `merge_getmem`](../../../sources/listobject-excerpts.md#merge-getmem)
- [Verbatim `MERGE_GETMEM`](../../../sources/listobject-excerpts.md#merge-getmem-macro)
- [Verbatim `list_sort_impl`](../../../sources/listobject-excerpts.md#list-sort-impl)
- [Modeling boundary](../../../sources/toplevel-theorems.md#explicit-scope-boundary)
