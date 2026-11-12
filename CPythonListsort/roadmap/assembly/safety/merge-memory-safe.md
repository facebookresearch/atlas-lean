---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.listSort_mergeMemory_safe
---

# Temporary merge-memory safety

The completed aggregate theorem is `listSort_mergeMemory_safe` at
`Code/Assembly/MergeMemorySafety.lean:200`. Its public premises are
exactly a Boolean comparator, `reverse`, a validated `ListSortInput`, and
`input.slice.entries.size ≤ PY_LIST_MAX`; there is no caller-supplied temporary
invariant, live-backing, values-mode, history, or allocation premise. The raw
counterpart `listSortImpl_mergeMemory_safe` at
`Code/Assembly/MergeMemorySafety.lean:159` has exactly the size bound
and the explicit `SortSlice.ValuesModeInvariant hasKeyfunc input` needed by the
raw entry point. Its existential conclusion is
`ListSortImplMergeMemorySafetyPost`, stated at
`Code/Assembly/MergeMemorySafety.lean:43`; it exports the same
execution, trace, lifecycle, storage, physical-bound, and provenance facts at
the raw evaluator boundary, with the retained mode bit equal to the explicit
`hasKeyfunc` (`Code/Assembly/MergeMemorySafety.lean:47`,
`Code/Assembly/MergeMemorySafety.lean:64`,
`Code/Assembly/MergeMemorySafety.lean:81`,
`Code/Assembly/MergeMemorySafety.lean:88`,
`Code/Assembly/MergeMemorySafety.lean:93`,
`Code/Assembly/MergeMemorySafety.lean:96`, and
`Code/Assembly/MergeMemorySafety.lean:100`). The ordinary
unkeyed-array specialization is
`listSort_unkeyedArray_mergeMemory_safe` at
`Code/Assembly/MergeMemorySafety.lean:236`.

The public conclusion is the existential
`ListSortMergeMemorySafetyPost`, defined at
`Code/Assembly/MergeMemorySafety.lean:103`. It pins, on the real
`listSortTraced?` execution, successful result and return code
(`Code/Assembly/MergeMemorySafety.lean:107` and `:109`), no result or
trace fuel exhaustion (`Code/Assembly/MergeMemorySafety.lean:111`
and `:113`), exact erasure to
`listSort?` (`Code/Assembly/MergeMemorySafety.lean:115`), ordinary
access bounds (`Code/Assembly/MergeMemorySafety.lean:120`), no
released temporary-payload access
(`Code/Assembly/MergeMemorySafety.lean:123`), the stack-depth bound
(`Code/Assembly/MergeMemorySafety.lean:126`), the concrete initial
physical bound (`Code/Assembly/MergeMemorySafety.lean:132`), the
exact lifecycle (`Code/Assembly/MergeMemorySafety.lean:137`), final
`TempStorageInv`, values-mode, and mode bit
(`Code/Assembly/MergeMemorySafety.lean:144`,
`Code/Assembly/MergeMemorySafety.lean:146`, and
`Code/Assembly/MergeMemorySafety.lean:149`), the final physical bound
(`Code/Assembly/MergeMemorySafety.lean:152`), and the closed
merge-`memcpy` provenance contract
(`Code/Assembly/MergeMemorySafety.lean:155`).

The lifecycle conjunct is the definition at
`Code/Assembly/MergeMemoryLifecycle.lean:1023`: the trace is exactly
one initial event, a continuous list of real directional-call events, and one
terminal cleanup. It requires `ActiveCore` at initialization, `Valid` and
`Bounded` for every call, and `CleanupValid` at exit. `ActiveCore` is defined at
`Code/Assembly/MergeMemoryLifecycle.lean:58`; it contains the raw
snapshot form of `TempStorageInv`, live backing, exact logical capacity, and
the concrete keyed/unkeyed values mode. `CleanupValid` is defined at
`Code/Assembly/MergeMemoryLifecycle.lean:815`; it deliberately
permits released storage's stale metadata while retaining the representation
and values-mode facts. These are definitions; their inhabitance for the actual
execution is what the two aggregate theorems above prove.

Every call's `Valid` record is defined at
`Code/Assembly/MergeMemoryLifecycle.lean:421`. It contains the exact
minimum request, shrink-only trimming and source-run/list-length chain, the
smaller-half bound, the keyed multiplier-two limit `2^59 - 1`, the unkeyed
limit `2^60 - 1`, `requestWithinLimit`, `outcome ≠ .guardRejected`, request-fit
and key/value physical-slot inequalities, and preservation of the physical
bound. Actual lo and hi records satisfy the whole record by
`mergeLoMemoryCallEvent_valid` and `mergeHiMemoryCallEvent_valid` at
`Code/Assembly/MergeMemoryLifecycle.lean:523` and
`Code/Assembly/MergeMemoryLifecycle.lean:617`; the
optional intermediate free and all three active snapshots satisfy the physical
ceiling through the bounded projections at
`Code/Assembly/MergeMemoryLifecycle.lean:777` and
`Code/Assembly/MergeMemoryLifecycle.lean:794`.

The storage frame consumed on each directional path is anchored to the exact
machine state returned by that call's named `merge_getmem`: the lo and hi
`allocationPost`/`postGetmemStorageFrame` fields are stated at
`Code/Assembly/MergeLoSafety.lean:3442` and
`Code/Assembly/MergeLoSafety.lean:3446`, and
`Code/Assembly/MergeHiSafety.lean:3969` and
`Code/Assembly/MergeHiSafety.lean:3973`. The downstream
semantic machine invariants refer to those same `mergeLoAllocated` and
`mergeHiAllocated` states definitionally at
`Code/Correctness/MergeLoInvariant.lean:150` and
`Code/Correctness/MergeHiInvariant.lean:144`; they do not silently
rebase the correctness machine on the pre-allocation state.

Consequently the theorem covers the physical bound at all three levels: the
initializer field is exported at
`Code/Assembly/MergeMemorySafety.lean:132`, every call is `Bounded`
through the lifecycle's all-call quantifier at
`Code/Assembly/MergeMemoryLifecycle.lean:1034`, and the post-cleanup
final state is bounded by the public post field at
`Code/Assembly/MergeMemorySafety.lean:152`.

The aggregate's `memcpyProvenance` field is at
`Code/Assembly/MergeMemorySafety.lean:155`; it is discharged by the
closed call-site theorem `mergeMemcpyCallsiteProvenance` at
`Code/Assembly/MergeMemcpyProvenance.lean:59`. That theorem covers
all six temp/main `memcpy` tags and retains the same-backing-overlap rejection
regression in its contract, rather than relying on an implicit C pointer fact.

Whole-trace temporary-payload liveness is a direct public post field at
`Code/Assembly/MergeMemorySafety.lean:123`, and final
`TempStorageInv`, values-mode, exact `hasValues` bit, and physical bound are the
fields at `Code/Assembly/MergeMemorySafety.lean:144`,
`Code/Assembly/MergeMemorySafety.lean:146`,
`Code/Assembly/MergeMemorySafety.lean:149`, and
`Code/Assembly/MergeMemorySafety.lean:152`. In particular, the
mode-bit equation is separate from the entrywise values-mode invariant, which
can be vacuous on an empty slice.

## Anti-vacuity pins

- A raw snapshot with a fabricated physical-slot count cannot satisfy
  `StorageInv`: `storageInv_rejects_phantomPhysicalSlots` is theorem-pinned at
  `Code/Assembly/MergeMemoryLifecycle.lean:76`.
- A raw call claiming `.guardRejected` cannot satisfy the signed `Valid`
  contract: `valid_rejects_guardRejected` is theorem-pinned at
  `Code/Assembly/MergeMemoryLifecycle.lean:467`. This is contract
  exclusion, not by itself evidence that the modeled rejection branch exists.
- The guard fencepost is observably reachable in the model:
  `mergeGetmem_keyed_boundary_regression` proves that keyed
  `need = 2^59 - 1` grows while `need = 2^59` returns `.guardRejected` at
  `Code/Transcription/MergeMemory.lean:202`.
- A two-call trace with a discontinuous boundary cannot satisfy the call chain:
  `MergeMemoryCallChain.rejects_two_call_gap` is theorem-pinned at
  `Code/Assembly/MergeMemoryLifecycle.lean:905`.
- Exact empty unkeyed and keyed executions contain only initialization followed
  by cleanup; the keyed witness also pins the retained mode bit to `true`.
  These are kernel-checked regressions at
  `Code/Assembly/MergeMemorySafety.lean:319` and
  `Code/Assembly/MergeMemorySafety.lean:348`.
- The aggregate post is kernel-inhabited on a nontrivial two-run lo fixture by
  `listSort_mergeMemory_lo_aggregate_regression` at
  `Code/Assembly/MergeMemorySafety.lean:386`.
- Exact lo and hi direction lists for actual top-level traces are
  compiler-checked `native_decide` proof leaves at
  `Code/Assembly/MergeMemorySafety.lean:380` and
  `Code/Assembly/MergeMemorySafety.lean:397`. They are review
  witnesses, not premises of the aggregate theorem.
- Reuse and repeated growth are exercised by a compiler-checked
  `native_decide` proof leaf at
  `Code/Assembly/MergeMemorySafety.lean:404`: its exact summaries
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
