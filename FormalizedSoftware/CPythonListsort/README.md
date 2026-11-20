# CPython listsort in Lean

This ATLAS v2 entry formalizes the list-sorting algorithm in a pinned snapshot
of CPython.  Its Lean modules are organized in five layers under `Code/`:
`Transcription`, `Equivalence`, `Policy`, `Assembly`, and `Correctness`.
The module prefix is `Code`, while the namespace and all declaration names
remain `CPythonListsort` exactly as in the development repository.

## Pinned implementation source

The target is CPython commit
[`67e6be72be9c0b75a31795ed42f9afb5eb431d47`](https://github.com/python/cpython/commit/67e6be72be9c0b75a31795ed42f9afb5eb431d47).
The pinned SHA-256 digests are:

- `Objects/listobject.c`:
  `ae082e295971b1c7cd2156d43421be07c6f4faf5fdf3577c695de22dcc564432`
- `Objects/listsort.txt`:
  `674d514b968e2a9b6f785ca2cbd99e09edc63bbc0f3698033391c27f53757512`

See [`sources/upstream-pins.md`](sources/upstream-pins.md) for all source and
toolchain pins.  The excerpt verifier downloads through the immutable commit
and compares the generated Markdown byte-for-byte.

## Public results

The entry's five headline public theorem statements are reproduced verbatim
below.  They live in namespace `CPythonListsort`.

### Comparator-independent safety

From [`Code/Assembly/ListSortSafety.lean`](Code/Assembly/ListSortSafety.lean):

```lean
theorem listsort_safe
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse input
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds
```

Named `listsort_safe_keyed` and `listsort_safe_unkeyed` corollaries specialize
this theorem to the two validated public constructors.

### Keyed functional correctness

From
[`Code/Correctness/ListSortCorrectness.lean`](Code/Correctness/ListSortCorrectness.lean):

```lean
theorem listsort_correct_keyed
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (reverse : Bool) (entries : Array (alpha × nu))
    (hmax : entries.size ≤ PY_LIST_MAX) :
    ∃ result : ListSortImplResult (Occurrence alpha) nu,
      listSort? lt reverse (ListSortInput.keyed entries) =
          some (eraseOccurrenceListSortImplResult result) ∧
        ListSortCorrectnessPost lt reverse
          (ListSortInput.keyed entries) result
```

`ListSortCorrectnessPost` exposes requested-order key sortedness,
occurrence-level stability, permutation of the complete key/payload snapshot,
successful return, and non-exhausted fuel.  The first conjunct above connects
that certificate to the ordinary untagged evaluator.

### Unkeyed functional correctness

Also from
[`Code/Correctness/ListSortCorrectness.lean`](Code/Correctness/ListSortCorrectness.lean):

```lean
theorem listsort_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (reverse : Bool) (xs : Array alpha)
    (hmax : xs.size ≤ PY_LIST_MAX) :
    ∃ result : ListSortImplResult (Occurrence alpha) PUnit,
      listSort? lt reverse (ListSortInput.unkeyed xs) =
          some (eraseOccurrenceListSortImplResult result) ∧
        listSort? (occurrenceComparator lt) reverse
            (ListSortInput.unkeyed xs).withOccurrenceKeys = some result ∧
        let tagged : TaggedOutput alpha := ⟨result.occurrences⟩
        Sorted (requestedComparator lt reverse) tagged.values ∧
          Stable (requestedComparator lt reverse) xs tagged ∧
          tagged.values.toList.Perm xs.toList
```

### Temporary-memory lifecycle safety

From
[`Code/Assembly/MergeMemorySafety.lean`](Code/Assembly/MergeMemorySafety.lean):

```lean
theorem listSort_mergeMemory_safe
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result, ListSortMergeMemorySafetyPost lt reverse input result
```

The postcondition combines successful execution, exact trace erasure,
in-bounds and live temporary-payload accesses, stack depth, initial and final
physical-storage bounds, the temporary-storage lifecycle, values mode, and
the proved `memcpy` call-site provenance.

### PowerSort merge-cost bound

From
[`Code/Assembly/ListSortCostBound.lean`](Code/Assembly/ListSortCostBound.lean):

```lean
theorem listsort_mergeCost_bound
    (lt : BoolComparator κ) (reverse : Bool) (input : ListSortInput κ ν)
    (hSize : input.slice.entries.size ≤ PY_LIST_MAX) :
    ∃ result profile implementationPlan powerSortPlan,
      ListSortMergeCostPost lt reverse input result profile
        implementationPlan powerSortPlan
```

The postcondition connects the real traced evaluator to its exact logical
merge plan and to a source-faithful canonical PowerSort plan, proving the
implementation cost is at most `nH + 2n` and at most the optimal alphabetic
merge cost plus `2n`.

## Claim boundary

Comparator model v1 uses a pure total Boolean comparator and an immutable
snapshot of already-computed keys paired with payloads.  Functional
correctness assumes a strict weak order; safety, storage-lifecycle safety, and
merge-cost accounting do not.  Both forward and reverse modes are covered.

Key-function evaluation, exception-raising or stateful comparisons, mutation
during sorting, allocation failure, interpreter reentrancy, compiler
correctness, and runtime behavior below C are outside scope.  These theorems
concern the Lean model.  Its correspondence to the pinned C is supported by
machine-verified source excerpts and human-reviewed transcription, not by a
machine-checked C-refinement proof.

**Key storage for short keyed sorts.** The model keeps the list being sorted
and the merge scratch storage in two separate stores. In C, a keyed sort of
fewer than 128 elements places its keys array inside `ms.temparray` (at
`&ms.temparray[saved_ob_size + 1]`), the same stack buffer that `merge_init`
uses as inline scratch storage. The scratch region occupies the first
`2 * ms.alloced <= saved_ob_size + 1` slots, so the two regions do not overlap,
but this layout fact is not proved in Lean. The memcpy provenance and
inline-capacity results hold for the model's separated stores; they do not by
themselves establish non-overlap within `temparray`.

The unsuffixed literal in `merge_init` makes its minrun-mask expression have
type `int`; the selected v1 platform fixes `int` at 32 bits and zero-extends
that bit pattern into the 64-bit stored word.  This is a project convention,
not a claim about ISO C behavior for undefined large signed shifts.  Exact
balanced-cycle equivalence is therefore limited to `mr_e < 32`; the public
results instead consume the unconditional bound `1 ≤ minrun ≤ 64`, proved by
`minrunNextN_output_bounds`
(`Code/Equivalence/MinrunResults.lean:295`).

For very large lists, this bound depends on the convention above.
`merge_init` computes `(1 << ms->mr_e) - 1`. For lists of 2^37 (~137
billion) or more elements, `mr_e >= 32`, so this shifts a 32-bit `int` by
32 or more, which is undefined behavior in C. On architectures whose 32-bit
shift masks the count to 5 bits (x86-64, AArch64, RISC-V, MIPS), the result
is `(1 << (mr_e mod 32)) - 1`; at `mr_e == 32` the mask is 0, so
`minrun_next` discards the remainder and returns a constant
`listlen >> mr_e`, still in [32, 64), which is harmless. On architectures
whose 32-bit shift yields 0 for counts >= 32 (PowerPC, s390x, AArch32), the
mask is -1, `mr_current` is never reset, and minrun grows with each run;
sorting would still be correct and stable but would degrade toward quadratic
insertion sort, and `mr_current` would overflow beyond ~2^43 elements. Of
these, only 64-bit PowerPC and s390x can address a list this large.

The cost theorem uses the positive lengths of the runs actually pushed by
`list_sort_impl`, after `count_run` and any adaptive `minrun_next`/
`binarysort` extension.  It does not use the original maximal-natural-run
vector and does not claim that formed leaves equal a balanced minrun target
cycle.  With an arbitrary comparator, “formed run” does not itself assert
semantic sortedness.  The bound concerns logical merge cost, not the paper's
comparison-count result.

## Proved tag erasure

Occurrence tags are proof-only ghost data, and their connection to the
ordinary evaluator is a theorem rather than an assumed model boundary.
[`eraseOccurrenceListSort`](Code/Correctness/OccurrenceErasureScan.lean)
proves that sorting occurrence-tagged keys with a value-only comparator and
then erasing the tags is exactly the ordinary untagged execution.
`ListSortCorrectnessPost.untaggedResultEq` exports that equality to the public
correctness API.

## Proof trust boundary

The principal theorem chains above are kernel-checked.  Twelve named,
compiler-checked `native_decide` regressions are retained solely as executable
review witnesses:

- `mergeAt_slide_regression`
- `mergeAt_thirdLast_slide_regression`
- `foundNewRunLoop_taken_merge_regression`
- `mergeForceCollapse_threeRun_equalKey_payload_regression`
- `listSortScan_long_run_no_extension_regression`
- `listSortScan_policy_merge_then_push_regression`
- `listSort_forward_keyed_duplicate_exact_regression`
- `listSort_reverse_keyed_duplicate_exact_regression`
- `listSort_mergeMemory_lo_event_regression`
- `listSort_mergeMemory_hi_event_regression`
- `listSort_mergeMemory_released_growth_regression`
- `listSort_powerSort_cost_rotation_regression`

The trust-boundary verifier enforces this exact allowlist and rejects any Lean
consumer of those declarations.

## Transcription-review provenance

The development workflow human-reviewed and signed off all 22 non-container
transcription nodes.  The local [`roadmap`](roadmap/README.md), including its
[`transcription` chapter](roadmap/transcription/README.md), is exported from
development commit
[`7a5f47de2501d41980fafa0a363c61c2a2fa688c`](https://github.com/neelsomani/cpython-listsort-lean/commit/7a5f47de2501d41980fafa0a363c61c2a2fa688c)
and retains the source citations and reviewed Lean targets.  Its
[`commit history`](https://github.com/neelsomani/cpython-listsort-lean/commits/main/blueprint/roadmap/transcription)
is the development-repository review record.  This provenance records human
review; it is not a machine-checked refinement proof or a cryptographic
signature.

## Verification

Use Lean `v4.33.1` and run the commands in
[`verify/VERIFY.md`](verify/VERIFY.md).  In short:

```sh
cd CPythonListsort
python3 verify/verify_excerpts.py
python3 verify/verify_trust_boundary.py
lake build
```
