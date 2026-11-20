---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeHi_correct
---

# `merge_hi` stable correctness

For occurrence-carrying keys, `mergeHi_correct` assumes a Boolean strict weak
order `lt`, a canonical occurrence sequence, `PendingLayout pre scanned`, the
bound `pre.listlen.toNat ≤ PY_LIST_MAX`, and an actual selector result
`prepareMergeAt? pre i = some (.mergeHi call)`. It also assumes the local
storage premises consumed by the safety theorem: `TempStorageInv pre.a
pre.alloced`, live temporary backing, and the synchronized-values mode
invariant.

The correctness premises have the same public shape as for `merge_lo`. In
order, they are `hcomparator`, which binds the call-state comparator to
`occurrenceComparator lt`; `hstable`, which states the shared
`StableOccurrencePermutation` of the concatenated retained key ranges directly
against `canonical`; and `hsemantic : MergeHiSemanticPre lt call`
(`Code/Correctness/MergeHiCorrectness.lean:1428`,
`Code/Correctness/MergeHiCorrectness.lean:1429`, and
`Code/Correctness/MergeHiCorrectness.lean:1432`, respectively).
These are premises of the machine-checked public theorem declared at
`Code/Correctness/MergeHiCorrectness.lean:1417`.

`MergeHiSemanticPre` is definitionally an abbreviation of the public shared
`MergeSemanticPre` (`Code/Correctness/MergeHiInvariant.lean:79`).
That shared structure contains exactly explicit `leftNonempty` and
`rightNonempty`; both retained ranges under the shared `Sorted` predicate; and
common signed-`read?` `firstStrict` and `lastStrict` endpoint witnesses saying
the retained right endpoint is strictly before the corresponding retained left
endpoint (`Code/Correctness/MergeSemanticPre.lean:26`; this is a
definition, not a proof pin). Comparator binding and canonical stability are
not fields of that run-local semantic predicate.

`Pairwise` remains proof-local rather than becoming a surrogate public
contract: named proved bridges derive the mapped-key forms at
`Code/Correctness/MergeHiInvariant.lean:86` and
`Code/Correctness/MergeHiInvariant.lean:97`, and the whole-entry
forms at `Code/Correctness/MergeHiInvariant.lean:110` and
`Code/Correctness/MergeHiInvariant.lean:122`. The loop and
pure-correctness proofs consume those bridges instead of silently rebuilding a
second sortedness premise.

The theorem returns a result satisfying `MergeHiCorrectnessPost`. That post
contains the reviewed traced `MergeHiSafetyPost`; exact equality of the whole
affected key/payload-entry range with `mergeHiTargetEntries`; shared sortedness
and occurrence stability; `List.Perm` of the complete entries in exactly that
range; and `SortSlice.EqualOutsideRange` for every surrounding cell. The post
is defined at `Code/Correctness/MergeHiCorrectness.lean:28`, and the
theorem inhabiting that exact post is machine-checked at
`Code/Correctness/MergeHiCorrectness.lean:1417`.
Definitionally, `mergeHiTargetEntries` is the same left-biased whole-entry
`stableEntryMerge` used by the forward merge
(`Code/Correctness/MergeHiInvariant.lean:35`). Snapshot preservation
is exported as a separate proved corollary at
`Code/Correctness/MergeHiCorrectness.lean:152`.

The direction-independence claim is also exported rather than left as a review
observation: `mergeLoTargetEntries_eq_mergeHiTargetEntries` proves that the two
target wrappers are equal for the same `lt` and `call`
(`Code/Correctness/MergeTargetConsistency.lean:20`). The wrappers
both expand to the same `stableEntryMerge` definition
(`Code/Correctness/StableMerge.lean:44`); the named theorem's proof is
`rfl` at `Code/Correctness/MergeTargetConsistency.lean:24`, a
definitional fact now exposed through a citable theorem.

## Discharged `merge_at` composition

The downstream public `mergeAt_correct` theorem now consumes
`PendingRunsCorrect`, the input snapshot, comparator binding, the list-size
and admitted-position guards, and the storage premises; it has no additional
top-level `MergeSemanticPre`, trimming, or canonical-stability hypothesis
(`Code/Correctness/MergeAtCorrectness.lean:1752`).  Consequently the
local `.mergeHi` selector equation, explicit nonemptiness, shared `Sorted`
facts, direct-range stability, and both strict trimming endpoints are
discharged by the `merge_at` composition rather than left to its caller.  The
derivation of those local facts is internal proof-body evidence; the cited
public theorem signature is the reviewable pin that none survives as an extra
premise.

In particular, the strict-order exclusion of the defensive post-second-gallop
`nb = 0` arm is exported as
`mergeAt_secondTrimZero_impossible`
(`Code/Correctness/MergeAtCorrectness.lean:699`).  A separate raw
regression shows that a deliberately inconsistent comparator really can reach
that success arm, so the exclusion is not vacuous and is not silently imported
into the transcription
(`Code/Correctness/MergeAtCorrectness.lean:1944`).

The resulting selected-pair certificate covers the complete adjacent union,
including the galloped prefix and suffix, and exports exact stable-merge
equality, sortedness, occurrence stability, whole-entry permutation, and the
external frame.  Those are definition fields of
`MergeAtSelectedPairCorrectness` at
`Code/Correctness/MergeAtCorrectness.lean:51`; the end-to-end theorem
inhabiting the enclosing post is `mergeAt_correct` at
`Code/Correctness/MergeAtCorrectness.lean:1752`.

## Source-to-declaration map

- Setup, allocation, copying B to temporary storage, and the forced first A
  copy in the pinned C excerpt
  (`sources/listobject-excerpts.md:1156`–`1175`) are transcribed by
  `mergeHi?` at `Code/Transcription/MergeHi.lean:978`. Their
  composition with the semantic cursor invariant is covered by the raw theorem
  `mergeHi_raw_correct` at
  `Code/Correctness/MergeHiCorrectness.lean:1320`.
- The straight backward loop and its winner counters
  (`sources/listobject-excerpts.md:1185`–`1209`) are transcribed by
  `mergeHiLoop?` at `Code/Transcription/MergeHi.lean:661`. The A,
  B, and equal-key control equations are theorem-pinned at
  `Code/Transcription/MergeHi.lean:867`,
  `Code/Transcription/MergeHi.lean:901`, and
  `Code/Transcription/MergeHi.lean:937`;
  `mergeHiLoop_semantic` proves the complete straight/galloping driver at
  `Code/Correctness/MergeHiCorrectness.lean:1143`.
- The backward gallop
  (`sources/listobject-excerpts.md:1217`–`1265`) is transcribed by
  `mergeHiGallopRound?` and `mergeHiGallopB?` at
  `Code/Transcription/MergeHi.lean:616` and
  `Code/Transcription/MergeHi.lean:559`. The exact
  `gallop_right` hint `na - 1` with `aCount = na - index`, and `gallop_left`
  hint `nb - 1` with `bCount = nb - index`, are theorem-pinned by the public
  equations at `Code/Transcription/MergeHi.lean:820` and
  `Code/Transcription/MergeHi.lean:764`.
  Their semantic theorems are at
  `Code/Correctness/MergeHiCorrectness.lean:962` and
  `Code/Correctness/MergeHiCorrectness.lean:765`.
- `Succeed` and `CopyA`
  (`sources/listobject-excerpts.md:1267`–`1280`) are transcribed by
  `mergeHiSucceed?` and `mergeHiCopyA?` at
  `Code/Transcription/MergeHi.lean:532` and
  `Code/Transcription/MergeHi.lean:544`. Their semantic theorems are
  at `Code/Correctness/MergeHiCorrectness.lean:195` and
  `Code/Correctness/MergeHiCorrectness.lean:216`. Comparator-error
  `Fail` is absent from the total-Boolean-comparator
  model; the shared remainder copy remains in `mergeHiSucceed?`.

## Review pins

- The unconditional raw evaluator result—successful exact whole-entry target
  plus external frame, without a raw-correctness premise—is proved by
  `mergeHi_raw_correct`
  (`Code/Correctness/MergeHiCorrectness.lean:1320`).
- The public theorem joins that raw result to the actual traced safety result
  and exports sortedness, shared stability, whole-entry permutation, and frame
  (`Code/Correctness/MergeHiCorrectness.lean:1417`).
- The forward and backward target wrappers compute the identical mathematical
  result for the same call; the public consistency theorem is
  `mergeLoTargetEntries_eq_mergeHiTargetEntries`
  (`Code/Correctness/MergeTargetConsistency.lean:20`).
- Backward equality copies B into the later output slot, thereby leaving the
  equal A occurrence earlier in forward order; the equation and the concrete
  payload-bearing framed result are pinned at
  `Code/Transcription/MergeHi.lean:937` and
  `Code/Correctness/MergeHiCorrectness.lean:1522`.
- The gallop fixture pins stable equal-key ordering and payload pairing in the
  final raw-evaluator output
  (`Code/Transcription/MergeHi.lean:1339`). It does not by itself
  observably pin branch entry; the two gallop-phase semantic theorems are at
  `Code/Correctness/MergeHiCorrectness.lean:962` and
  `Code/Correctness/MergeHiCorrectness.lean:765`.
- The raw inconsistent-comparator `nb = 0` hedge is observably exercised, while
  strict-order correctness proves the gallop-left insertion index positive and
  therefore excludes that outcome
  (`Code/Transcription/MergeHi.lean:1404` and
  `Code/Correctness/MergeHiInvariant.lean:1557`).
- The concrete raw evaluator reaches the exact expected result, and its
  temporary allocation satisfies `TempStorageInv`
  (`Code/Correctness/MergeHiCorrectness.lean:1513` and
  `Code/Correctness/MergeHiCorrectness.lean:1477`).
- Persistent whole-entry snapshot preservation follows from the exported local
  permutation, range bound, and frame
  (`Code/Correctness/MergeHiCorrectness.lean:152`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [merge_hi](../../transcription/merge-hi.md)
- [merge_hi safety](../safety/merge-hi-safe.md)

## Proof depends on

- [gallop_left partition specification](gallop-correct.md)
- [gallop_right partition specification](gallop-right-correct.md)

## Sources

- [CPython merge algorithms](../../../sources/listsort.md#merge-algorithms)
- [Verbatim `merge_hi`](../../../sources/listobject-excerpts.md#merge-hi)
