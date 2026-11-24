---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.mergeLo_correct
---

# `merge_lo` stable correctness

For occurrence-carrying keys, `mergeLo_correct` assumes a Boolean strict weak
order `lt`, a canonical occurrence sequence, `PendingLayout pre scanned`, the
bound `pre.listlen.toNat ≤ PY_LIST_MAX`, and an actual selector result
`prepareMergeAt? pre i = some (.mergeLo call)`. It also assumes the local
storage premises consumed by the safety theorem: `TempStorageInv pre.a
pre.alloced`, live temporary backing, and the synchronized-values mode
invariant.

The correctness premises have the same public shape as for `merge_hi`. In
order, they are `hcomparator`, which binds the call-state comparator to
`occurrenceComparator lt`; `hstable`, which states the shared
`StableOccurrencePermutation` of the concatenated retained key ranges directly
against `canonical`; and `hsemantic : MergeLoSemanticPre lt call`
(`Correctness/MergeLoCorrectness.lean:1160`,
`Correctness/MergeLoCorrectness.lean:1161`, and
`Correctness/MergeLoCorrectness.lean:1164`, respectively).
These are premises of the machine-checked public theorem declared at
`Correctness/MergeLoCorrectness.lean:1148`.

`MergeLoSemanticPre` is definitionally an abbreviation of the public shared
`MergeSemanticPre` (`Correctness/MergeLoInvariant.lean:66`).
That shared structure contains exactly explicit `leftNonempty` and
`rightNonempty`; both retained ranges under the shared `Sorted` predicate; and
common signed-`read?` `firstStrict` and `lastStrict` endpoint witnesses saying
the retained right endpoint is strictly before the corresponding retained left
endpoint (`Correctness/MergeSemanticPre.lean:34`; this is a
definition, not a proof pin). Comparator binding and canonical stability are
not fields of that run-local semantic predicate.

`Pairwise` remains proof-local rather than becoming a surrogate public
contract: named proved bridges derive the mapped-key forms at
`Correctness/MergeLoInvariant.lean:73` and
`Correctness/MergeLoInvariant.lean:84`, and the whole-entry
forms at `Correctness/MergeLoInvariant.lean:96` and
`Correctness/MergeLoInvariant.lean:108`. The loop and
pure-correctness proofs consume those bridges instead of silently rebuilding a
second sortedness premise.

The theorem returns a result satisfying `MergeLoCorrectnessPost`. That post
contains the reviewed traced `MergeLoSafetyPost`; exact equality of the whole
affected key/payload-entry range with `mergeLoTargetEntries`; shared sortedness
and occurrence stability; `List.Perm` of the complete entries in exactly that
range; and `SortSlice.EqualOutsideRange` for every surrounding cell. The post
is defined at `Correctness/MergeLoCorrectness.lean:29`, and the
theorem inhabiting that exact post is machine-checked at
`Correctness/MergeLoCorrectness.lean:1148`.
Definitionally, `mergeLoTargetEntries` is the left-biased whole-entry
`stableEntryMerge` of the two retained runs
(`Correctness/MergeLoInvariant.lean:44`). Snapshot preservation
is exported as a separate proved corollary at
`Correctness/MergeLoCorrectness.lean:159`.

The direction-independence claim is also exported rather than left as a review
observation: `mergeLoTargetEntries_eq_mergeHiTargetEntries` proves that the two
target wrappers are equal for the same `lt` and `call`
(`Correctness/MergeTargetConsistency.lean:28`). The wrappers
both expand to the same `stableEntryMerge` definition
(`Correctness/StableMerge.lean:52`); the named theorem's proof is
`rfl` at `Correctness/MergeTargetConsistency.lean:32`, a
definitional fact now exposed through a citable theorem.

## Discharged `merge_at` composition

The downstream public `mergeAt_correct` theorem now consumes
`PendingRunsCorrect`, the input snapshot, comparator binding, the list-size
and admitted-position guards, and the storage premises; it has no additional
top-level `MergeSemanticPre`, trimming, or canonical-stability hypothesis
(`Correctness/MergeAtCorrectness.lean:1760`).  Consequently the
local `.mergeLo` selector equation, explicit nonemptiness, shared `Sorted`
facts, direct-range stability, and both strict trimming endpoints are
discharged by the `merge_at` composition rather than left to its caller.  The
derivation of those local facts is internal proof-body evidence; the cited
public theorem signature is the reviewable pin that none survives as an extra
premise.

The resulting selected-pair certificate covers the complete adjacent union,
including the galloped prefix and suffix, and exports exact stable-merge
equality, sortedness, occurrence stability, whole-entry permutation, and the
external frame.  Those are definition fields of
`MergeAtSelectedPairCorrectness` at
`Correctness/MergeAtCorrectness.lean:59`; the end-to-end theorem
inhabiting the enclosing post is `mergeAt_correct` at
`Correctness/MergeAtCorrectness.lean:1760`.

## Source-to-declaration map

- Setup, allocation, copying A to temporary storage, and the forced first B
  copy in the pinned C excerpt
  (`sources/listobject-excerpts.md:1016`–`1029`) are transcribed by
  `mergeLo?` at `Transcription/MergeLo.lean:831`. Their
  composition with the semantic invariant is covered by the raw theorem
  `mergeLo_raw_correct` at
  `Correctness/MergeLoCorrectness.lean:1122`.
- The ordinary loop and its winner counters
  (`sources/listobject-excerpts.md:1039`–`1063`) are transcribed by
  `mergeLoLoop?` at `Transcription/MergeLo.lean:581`. The B,
  A, and equal-key control equations are theorem-pinned at
  `Transcription/MergeLo.lean:750`,
  `Transcription/MergeLo.lean:774`, and
  `Transcription/MergeLo.lean:798`; the
  semantic preservation theorem for a complete ordinary step is at
  `Correctness/MergeLoCorrectness.lean:428`.
- The `gallop_right(..., hint = 0)` / `gallop_left(..., hint = 0)` round and its
  bulk movements (`sources/listobject-excerpts.md:1071`–`1117`) are
  transcribed by `mergeLoGallopRound?` at
  `Transcription/MergeLo.lean:509` and exposed by its public
  equation theorem at `Transcription/MergeLo.lean:675`. The
  complete galloping semantic step is machine-checked at
  `Correctness/MergeLoCorrectness.lean:584`.
- `Succeed` and `CopyB`
  (`sources/listobject-excerpts.md:1119`–`1130`) are transcribed by
  `mergeLoSucceed?` and `mergeLoCopyB?` at
  `Transcription/MergeLo.lean:483` and
  `Transcription/MergeLo.lean:491`. Their total
  semantic theorems are at
  `Correctness/MergeLoCorrectness.lean:173` and
  `Correctness/MergeLoCorrectness.lean:194`.
  Comparator-error `Fail` is absent from the total-Boolean-comparator model;
  the shared remainder copy remains in `mergeLoSucceed?`.

## Review pins

- The unconditional raw evaluator result—successful exact whole-entry target
  plus external frame, without a raw-correctness premise—is proved by
  `mergeLo_raw_correct`
  (`Correctness/MergeLoCorrectness.lean:1122`).
- The public theorem exports the actual traced safety result together with
  sortedness, shared stability, whole-entry permutation, and frame
  (`Correctness/MergeLoCorrectness.lean:1148`).
- The forward and backward target wrappers compute the identical mathematical
  result for the same call; the public consistency theorem is
  `mergeLoTargetEntries_eq_mergeHiTargetEntries`
  (`Correctness/MergeTargetConsistency.lean:28`).
- The pure target simultaneously has sorted keys, the shared occurrence
  stability predicate, and whole-entry permutation by
  `stableEntryMerge_correct`
  (`Correctness/StableMerge.lean:278`).
- The ordinary equal-key branch selects A, and the executable nonzero-base
  fixture retains the left equal occurrence before the right while preserving
  payloads and both outside sentinels
  (`Transcription/MergeLo.lean:798` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeLoCorrectness.lean:20`).
- The min-gallop-one fixture pins the final stable equal-key/payload result
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeLoCorrectness.lean:38`). It does not by
  itself observably pin entry into galloping mode; gallop semantics are instead
  covered parametrically by the theorem at
  `Correctness/MergeLoCorrectness.lean:584`.
- The raw inconsistent-comparator `na = 0` hedge is observably exercised with
  a continuation that always fails, while the strict-order correctness proof
  excludes that outcome through the strict gallop bound
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Transcription/MergeLo.lean:135` and
  `Correctness/MergeLoInvariant.lean:1919`).
- The concrete fixture's declared temporary allocation satisfies
  `TempStorageInv`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeLoCorrectness.lean:56`).

## Depends on

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)
- [merge_lo](../../transcription/merge-lo.md)
- [merge_lo safety](../safety/merge-lo-safe.md)

## Proof depends on

- [gallop_left partition specification](gallop-correct.md)
- [gallop_right partition specification](gallop-right-correct.md)

## Sources

- [CPython merge algorithms](../../../sources/listsort.md#merge-algorithms)
- [Verbatim `merge_lo`](../../../sources/listobject-excerpts.md#merge-lo)
