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
(`Correctness/MergeHiCorrectness.lean:1439`,
`Correctness/MergeHiCorrectness.lean:1440`, and
`Correctness/MergeHiCorrectness.lean:1443`, respectively).
These are premises of the machine-checked public theorem declared at
`Correctness/MergeHiCorrectness.lean:1428`.

`MergeHiSemanticPre` is definitionally an abbreviation of the public shared
`MergeSemanticPre` (`Correctness/MergeHiInvariant.lean:87`).
That shared structure contains exactly explicit `leftNonempty` and
`rightNonempty`; both retained ranges under the shared `Sorted` predicate; and
common signed-`read?` `firstStrict` and `lastStrict` endpoint witnesses saying
the retained right endpoint is strictly before the corresponding retained left
endpoint (`Correctness/MergeSemanticPre.lean:34`; this is a
definition, not a proof pin). Comparator binding and canonical stability are
not fields of that run-local semantic predicate.

`Pairwise` remains proof-local rather than becoming a surrogate public
contract: named proved bridges derive the mapped-key forms at
`Correctness/MergeHiInvariant.lean:94` and
`Correctness/MergeHiInvariant.lean:105`, and the whole-entry
forms at `Correctness/MergeHiInvariant.lean:118` and
`Correctness/MergeHiInvariant.lean:130`. The loop and
pure-correctness proofs consume those bridges instead of silently rebuilding a
second sortedness premise.

The theorem returns a result satisfying `MergeHiCorrectnessPost`. That post
contains the reviewed traced `MergeHiSafetyPost`; exact equality of the whole
affected key/payload-entry range with `mergeHiTargetEntries`; shared sortedness
and occurrence stability; `List.Perm` of the complete entries in exactly that
range; and `SortSlice.EqualOutsideRange` for every surrounding cell. The post
is defined at `Correctness/MergeHiCorrectness.lean:39`, and the
theorem inhabiting that exact post is machine-checked at
`Correctness/MergeHiCorrectness.lean:1428`.
Definitionally, `mergeHiTargetEntries` is the same left-biased whole-entry
`stableEntryMerge` used by the forward merge
(`Correctness/MergeHiInvariant.lean:43`). Snapshot preservation
is exported as a separate proved corollary at
`Correctness/MergeHiCorrectness.lean:163`.

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
local `.mergeHi` selector equation, explicit nonemptiness, shared `Sorted`
facts, direct-range stability, and both strict trimming endpoints are
discharged by the `merge_at` composition rather than left to its caller.  The
derivation of those local facts is internal proof-body evidence; the cited
public theorem signature is the reviewable pin that none survives as an extra
premise.

In particular, the strict-order exclusion of the defensive post-second-gallop
`nb = 0` arm is exported as
`mergeAt_secondTrimZero_impossible`
(`Correctness/MergeAtCorrectness.lean:707`).  A separate raw
regression shows that a deliberately inconsistent comparator really can reach
that success arm, so the exclusion is not vacuous and is not silently imported
into the transcription
(`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeAtCorrectness.lean:174`).

The resulting selected-pair certificate covers the complete adjacent union,
including the galloped prefix and suffix, and exports exact stable-merge
equality, sortedness, occurrence stability, whole-entry permutation, and the
external frame.  Those are definition fields of
`MergeAtSelectedPairCorrectness` at
`Correctness/MergeAtCorrectness.lean:59`; the end-to-end theorem
inhabiting the enclosing post is `mergeAt_correct` at
`Correctness/MergeAtCorrectness.lean:1760`.

## Source-to-declaration map

- Setup, allocation, copying B to temporary storage, and the forced first A
  copy in the pinned C excerpt
  (`sources/listobject-excerpts.md:1156`–`1175`) are transcribed by
  `mergeHi?` at `Transcription/MergeHi.lean:986`. Their
  composition with the semantic cursor invariant is covered by the raw theorem
  `mergeHi_raw_correct` at
  `Correctness/MergeHiCorrectness.lean:1331`.
- The straight backward loop and its winner counters
  (`sources/listobject-excerpts.md:1185`–`1209`) are transcribed by
  `mergeHiLoop?` at `Transcription/MergeHi.lean:669`. The A,
  B, and equal-key control equations are theorem-pinned at
  `Transcription/MergeHi.lean:875`,
  `Transcription/MergeHi.lean:909`, and
  `Transcription/MergeHi.lean:945`;
  `mergeHiLoop_semantic` proves the complete straight/galloping driver at
  `Correctness/MergeHiCorrectness.lean:1154`.
- The backward gallop
  (`sources/listobject-excerpts.md:1217`–`1265`) is transcribed by
  `mergeHiGallopRound?` and `mergeHiGallopB?` at
  `Transcription/MergeHi.lean:624` and
  `Transcription/MergeHi.lean:567`. The exact
  `gallop_right` hint `na - 1` with `aCount = na - index`, and `gallop_left`
  hint `nb - 1` with `bCount = nb - index`, are theorem-pinned by the public
  equations at `Transcription/MergeHi.lean:828` and
  `Transcription/MergeHi.lean:772`.
  Their semantic theorems are at
  `Correctness/MergeHiCorrectness.lean:973` and
  `Correctness/MergeHiCorrectness.lean:777`.
- `Succeed` and `CopyA`
  (`sources/listobject-excerpts.md:1267`–`1280`) are transcribed by
  `mergeHiSucceed?` and `mergeHiCopyA?` at
  `Transcription/MergeHi.lean:540` and
  `Transcription/MergeHi.lean:552`. Their semantic theorems are
  at `Correctness/MergeHiCorrectness.lean:206` and
  `Correctness/MergeHiCorrectness.lean:227`. Comparator-error
  `Fail` is absent from the total-Boolean-comparator
  model; the shared remainder copy remains in `mergeHiSucceed?`.

## Review pins

- The unconditional raw evaluator result—successful exact whole-entry target
  plus external frame, without a raw-correctness premise—is proved by
  `mergeHi_raw_correct`
  (`Correctness/MergeHiCorrectness.lean:1331`).
- The public theorem joins that raw result to the actual traced safety result
  and exports sortedness, shared stability, whole-entry permutation, and frame
  (`Correctness/MergeHiCorrectness.lean:1428`).
- The forward and backward target wrappers compute the identical mathematical
  result for the same call; the public consistency theorem is
  `mergeLoTargetEntries_eq_mergeHiTargetEntries`
  (`Correctness/MergeTargetConsistency.lean:28`).
- Backward equality copies B into the later output slot, thereby leaving the
  equal A occurrence earlier in forward order; the equation and the concrete
  payload-bearing framed result are pinned at
  `Transcription/MergeHi.lean:945` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeHiCorrectness.lean:92`.
- The gallop fixture pins stable equal-key ordering and payload pairing in the
  final raw-evaluator output
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Transcription/MergeHi.lean:87`). It does not by itself
  observably pin branch entry; the two gallop-phase semantic theorems are at
  `Correctness/MergeHiCorrectness.lean:973` and
  `Correctness/MergeHiCorrectness.lean:777`.
- The raw inconsistent-comparator `nb = 0` hedge is observably exercised, while
  strict-order correctness proves the gallop-left insertion index positive and
  therefore excludes that outcome
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Transcription/MergeHi.lean:106` and
  `Correctness/MergeHiInvariant.lean:1565`).
- The concrete raw evaluator reaches the exact expected result, and its
  temporary allocation satisfies `TempStorageInv`
  (`CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeHiCorrectness.lean:83` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeHiCorrectness.lean:47`).
- Persistent whole-entry snapshot preservation follows from the exported local
  permutation, range bound, and frame
  (`Correctness/MergeHiCorrectness.lean:163`).

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
