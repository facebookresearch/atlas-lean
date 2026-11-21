# CPython listsort in Lean roadmap

The project formalizes the complete listsort algorithm from the pinned CPython
snapshot. PowerSort is treated as its merge policy, not as the whole sorter.
Work proceeds from implementation transcription through bit-level bridge
lemmas and policy safety to the two assembly theorems.

## Chapters

1. [Implementation transcription](transcription/README.md)
2. [Bit-level equivalence](bit-equivalence/README.md)
3. [Comparator-independent merge policy](policy/README.md)
4. [Assembly and top-level theorems](assembly/README.md)

## Proof trust boundary

Roadmap declarations in the safety, policy, and correctness chains are
required to be kernel-checked. Review packets must report their
`#print axioms` output, with only Lean's standard logical infrastructure
(`propext`, `Classical.choice`, and `Quot.sound`) admitted. Small executable
regressions use kernel `decide` wherever it can normalize the model directly.

Paths below are relative to this development's root,
`CSLibExt/Algorithms/Sorting/CPythonListsort/`, except where they begin with
`CSLibExtTest/`, which is relative to the repository root.

The following twelve review witnesses used `native_decide` in the standalone
development. The root library forbids that tactic, so each one is now an
asserting `IO Unit` **runtime regression** in the test library, executed by
`#eval` when `CSLibExtTest` is built. Each retains its original fixtures and
its original Boolean proposition; none is a theorem, a proof premise, or a
proposition the kernel has checked:

- `mergeAt_slide_regression` —
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Transcription/MergeAt.lean:37`;
- `mergeAt_thirdLast_slide_regression` —
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeAtCorrectness.lean:158`;
- `foundNewRunLoop_taken_merge_regression` —
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/FoundNewRunCorrectness.lean:44`;
- `mergeForceCollapse_threeRun_equalKey_payload_regression` —
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/MergeForceCollapseCorrectness.lean:72`;
- `listSortScan_long_run_no_extension_regression` and
  `listSortScan_policy_merge_then_push_regression` —
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ScanStepCorrectness.lean:92` and `:137`.
- `listSort_forward_keyed_duplicate_exact_regression` and
  `listSort_reverse_keyed_duplicate_exact_regression` — exact observable
  key/origin/payload outputs for one duplicate-key input in both public
  directions, at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Correctness/ListSortCorrectness.lean:158` and `:177`.
- `listSort_mergeMemory_lo_event_regression` and
  `listSort_mergeMemory_hi_event_regression` — exact singleton directional-call
  lists for actual nontrivial top-level executions, at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:149` and
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:168`;
- `listSort_mergeMemory_released_growth_regression` — exact reuse/growth
  summaries for an actual keyed execution, including the released intermediate
  state before its second heap growth, at
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/MergeMemorySafety.lean:177`.
- `listSort_powerSort_cost_rotation_regression` — the exact policy-event
  stream for a real 256-element execution, pinning its seven formed runs,
  boundary powers, scan cost, CPython final-collapse cost 685, and canonical
  PowerSort cost 689, in
  `CSLibExtTest/Algorithms/Sorting/CPythonListsort/Assembly/PowerSortCostRegression.lean:125`.

These execute through opaque evaluator boundaries that kernel `decide` does
not normalize; direct replacement was tested and fails with “Decidable did not
reduce,” rather than merely timing out.  That is why they were never
kernel-checked premises.  As `IO Unit` definitions they carry no proof term
and no axioms at all: the Boolean is evaluated by the Lean interpreter and a
false result raises an `IO` error that fails the `CSLibExtTest` build.  They
establish concrete branch reachability for human review only.  No theorem,
definition, or roadmap proof edge may consume them.
`verify/verify_trust_boundary.py` enforces the exact allowlist, checks each
witness against the original proposition recorded in
`verify/migration-map.json`, and verifies that every listed regression has no
production consumer.

<!-- AUTHORING NOTES — these comments are not published.

     Replace the line above with a short statement of the goal, then link each
     chapter below in reading order. This page is the book's preface and table
     of contents; keep it short.

     A chapter is a DIRECTORY holding a README.md. That README.md *is* the
     chapter: it carries the narrative prose, and the formalizable statements
     beside it are placed into that prose where they are first used.

         roadmap/
           README.md              <- this page
           first-chapter/
             README.md            <- the chapter, with its exposition
             some-definition.md   <- a formalizable leaf
             main-result.md

     A chapter directory WITHOUT a README.md is not a chapter. Its pages
     collapse to the top level and the published book has no structure. Write
     the chapter as `<chapter>/README.md`, never as a sibling file beside the
     directory, then run `autoform check`.

     Add a `## Chapters` heading once there is more than one chapter to list.
-->
