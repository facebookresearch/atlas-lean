# Replaying MiniImp's operational read-cost proof

Build the actual proof and test modules from the repository root:

```sh
lake --wfail --iofail build CSLibExt.Languages.MiniImp.BinarySearch
lake --wfail build CSLibExtTest.Languages.MiniImp.BinarySearchCostTests \
  CSLibExtTest.Languages.MiniImp.BinarySearchTests \
  CSLibExtTest.Languages.MiniImp.IMPBridgeTests
```

## The cost being proved

`execReads` uses canonical `Cslib.Algorithms.Lean.TimeM Nat (Option State)`.
One unit means one successful bounds-checked immutable-array read. Scalar
arithmetic, guards, assignments, branches and call overhead are free. Invalid
reads and zero fuel do not access an array and charge zero. A later failure
retains charges from its executed prefix, because `TimeM` is outside `Option`.
Fuel still bounds interpreter recursion depth, not this operation count.

## Proof chain

1. `execReads_ret` erases instrumentation to the existing `exec` for every
   program, state and fuel, including failure.
2. `ReadSteps` counts successful read rules in an operational derivation.
   Each read rule requires its actual index bound; other rules either charge
   zero or add the executed subderivations' counts. `execReads_sound` gives
   this derivation with exactly the instrumented count on success.
   `ReadSteps.erase` produces the original `BigStep` and its read-safety
   evidence. Conversely, `BigStep.exists_readSteps` supplies an existential
   count, without extracting data from proof-irrelevant evidence.
3. `BinarySearch.loop_reads_eq_time` unfolds the actual syntax body and one
   canonical `lowerBound.loop` step. One read corresponds to one canonical
   comparison; both follow the same branch and next interval. Fuel induction
   and the existing interval-decrease lemma establish exact count agreement.
   No assumed total-cost invariant or second search implementation is used.
4. `BinarySearch.program_reads_eq_time` includes the two free initialization
   assignments. For every state and fuel at least `xs.size + 7`, it proves
   actual reads equal `(TimeM.lowerBound xs key).time`, without sortedness.
5. `BinarySearch.program_reads_le` reuses `TimeM.lowerBound_time_le` to obtain
   the actual bound `Nat.clog 2 (xs.size + 1)`, also without sortedness.
6. `BinarySearch.verified_read_cost` composes successful instrumented and
   original execution, operational read adequacy, exact cost, the bound,
   the existing generated VC and Hoare triple, and sorted index-separation
   specification. Only the result interpretation requires sortedness.

The private `composed_client` test instantiates this theorem on `#[1,3,3,7]`
with key `3`, for any entry state. It obtains an actual counted derivation
with three reads, an original `BigStep`, and returned index one.

## Positive and falsifying checks

The tests check independently fixed counts for sizes 0, 1, 2, 3, 7, 8, 15 and
16, keys below/equal/above repeated elements, duplicate-key examples, arbitrary
entry values, both branches, invalid reads, exhausted fuel, and retained
failure-prefix costs. A real length-eight linear scan returns eight and costs
eight reads, exceeding the binary bound `clog₂(9) = 4`. A one-read command is
kernel-proved not to cost zero. These controls distinguish this specific
binary-search proof from an invalid bound for arbitrary MiniImp programs.

There are 16,380 full-search cost/index comparisons (two sufficient fuels for
each of 8,190 inputs) and 4,494 subinterval comparisons against the canonical
algorithm, including unsorted arrays. Both counts are asserted. The original
8,190 + 4,494 executable comparisons and canonical IMP bridge tests also run.
Finite tests supplement the universally quantified theorems.

## Trust and limits

Executor, erasure, exact-count and operational-adequacy proofs do not use
`Classical.choice`. The logarithmic corollary and its composed clients inherit
that standard axiom solely through the existing canonical logarithm bound;
they are not claimed constructive. No new axiom or native decision procedure
is added. The existing IMP bridge's test-only string-renaming exception is
unchanged.

This does not establish wall-time, instruction/byte/space cost, RAM adequacy,
polynomial-time computability or the rest of COST/LOGICS. The pinned CSLib
Boole README is only a placeholder; no Boole integration is claimed.
