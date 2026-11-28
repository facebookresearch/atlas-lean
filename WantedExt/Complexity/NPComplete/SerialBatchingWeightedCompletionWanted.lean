/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL-BATCHING TOTAL WEIGHTED COMPLETION TIME (1|s-batch|Σw_iC_i) is NP-complete

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47(2) (1993), 87-107, doi:10.1016/0166-218X(93)90085-3 (unary NP-hardness; text not
available to the author); P. Baptiste and A. Jouglet, "On minimizing total tardiness in a serial
batching problem", RAIRO Operations Research 35(1) (2001), 107-115, doi:10.1051/ro:2001105
(the model, and Table 1: "1|s-batch|Σw_iC_i, unary NP-Hard", citing Albers and Brucker).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SerialBatchingWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedCompletion

/-!
# SERIAL-BATCHING TOTAL WEIGHTED COMPLETION TIME (1|s-batch|Σw_iC_i) is NP-complete

INSTANCE: jobs `1, …, n` with processing times `p_j` and weights `w_j` (natural numbers), a setup
time `s`, and a bound `K`.
QUESTION: is there a serial-batching schedule on one machine whose total weighted completion time
`∑_j w_j C_j` is at most `K`, where `C_j` is the completion time of job `j`?

Serial batching (Baptiste and Jouglet 2001; Brucker and Knust's class `s-batch`): the jobs are
partitioned into batches processed one after another on the machine; a constant setup time `s`
precedes every batch; the length of a batch is the sum of the processing times of its jobs; all
jobs of a batch start together, when the batch's processing starts, and complete together, when
it completes. A schedule puts job `j` into batch `b j` and starts the setup of batch `k` at time
`S k`: batch `k` is set up during `[S k, S k + s)` and processes its jobs during
`[S k + s, S k + s + p(batch k))`, and a batch with a larger index starts only after every
nonempty batch with a smaller index has completed. Empty batch indices play no role. The setup
time is a positive natural number.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`; numbers are in binary encoding.
Undecodable bitstrings, and bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SERIAL-BATCHING TOTAL WEIGHTED COMPLETION TIME is NP-complete.**
Source: Albers and Brucker (1993), as recorded by Baptiste and Jouglet (2001), Table 1. -/
public theorem_wanted serialBatchingWeightedCompletion_npComplete :
    serialBatchingWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L serialBatchingWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SerialBatchingWeightedCompletion
