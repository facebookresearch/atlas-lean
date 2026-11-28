/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL BATCHING WITH CHAINS TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47 (1993), 87-107, doi:10.1016/0166-218X(93)90085-3 (`1|chains; s-batch|∑ Cᵢ`);
P. Brucker, *Scheduling Algorithms*, 5th edition, Springer (2007), Sections 2.7 and 8.1 (the
single machine s-batching model) and Table 8.2 (NP-hard serial batching problems), which lists
`1|chains; s-batch|∑ Cᵢ` as NP-hard with the attribution to Albers and Brucker.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTime

/-!
# SERIAL BATCHING WITH CHAINS TO MINIMIZE TOTAL COMPLETION TIME is NP-complete

INSTANCE: jobs `J₁, …, Jₙ` with processing times `pᵢ ∈ ℤ₀⁺`, a precedence relation on the
jobs that consists of chains (each job has at most one immediate predecessor and at most one
immediate successor), a set-up time `s ∈ ℤ₀⁺`, and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a
sequence of the jobs compatible with the precedence constraints and a partition of this
sequence into consecutive s-batches such that `∑ᵢ Cᵢ ≤ K`? Here each batch is preceded by a
machine set-up of `s` time units, the jobs of a batch are processed one after another, and every
job of a batch completes when the last job of its batch completes (`Cᵢ` is that time).

This is the single machine s-batching problem of Albers and Brucker in Brucker's formulation
(Sections 2.7 and 8.1: "an s-batch is a set of jobs which are processed jointly. The length of
an s-batch is the sum of the processing time of jobs in the batch. The flow time `Cᵢ` of a job
coincides with the completion time of the last scheduled job in its batch", with a set-up of
`s ≥ 0` time units for every batch, and for precedence constraints "a sequence which is
compatible with the precedence constraints"), with chain precedence and the objective
`∑ Cᵢ` (`1|chains; s-batch|∑ Cᵢ`).

A schedule is described by a batch index `β(i) ∈ ℕ` for every job: the batches are the nonempty
classes `{i | β(i) = b}`, processed in increasing order of `b`. Job `i` then completes after one
set-up for every nonempty batch with index at most `β(i)` and after all jobs of those batches:
`Cᵢ = s · |{β(j) | β(j) ≤ β(i)}| + ∑_{j : β(j) ≤ β(i)} pⱼ`. A sequence compatible with the
precedence constraints and partitioned into consecutive batches gives such a `β` with
`i → j` implying `β(i) ≤ β(j)`; conversely, from such a `β`, ordering the batches by index and
each batch along the (acyclic) precedence constraints gives a compatible sequence with the same
completion times, since the order inside a batch does not change them. The partial order is
given by the list of its pairs `(i, j)` with `i → j`, required to be a strict order (Mathlib's
`IsStrictOrder`); `i` is an immediate predecessor of `j` when `i → j` and no job `c` has
`i → c → j`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SERIAL BATCHING WITH CHAINS TO MINIMIZE TOTAL COMPLETION TIME is NP-complete.** Source:
Albers and Brucker (1993); Brucker (2007), Table 8.2. -/
public theorem_wanted chainsSerialBatchingCompletionTime_npComplete :
    chainsSerialBatchingCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsSerialBatchingCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTime
