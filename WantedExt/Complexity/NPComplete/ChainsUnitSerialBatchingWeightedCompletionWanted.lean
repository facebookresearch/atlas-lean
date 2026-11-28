/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL BATCHING WITH CHAINS AND UNIT PROCESSING TIMES TO MINIMIZE TOTAL WEIGHTED COMPLETION
# TIME is NP-complete

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47 (1993), 87-107, doi:10.1016/0166-218X(93)90085-3
(`1|chains; pⱼ = 1; s-batch|∑ wⱼCⱼ`);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Sections 2.7 and 8.1 (the
s-batching model) and the table of NP-hard single machine s-batching problems, which lists
`1|chains; pⱼ = 1; s-batch|∑ wⱼCⱼ` as NP-hard in the strong sense (Albers and Brucker);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (serial batching problems).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainsUnitSerialBatchingWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitSerialBatchingWeightedCompletion

open ChainsSerialBatchingCompletionTime (ChainsSerialBatchingCompletionTimeInstance Job Prec
  completionTime)

/-!
# SERIAL BATCHING WITH CHAINS AND UNIT PROCESSING TIMES TO MINIMIZE TOTAL WEIGHTED COMPLETION
# TIME is NP-complete

INSTANCE: jobs `J₁, …, Jₙ` with unit processing times `pᵢ = 1` and weights `wᵢ ∈ ℤ₀⁺`, a
precedence relation on the jobs that consists of chains (each job has at most one immediate
predecessor and at most one immediate successor), a set-up time `s ∈ ℤ₀⁺`, and a bound
`K ∈ ℤ₀⁺`. QUESTION: is there a sequence of the jobs compatible with the precedence constraints
and a partition of this sequence into consecutive s-batches such that `∑ᵢ wᵢCᵢ ≤ K`? Here each
batch is preceded by a machine set-up of `s` time units, the jobs of a batch are processed one
after another, and every job of a batch completes when the last job of its batch completes
(`Cᵢ` is that time).

This is `1|chains; pⱼ = 1; s-batch|∑ wⱼCⱼ` (Albers and Brucker 1993), the single machine
s-batching problem in Brucker's formulation with chain precedence, unit processing times and
weights. The s-batching model, its precedence relation and its completion times are those of
`WantedExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTimeWanted`
(`1|chains; s-batch|∑ Cᵢ`), whose instance type, jobs, precedence relation `Prec`,
well-formedness condition (listed pairs naming jobs and forming a strict partial order that
consists of chains) and completion time `completionTime` (of a schedule given by a batch index
for every job) are reused unchanged. An instance here is that problem's instance together with
the list of weights; the restriction `pᵢ = 1` and one weight per job are added to `WellFormed`,
and the question weights the completion times. Binary encoding of all numbers.

Albers and Brucker prove NP-hardness in the strong sense. Membership in NP holds because the
batch indices can be taken below `n`, so a schedule is a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SERIAL BATCHING WITH CHAINS AND UNIT PROCESSING TIMES TO MINIMIZE TOTAL WEIGHTED
COMPLETION TIME is NP-complete.** Source: Albers and Brucker (1993) (NP-hardness); Brucker
(2004). -/
public theorem_wanted chainsUnitSerialBatchingWeightedCompletion_npComplete :
    chainsUnitSerialBatchingWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitSerialBatchingWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitSerialBatchingWeightedCompletion
