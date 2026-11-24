/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (`F2|no-wait|Lmax` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems with no-wait" (`F2|no-wait|Lmax`, minimal NP-hard, credited to Röck
1984);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (the deadline version, solvable in polynomial time for `m = 2`, Gilmore and Gomory 1964).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness

/-!
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete

INSTANCE: a set of jobs `J₁, …, Jₙ` in a two-machine flow shop, job `Jⱼ` consisting of an
operation on machine `M₁` with processing time `pⱼ₁` followed by an operation on machine `M₂`
with processing time `pⱼ₂`, a due date `dⱼ` for each job, and an integer `y`; all processing
times and due dates are nonnegative integers. QUESTION: is there a schedule (each machine
handles at most one job at a time, and the operation of `Jⱼ` on `M₂` starts only after its
operation on `M₁` is completed, with no wait: it starts exactly when that operation is
completed) whose maximum lateness `L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`,
`Cⱼ` being the completion time of `Jⱼ` on `M₂`?

This is `F2|no-wait|Lmax` (`n|2|F,no wait|Lmax` in the notation of Lenstra, Rinnooy Kan, and Brucker
1977, who also define the data and the recognition version "is there a schedule with value `≤ y`").
With the deadline objective in place of `L_max` the two-machine no-wait problem is solvable in
polynomial time (Gilmore and Gomory 1964; Garey and Johnson, [SS16]). A schedule is given by the
starting times `s₁ⱼ`, `s₂ⱼ ∈ ℤ₀⁺` of the two operations of job `j`. That each machine handles at
most one job at a time is read, as in `FlowShopSchedulingWanted`, as non-overlap of the operations
of two distinct jobs on the same machine (`s + p ≤ s'` or `s' + p' ≤ s`). The bound `y` is an
integer, encoded as a pair `(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in `ZeroOneILPWanted`;
`Cⱼ - dⱼ ≤ y⁺ - y⁻` is stated over `ℕ` as `Cⱼ + y⁻ ≤ dⱼ + y⁺`. The flow-shop schedule predicates of
`FlowShopSchedulingWanted` and `NoWaitFlowShopSchedulingWanted` carry the overall deadline in their
instance and schedule conditions, so they do not apply to a lateness objective. Jobs are `Fin n`.
Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs, job `j` being the `j`-th triple `(pⱼ₁, pⱼ₂, dⱼ)` of its processing
times on `M₁` and `M₂` and its due date, and the bound `y` as a pair `(y⁺, y⁻)` with
`y = y⁺ - y⁻`. -/
abbrev TwoProcessorNoWaitFlowShopMaximumLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Type := Fin i.1.length

/-- The processing time `pⱼ₁` of job `j` on machine `M₁`. -/
def time₁ (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The processing time `pⱼ₂` of job `j` on machine `M₂`. -/
def time₂ (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Every instance is well-formed: processing times and due dates are nonnegative integers by
their type, and the bound `y` is an arbitrary integer. -/
def WellFormed (_i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Prop := True

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂`, runs one operation at
a time on each machine, starts each job on `M₂` exactly when it is completed on `M₁`, and
completes every job `j` on `M₂` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def TwoProcessorNoWaitFlowShopMaximumLatenessFeasible
    (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + time₁ i j ≤ s₁ k ∨ s₁ k + time₁ i k ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + time₂ i j ≤ s₂ k ∨ s₂ k + time₂ i k ≤ s₂ j) ∧
    (∀ j, s₂ j = s₁ j + time₁ i j) ∧
    ∀ j, s₂ j + time₂ i j + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitFlowShopMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorNoWaitFlowShopMaximumLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitFlowShopMaximumLatenessFeasible i)
  | none => false

/-- **TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS is NP-complete.** Source: Röck (1984);
Brucker and Knust's classification (`F2|no-wait|Lmax`). -/
public theorem_wanted twoProcessorNoWaitFlowShopMaximumLateness_npComplete :
    twoProcessorNoWaitFlowShopMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorNoWaitFlowShopMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness
