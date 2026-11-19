/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X,
Theorem 1(k) and Theorem 4(c) in the preprint, Mathematisch Centrum report BW 43/75 (1975),
https://ir.cwi.nl/pub/9725 (KNAPSACK reduces to `n|1|r_n ≥ 0|Lmax`, which reduces to
`n|2|F|Lmax`: `F2||Lmax`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2||Lmax`, minimal NP-hard, credited to Lenstra,
Rinnooy Kan, and Brucker 1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLateness

/-!
# TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete

INSTANCE: a set of jobs `J₁, …, Jₙ` in a two-machine flow shop, job `Jⱼ` consisting of an
operation on machine `M₁` with processing time `pⱼ₁` followed by an operation on machine `M₂`
with processing time `pⱼ₂`, a due date `dⱼ` for each job, and an integer `y`; all processing
times and due dates are nonnegative integers. QUESTION: is there a schedule (each machine
handles at most one job at a time, and the operation of `Jⱼ` on `M₂` starts only after its
operation on `M₁` is completed) whose maximum lateness `L_max = maxⱼ (Cⱼ - dⱼ)` is at most `y`,
`Cⱼ` being the completion time of `Jⱼ` on `M₂`?

This is `F2||Lmax` in the notation of Lenstra, Rinnooy Kan, and Brucker (`n|2|F|Lmax`), with the
optimization problem replaced, as in their paper, by the recognition problem "is there a
schedule with value `≤ y`". A schedule is given by the starting times `s₁ⱼ`, `s₂ⱼ ∈ ℤ₀⁺` of the
two operations of job `j`. That each machine handles at most one job at a time is read, as in
`FlowShopSchedulingWanted`, as non-overlap of the operations of two distinct jobs on the same
machine (`s + p ≤ s'` or `s' + p' ≤ s`). The bound `y` is an integer, encoded as a pair
`(y⁺, y⁻)` of naturals representing `y⁺ - y⁻`, as in `ZeroOneILPWanted`; `Cⱼ - dⱼ ≤ y⁺ - y⁻` is
stated over `ℕ` as `Cⱼ + y⁻ ≤ dⱼ + y⁺`. The flow-shop schedule predicates of
`FlowShopSchedulingWanted` and `NoWaitFlowShopSchedulingWanted` carry the overall deadline in
their instance and schedule conditions, so they do not apply to a lateness objective. Jobs are
`Fin n`. Binary encoding of all numbers.

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
abbrev TwoProcessorFlowShopMaximumLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : TwoProcessorFlowShopMaximumLatenessInstance) : Type := Fin i.1.length

/-- The processing time `pⱼ₁` of job `j` on machine `M₁`. -/
def time₁ (i : TwoProcessorFlowShopMaximumLatenessInstance) (j : Job i) : ℕ := (i.1.get j).1

/-- The processing time `pⱼ₂` of job `j` on machine `M₂`. -/
def time₂ (i : TwoProcessorFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : TwoProcessorFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Every instance is well-formed: processing times and due dates are nonnegative integers by
their type, and the bound `y` is an arbitrary integer. -/
def WellFormed (_i : TwoProcessorFlowShopMaximumLatenessInstance) : Prop := True

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂`, runs one operation at
a time on each machine, starts each job on `M₂` only after it is completed on `M₁`, and
completes every job `j` on `M₂` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def TwoProcessorFlowShopMaximumLatenessFeasible
    (i : TwoProcessorFlowShopMaximumLatenessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + time₁ i j ≤ s₁ k ∨ s₁ k + time₁ i k ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + time₂ i j ≤ s₂ k ∨ s₂ k + time₂ i k ≤ s₂ j) ∧
    (∀ j, s₁ j + time₁ i j ≤ s₂ j) ∧
    ∀ j, s₂ j + time₂ i j + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS as a decision problem over bitstrings. -/
noncomputable def twoProcessorFlowShopMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFlowShopMaximumLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFlowShopMaximumLatenessFeasible i)
  | none => false

/-- **TWO-PROCESSOR FLOW-SHOP MAXIMUM LATENESS is NP-complete.** Source: Lenstra, Rinnooy Kan,
and Brucker (1977), Theorems 1(k) and 4(c); Brucker and Knust's classification (`F2||Lmax`). -/
public theorem_wanted twoProcessorFlowShopMaximumLateness_npComplete :
    twoProcessorFlowShopMaximumLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopMaximumLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLateness
