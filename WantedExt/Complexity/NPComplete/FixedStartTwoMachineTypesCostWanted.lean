/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times) is NP-complete

Source:
K. Nakajima, S. L. Hakimi and J. K. Lenstra, "Complexity results for scheduling tasks in fixed
intervals on two types of machines", SIAM Journal on Computing 11 (1982), 512-520,
doi:10.1137/0211040, Theorem 2 ("The FST problem is NP-hard in the strong sense").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedStartTwoMachineTypesCost

/-!
# SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times) is NP-complete

INSTANCE: tasks `T₁, …, Tₙ`, task `Tⱼ` with release date `rⱼ`, processing time `pⱼ` on a slow
machine and `qⱼ < pⱼ` on a fast machine; machine costs `Cˢ < Cᶠ` (slow, fast); a bound `B`. All
numbers are integers.
QUESTION: is there a feasible schedule, on `mˢ` slow and `mᶠ` fast machines, of total cost
`mˢ Cˢ + mᶠ Cᶠ ≤ B`? A task on a slow machine occupies `[rⱼ, rⱼ + pⱼ)` ("the tasks assigned to
slow machines have to start at their release dates in order to meet their deadlines"
`dⱼ = rⱼ + pⱼ`), a task on a fast machine occupies `[rⱼ, rⱼ + qⱼ)` (FST: "`Tⱼ` has to start at time
`rⱼ`"), tasks run without preemption, and a machine executes at most one task at a time.

This is the decision version of the FST problem of Nakajima, Hakimi and Lenstra (1982), whose
Theorem 2 proves it NP-hard in the strong sense (from NUMERICAL MATCHING WITH TARGET SUMS, with
`Cᶠ / Cˢ = (t + 2) / (t + 1)` and `pⱼ / qⱼ = z` for all `j`); the case of equal release dates is
solvable in `O(n)` time (their Theorem 3).

A schedule assigns every task to a machine, slow machines `Fin mˢ` and fast machines `Fin mᶠ`
(`Sum.inl` and `Sum.inr`). Two distinct tasks on the same machine must not overlap: one ends no
later than the other starts (a task may start when another ends). Processing times and the slow
cost are required to be positive; the source's reduction uses positive values only, so its
hardness proof applies. Numbers use the canonical binary encoding.

Membership in NP: the certificate is the assignment; at most `n` machines of each type are
useful, and disjointness is checked pairwise.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tasks `(rⱼ, pⱼ, qⱼ)` (release date, slow and fast processing time), the slow
machine cost `Cˢ`, the fast machine cost `Cᶠ`, and the bound `B`. -/
abbrev FixedStartTwoMachineTypesCostInstance := List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- Well-formedness of an instance: every task has `0 < qⱼ < pⱼ`, and `0 < Cˢ < Cᶠ`. -/
def WellFormed (i : FixedStartTwoMachineTypesCostInstance) : Prop :=
  (∀ t ∈ i.1, 0 < t.2.2 ∧ t.2.2 < t.2.1) ∧ 0 < i.2.1 ∧ i.2.1 < i.2.2.1

/-- The release date of task `j`. -/
def release (i : FixedStartTwoMachineTypesCostInstance) (j : Fin i.1.length) : ℕ :=
  (i.1.get j).1

/-- The processing time of task `j` on a machine of the given type: `pⱼ` on a slow machine
(`Sum.inl`), `qⱼ` on a fast machine (`Sum.inr`). -/
def duration {ms mf : ℕ} (i : FixedStartTwoMachineTypesCostInstance) (j : Fin i.1.length) :
    Fin ms ⊕ Fin mf → ℕ
  | Sum.inl _ => (i.1.get j).2.1
  | Sum.inr _ => (i.1.get j).2.2

/-- A feasible schedule of total cost at most `B`: `mˢ` slow and `mᶠ` fast machines with
`mˢ Cˢ + mᶠ Cᶠ ≤ B`, and an assignment `σ` of tasks to machines such that two distinct tasks on
the same machine do not overlap, each task starting at its release date. -/
def FixedStartTwoMachineTypesCostFeasible (i : FixedStartTwoMachineTypesCostInstance) : Prop :=
  ∃ (ms mf : ℕ) (σ : Fin i.1.length → Fin ms ⊕ Fin mf), ms * i.2.1 + mf * i.2.2.1 ≤ i.2.2.2 ∧
    ∀ j k, j ≠ k → σ j = σ k →
      release i j + duration i j (σ j) ≤ release i k ∨
        release i k + duration i k (σ k) ≤ release i j

open Classical in
/-- SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times) as a decision
problem over bitstrings. -/
noncomputable def fixedStartTwoMachineTypesCostDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedStartTwoMachineTypesCostInstance) x with
  | some i => decide (WellFormed i ∧ FixedStartTwoMachineTypesCostFeasible i)
  | none => false

/-- **SCHEDULING TO MINIMIZE MACHINE COST (two machine types, fixed start times) is
NP-complete.** Source: Nakajima, Hakimi and Lenstra (1982), Theorem 2. -/
public theorem_wanted fixedStartTwoMachineTypesCost_npComplete :
    fixedStartTwoMachineTypesCostDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fixedStartTwoMachineTypesCostDec

end MetaMathlibExt.Complexity.NPComplete.FixedStartTwoMachineTypesCost
