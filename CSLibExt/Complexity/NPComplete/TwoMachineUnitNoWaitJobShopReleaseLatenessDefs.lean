/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS,: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|p_ij=1;r_i;no-wait|L_max`: minimal NP-hard,
in the strong sense, Timkovsky (1998)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseLateness

/-- An instance: the jobs, job `j` given as `(μ_j1, n_j, r_j, d_j)` (the machine of its first
operation, its number of operations, its release date and its due date as a pair
`(d⁺, d⁻)` with `d_j = d⁺ - d⁻`), and the bound `K` as a pair `(K⁺, K⁻)` with
`K = K⁺ - K⁻`. -/
abbrev TwoMachineUnitNoWaitJobShopReleaseLatenessInstance :=
  List (ℕ × ℕ × ℕ × (ℕ × ℕ)) × (ℕ × ℕ)

/-- Well-formedness of an instance: the first machine of every job is `1` or `2`, and every job
has at least one operation. -/
def WellFormed (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Prop :=
  ∀ job ∈ i.1, (job.1 = 1 ∨ job.1 = 2) ∧ 0 < job.2.1

/-- An operation `O_jk` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Type :=
  (j : Fin i.1.length) × Fin (i.1.get j).2.1

/-- The machine `μ_jk` of an operation: the first machine of its job at even positions, the
other machine (`3 - μ_j1`) at odd positions. -/
def machine (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) (o : Operation i) :
    ℕ :=
  if o.2.1 % 2 = 0 then (i.1.get o.1).1 else 3 - (i.1.get o.1).1

/-- There is a feasible no-wait schedule with maximum lateness at most `K`: start times `σ`
such that two distinct operations on the same machine occupy disjoint unit intervals, each
operation of a job after the first starts exactly one time unit after the previous one, the
first operation of every job `j` starts no earlier than `r_j`, and the last operation of every
job `j` completes at a time `C_j` with `C_j - d_j ≤ K`. -/
def TwoMachineUnitNoWaitJobShopReleaseLatenessFeasible
    (i : TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) : Prop :=
  ∃ σ : Operation i → ℕ,
    (∀ o o', o ≠ o' → machine i o = machine i o' → σ o + 1 ≤ σ o' ∨ σ o' + 1 ≤ σ o) ∧
    (∀ j (k k' : Fin (i.1.get j).2.1), k'.1 = k.1 + 1 → σ ⟨j, k'⟩ = σ ⟨j, k⟩ + 1) ∧
    (∀ j (k : Fin (i.1.get j).2.1), k.1 = 0 → (i.1.get j).2.2.1 ≤ σ ⟨j, k⟩) ∧
    ∀ j (k : Fin (i.1.get j).2.1), k.1 + 1 = (i.1.get j).2.1 →
      ((σ ⟨j, k⟩ + 1 : ℕ) : ℤ) - (((i.1.get j).2.2.2.1 : ℤ) - (i.1.get j).2.2.2.2) ≤
        (i.2.1 : ℤ) - i.2.2

open Classical in
/-- TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP WITH RELEASE DATES, MAXIMUM LATENESS, as a decision
problem over bitstrings. -/
noncomputable def twoMachineUnitNoWaitJobShopReleaseLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineUnitNoWaitJobShopReleaseLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineUnitNoWaitJobShopReleaseLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseLateness
