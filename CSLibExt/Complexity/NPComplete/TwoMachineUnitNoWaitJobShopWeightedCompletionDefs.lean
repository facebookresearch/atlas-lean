/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED COMPLETION TIME,: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|p_ij=1;no-wait|∑ w_iC_i`: minimal NP-hard,
in the ordinary sense, Timkovsky (1998)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedCompletion

/-- An instance: the jobs, job `j` given as `(μ_j1, n_j, w_j)` (the machine of its first
operation, its number of operations and its weight), and the bound `K`. -/
abbrev TwoMachineUnitNoWaitJobShopWeightedCompletionInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the first machine of every job is `1` or `2`, and every job
has at least one operation. -/
def WellFormed (i : TwoMachineUnitNoWaitJobShopWeightedCompletionInstance) : Prop :=
  ∀ job ∈ i.1, (job.1 = 1 ∨ job.1 = 2) ∧ 0 < job.2.1

/-- An operation `O_jk` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : TwoMachineUnitNoWaitJobShopWeightedCompletionInstance) : Type :=
  (j : Fin i.1.length) × Fin (i.1.get j).2.1

/-- The machine `μ_jk` of an operation: the first machine of its job at even positions, the
other machine (`3 - μ_j1`) at odd positions. -/
def machine (i : TwoMachineUnitNoWaitJobShopWeightedCompletionInstance) (o : Operation i) :
    ℕ :=
  if o.2.1 % 2 = 0 then (i.1.get o.1).1 else 3 - (i.1.get o.1).1

/-- There is a feasible no-wait schedule with total weighted completion time at most `K`:
start times `σ` such that two distinct operations on the same machine occupy disjoint unit
intervals, and each operation of a job after the first starts exactly one time unit after the
previous one, together with completion times `C j` equal to the finishing time of the last
operation of job `j`, with `∑_j w_j C_j ≤ K`. -/
def TwoMachineUnitNoWaitJobShopWeightedCompletionFeasible
    (i : TwoMachineUnitNoWaitJobShopWeightedCompletionInstance) : Prop :=
  ∃ σ : Operation i → ℕ,
    (∀ o o', o ≠ o' → machine i o = machine i o' → σ o + 1 ≤ σ o' ∨ σ o' + 1 ≤ σ o) ∧
    (∀ j (k k' : Fin (i.1.get j).2.1), k'.1 = k.1 + 1 → σ ⟨j, k'⟩ = σ ⟨j, k⟩ + 1) ∧
    ∃ C : Fin i.1.length → ℕ,
      (∀ j (k : Fin (i.1.get j).2.1), k.1 + 1 = (i.1.get j).2.1 → C j = σ ⟨j, k⟩ + 1) ∧
      ∑ j, (i.1.get j).2.2 * C j ≤ i.2

open Classical in
/-- TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED COMPLETION TIME, as a decision
problem over bitstrings. -/
noncomputable def twoMachineUnitNoWaitJobShopWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineUnitNoWaitJobShopWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineUnitNoWaitJobShopWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedCompletion
