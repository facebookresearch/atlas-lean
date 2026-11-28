/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED TARDINESS,: definitions

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class table "Job-shop problems with nowait" (`J2|p_ij=1;no-wait|∑ w_iT_i`: minimal NP-hard,
in the strong sense, Timkovsky (1998)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedTardiness

/-- An instance: the jobs, job `j` given as `(μ_j1, n_j, d_j, w_j)` (the machine of its first
operation, its number of operations, its due date and its weight), and the bound `K`. -/
abbrev TwoMachineUnitNoWaitJobShopWeightedTardinessInstance := List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the first machine of every job is `1` or `2`, and every job
has at least one operation. -/
def WellFormed (i : TwoMachineUnitNoWaitJobShopWeightedTardinessInstance) : Prop :=
  ∀ job ∈ i.1, (job.1 = 1 ∨ job.1 = 2) ∧ 0 < job.2.1

/-- An operation `O_jk` of the instance: a job `j` and a position `k < n_j`. -/
abbrev Operation (i : TwoMachineUnitNoWaitJobShopWeightedTardinessInstance) : Type :=
  (j : Fin i.1.length) × Fin (i.1.get j).2.1

/-- The machine `μ_jk` of an operation: the first machine of its job at even positions, the
other machine (`3 - μ_j1`) at odd positions. -/
def machine (i : TwoMachineUnitNoWaitJobShopWeightedTardinessInstance) (o : Operation i) :
    ℕ :=
  if o.2.1 % 2 = 0 then (i.1.get o.1).1 else 3 - (i.1.get o.1).1

/-- There is a feasible no-wait schedule with total weighted tardiness at most `K`:
start times `σ` such that two distinct operations on the same machine occupy disjoint unit
intervals, and each operation of a job after the first starts exactly one time unit after the
previous one, together with completion times `C j` equal to the finishing time of the last
operation of job `j`, with `∑_j w_j (C_j - d_j) ≤ K` (truncated subtraction). -/
def TwoMachineUnitNoWaitJobShopWeightedTardinessFeasible
    (i : TwoMachineUnitNoWaitJobShopWeightedTardinessInstance) : Prop :=
  ∃ σ : Operation i → ℕ,
    (∀ o o', o ≠ o' → machine i o = machine i o' → σ o + 1 ≤ σ o' ∨ σ o' + 1 ≤ σ o) ∧
    (∀ j (k k' : Fin (i.1.get j).2.1), k'.1 = k.1 + 1 → σ ⟨j, k'⟩ = σ ⟨j, k⟩ + 1) ∧
    ∃ C : Fin i.1.length → ℕ,
      (∀ j (k : Fin (i.1.get j).2.1), k.1 + 1 = (i.1.get j).2.1 → C j = σ ⟨j, k⟩ + 1) ∧
      ∑ j, (i.1.get j).2.2.2 * (C j - (i.1.get j).2.2.1) ≤ i.2

open Classical in
/-- TWO-MACHINE UNIT-TIME NO-WAIT JOB SHOP, TOTAL WEIGHTED TARDINESS, as a decision
problem over bitstrings. -/
noncomputable def twoMachineUnitNoWaitJobShopWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineUnitNoWaitJobShopWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineUnitNoWaitJobShopWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopWeightedTardiness
