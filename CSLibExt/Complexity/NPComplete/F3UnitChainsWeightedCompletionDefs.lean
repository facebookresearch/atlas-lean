/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP `F3|p_ij=1;chains|Σw_iC_i`: definitions

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8; recorded as strongly NP-hard (a minimal NP-hard problem) in
P. Brucker and S. Knust, *Complexity results for scheduling problems*, class "Flow-shop problems
without preemption" (University of Osnabrück,
http://www2.informatik.uni-osnabrueck.de/knust/class/), problem `F3|p_ij=1;chains|Σw_iC_i`,
credited to Tanaev et al. (1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletion

open F3UnitChainsLateJobs (ChainsWellFormed IsSchedule)

/-- An instance `(w, chains, K)`: the weights `w_i` of the jobs `0, …, n - 1` (`n` is the length of
the list), the chain arcs `(i, j)` (job `i` immediately precedes job `j`), and the bound `K`. -/
abbrev F3UnitChainsWeightedCompletionInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness: the arcs form chains on the jobs (`F3UnitChainsLateJobs.ChainsWellFormed`). -/
def WellFormed (i : F3UnitChainsWeightedCompletionInstance) : Prop :=
  ChainsWellFormed i.1.length i.2.1

/-- Some feasible schedule (`F3UnitChainsLateJobs.IsSchedule`) has total weighted completion time
at most `K`, with `C_j = S j 2 + 1`. -/
def F3UnitChainsWeightedCompletionFeasible (i : F3UnitChainsWeightedCompletionInstance) : Prop :=
  ∃ S : Fin i.1.length → Fin 3 → ℕ, IsSchedule i.1.length i.2.1 S ∧
    ∑ j, i.1.get j * (S j 2 + 1) ≤ i.2.2

open Classical in
/-- `F3|p_ij=1;chains|Σw_iC_i` as a decision problem over bitstrings. -/
noncomputable def f3UnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := F3UnitChainsWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ F3UnitChainsWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.F3UnitChainsWeightedCompletion
