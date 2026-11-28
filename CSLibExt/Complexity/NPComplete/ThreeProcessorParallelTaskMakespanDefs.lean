/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THREE-PROCESSOR PARALLEL TASK SCHEDULING `P3|size_i|Cmax`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING (the
case in which every task has size `1`);
J. Du and J. Y.-T. Leung, "Complexity of scheduling parallel task systems", SIAM Journal on
Discrete Mathematics 2 (1989), 473-487, doi:10.1137/0402042 (pseudo-polynomial algorithm for
three processors);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Section 11.4 (tasks of type
`sizeᵢ`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeProcessorParallelTaskMakespan

/-- An instance: the tasks `(pᵢ, sizeᵢ)` (processing time and size), one per entry, and the
bound `K`. -/
abbrev ThreeProcessorParallelTaskMakespanInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness: every task has a positive processing time and size `1`, `2` or `3`. -/
def WellFormed (i : ThreeProcessorParallelTaskMakespanInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 3

/-- There are start times `s` such that every task completes by `K`, and at every time `t` the
tasks running at `t` (`s j ≤ t < s j + p_j`) have total size at most `3`. -/
def ThreeProcessorParallelTaskMakespanFeasible
    (i : ThreeProcessorParallelTaskMakespanInstance) : Prop :=
  ∃ s : Fin i.1.length → ℕ, (∀ j, s j + (i.1.get j).1 ≤ i.2) ∧
    ∀ t : ℕ, ∑ j ∈ Finset.univ.filter (fun j => s j ≤ t ∧ t < s j + (i.1.get j).1),
      (i.1.get j).2 ≤ 3

open Classical in
/-- `P3|size_i|Cmax` as a decision problem over bitstrings. -/
noncomputable def threeProcessorParallelTaskMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeProcessorParallelTaskMakespanInstance) x with
  | some i => decide (WellFormed i ∧ ThreeProcessorParallelTaskMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeProcessorParallelTaskMakespan
