/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT-TIME PARALLEL-TASK SCHEDULING, TOTAL COMPLETION TIME (P|sizeⱼ, pⱼ = 1|∑ Cⱼ): definitions

Source:
M. Drozdowski and P. Dell'Olmo, "Scheduling multiprocessor tasks for mean flow time criterion",
Computers & Operations Research 27 (2000), 571-585, doi:10.1016/S0305-0548(99)00048-9 (abstract:
"When tasks have unit execution time and the number of processors is arbitrary the problem is
shown to be computationally hard");
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multiprocessor task problems with
parallel processors", which lists `P|pᵢ = 1; sizeᵢ|∑ Cᵢ` as minimal NP-hard with this
attribution.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitParallelTaskCompletionTime

/-- An instance: the number `m` of processors, the sizes `sizeⱼ` of the tasks, and the bound
`K`. -/
abbrev UnitParallelTaskInstance := ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: there is at least one processor (`0 < m`), every size
satisfies `1 ≤ sizeⱼ ≤ m`, and `0 < K`. -/
def WellFormed (i : UnitParallelTaskInstance) : Prop :=
  0 < i.1 ∧ (∀ q ∈ i.2.1, 0 < q ∧ q ≤ i.1) ∧ 0 < i.2.2

/-- There are start times `s` such that at every time `t` the tasks started at `t` (those
processed during `[t, t + 1)`) need at most `m` processors in total, and the total completion
time `∑ⱼ (s j + 1)` is at most `K`. -/
def UnitParallelTaskCompletionTimeFeasible (i : UnitParallelTaskInstance) : Prop :=
  ∃ s : Fin i.2.1.length → ℕ,
    (∀ t, ((Finset.univ.filter fun j => s j = t).sum fun j => i.2.1.get j) ≤ i.1) ∧
      ∑ j, (s j + 1) ≤ i.2.2

open Classical in
/-- `P|sizeⱼ, pⱼ = 1|∑ Cⱼ` as a decision problem over bitstrings. -/
noncomputable def unitParallelTaskCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitParallelTaskInstance) x with
  | some i => decide (WellFormed i ∧ UnitParallelTaskCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitParallelTaskCompletionTime
