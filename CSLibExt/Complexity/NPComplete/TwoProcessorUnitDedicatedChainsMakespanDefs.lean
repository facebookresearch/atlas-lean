/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|C_max`: definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994),
259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 2.7;
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4 (the approach of the proof);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with dedicated processors"
(`P2|chains;p_i=1;fix_i|C_max`, minimal NP-hard in the strong sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan

open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)
open MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan
  (UnitDedicatedProcessorInstance)

/-- An instance: an instance `(m, fix, K)` of `P|fix_j, p_j = 1|C_max` and the chain arcs
`(i, j)` (task `i` immediately precedes task `j`). -/
abbrev TwoProcessorUnitDedicatedChainsInstance := UnitDedicatedProcessorInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: it is well-formed for `P|fix_j, p_j = 1|C_max` (nonempty
processor sets without repetitions, processors below `m`, `0 < m`, `0 < K`), `m = 2`, and the
arcs form chains on the tasks. -/
def WellFormed (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  UnitDedicatedProcessorMakespan.WellFormed i.1 ∧ i.1.1 = 2 ∧
    ChainsWellFormed i.1.2.1.length i.2

/-- `s` (start times of the unit tasks) is a schedule: two different tasks with a common
processor run in disjoint unit time intervals, and every chain arc `(j, j')` has
`s j + 1 ≤ s j'`. -/
def IsSchedule (i : TwoProcessorUnitDedicatedChainsInstance) (s : Fin i.1.2.1.length → ℕ) :
    Prop :=
  (∀ j j', j ≠ j' → (∃ k ∈ i.1.2.1.get j, k ∈ i.1.2.1.get j') →
    s j + 1 ≤ s j' ∨ s j' + 1 ≤ s j) ∧
    ∀ j j' : Fin i.1.2.1.length, ((j : ℕ), (j' : ℕ)) ∈ i.2 → s j + 1 ≤ s j'

/-- Some schedule has makespan at most `K`: every `s j + 1 ≤ K`. -/
def TwoProcessorUnitDedicatedChainsMakespanFeasible
    (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  ∃ s, IsSchedule i s ∧ ∀ j, s j + 1 ≤ i.1.2.2

open Classical in
/-- `P2|chains;p_i=1;fix_i|C_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitDedicatedChainsMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitDedicatedChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitDedicatedChainsMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan
