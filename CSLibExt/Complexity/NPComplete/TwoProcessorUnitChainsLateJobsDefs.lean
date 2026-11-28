/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES, UNIT CHAINS, NUMBER OF LATE JOBS `P2|chains;p_i=1|ΣU_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|chains;p_i=1|ΣU_i, ΣT_i` (minimal NP-hard in the strong
sense, justified by the single-machine problem);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1 (`1|chains, p_j = 1|ΣU_j`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TardyTasksUnitChainsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsLateJobs

open TardyTasksUnitChains (TardyTasksUnitChainsInstance Task deadline Prec ImmediatePredecessor)

/-- Well-formedness of an instance: every listed pair names two jobs, the listed pairs form a
strict partial order, and the order consists of chains (every job has at most one immediate
predecessor and at most one immediate successor). Due dates and `K` are arbitrary natural
numbers. -/
def WellFormed (i : TardyTasksUnitChainsInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Task i) (Prec i) ∧
    (∀ t a b, ImmediatePredecessor i a t → ImmediatePredecessor i b t → a = b) ∧
    ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- Some two-machine schedule of the unit jobs (at most two start at each time `u`) obeys the
precedence constraints and has at most `K` late jobs, those with `σ(t) + 1 > d(t)`. -/
def TwoProcessorUnitChainsLateJobsFeasible (i : TardyTasksUnitChainsInstance) : Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (Finset.univ.filter fun t => σ t = u).card ≤ 2) ∧
    (∀ t t', Prec i t t' → σ t + 1 ≤ σ t') ∧
    (Finset.univ.filter fun t => deadline i t < σ t + 1).card ≤ i.2.2

open Classical in
/-- `P2|chains;p_i=1|ΣU_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitChainsLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TardyTasksUnitChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitChainsLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsLateJobs
