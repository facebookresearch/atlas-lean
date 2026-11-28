/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES, UNIT CHAINS, TOTAL TARDINESS `P2|chains;p_i=1|ΣT_i`: definitions

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pqr_nop` (parallel machine
problems without preemption), entry `P2|chains;p_i=1|ΣU_i, ΣT_i` (minimal NP-hard in the strong
sense, justified by the single-machine problem);
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, p_j = 1|ΣT_j` is NP-hard in the strong sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChainsUnitTaskTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsTotalTardiness

open PrecedenceUnitTaskTardiness (PrecedenceUnitTaskTardinessInstance Prec)
open SequencingToMinimizeWeightedTardiness (Task taskLength weight deadline)
open ChainsUnitTaskTardiness (IsChainLike)

/-- Well-formedness of an instance: every job has length and weight `1`, every listed pair names
two jobs, the listed pairs form a strict partial order, and the order is chain-like. Due dates
and `K` are arbitrary natural numbers. -/
def WellFormed (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  (∀ x ∈ i.1.1, x.1 = 1 ∧ x.2.1 = 1) ∧
    (∀ p ∈ i.2, p.1 < i.1.1.length ∧ p.2 < i.1.1.length) ∧
    IsStrictOrder (Task i.1) (Prec i) ∧ IsChainLike i

/-- Some two-machine schedule (at every time `u` at most two jobs with `σ(t) ≤ u < σ(t) + l(t)`)
obeys the precedence constraints and has total tardiness at most `K`: the sum, over the jobs with
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is at most `K`. -/
def TwoProcessorUnitChainsTotalTardinessFeasible (i : PrecedenceUnitTaskTardinessInstance) :
    Prop :=
  ∃ σ : Task i.1 → ℕ,
    (∀ u, (Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + taskLength i.1 t).card ≤ 2) ∧
    (∀ t t', Prec i t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i.1 t < σ t + taskLength i.1 t),
      (σ t + taskLength i.1 t - deadline i.1 t) * weight i.1 t ≤ i.1.2

open Classical in
/-- `P2|chains;p_i=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitChainsTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitTaskTardinessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitChainsTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsTotalTardiness
