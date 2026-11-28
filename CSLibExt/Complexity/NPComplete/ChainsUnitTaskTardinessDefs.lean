/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times: definitions

Source:
J. Y.-T. Leung and G. H. Young, "Minimizing total tardiness on a single machine with
precedence constraints", ORSA Journal on Computing 2 (1990), 346-352,
doi:10.1287/ijoc.2.4.346 (`1|chains, pⱼ = 1|∑ Tⱼ`);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3 (the scheduling model and the chain-like precedence relation);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (single machine problems:
`1|chains; pᵢ = 1|∑ Tᵢ`, minimal NP-hard in the strong sense, Leung and Young (1990)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PrecedenceUnitTaskTardinessDefs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitTaskTardiness

open PrecedenceUnitTaskTardiness (PrecedenceUnitTaskTardinessInstance Prec
  PrecedenceUnitTaskTardinessFeasible)
open SequencingToMinimizeWeightedTardiness (Task)

/-- `t` is an immediate predecessor of `t'` (and `t'` an immediate successor of `t`): `t → t'`,
and no job `c` has `t → c → t'`. -/
def ImmediatePredecessor (i : PrecedenceUnitTaskTardinessInstance) (t t' : Task i.1) : Prop :=
  Prec i t t' ∧ ∀ c, ¬ (Prec i t c ∧ Prec i c t')

/-- The precedence relation is chain-like: no job has more than one immediate predecessor, and
no job has more than one immediate successor. -/
def IsChainLike (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  (∀ t' a b, ImmediatePredecessor i a t' → ImmediatePredecessor i b t' → a = b) ∧
    ∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b

/-- Well-formedness of an instance: it is a well-formed instance of `1|prec, pⱼ = 1|∑ Tⱼ`
(unit lengths and weights, positive due dates and `K`, listed pairs naming jobs and forming a
strict partial order), and the precedence relation is chain-like. -/
def WellFormed (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  PrecedenceUnitTaskTardiness.WellFormed i ∧ IsChainLike i

open Classical in
/-- SINGLE-MACHINE TOTAL TARDINESS with chains and unit processing times as a decision problem
over bitstrings. -/
noncomputable def chainsUnitTaskTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitTaskTardinessInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceUnitTaskTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitTaskTardiness
