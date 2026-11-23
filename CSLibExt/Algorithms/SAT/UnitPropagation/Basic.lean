/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.DPLL.Correctness

/-!
# Soundness of unit-propagation conflicts

One unit-propagation step picks a unit clause `[l]` and restricts the formula by `l`
(`Cslib.Logic.PL.CNF.restrict`): clauses containing `l` disappear and the variable of `l`
is removed from every other clause. `UPConflict φ` states that iterated unit propagation
from `φ` reaches a formula containing the empty clause. Such a conflict certifies that `φ`
is unsatisfiable.

## Main definitions

- `UPConflict φ` : iterated unit propagation from `φ` reaches the empty clause.

## Main results

- `not_cnfSat_of_upConflict` : a unit-propagation conflict refutes `CNFSat φ`.
- `upConflict_unsat` : no assignment satisfies a formula with a unit-propagation conflict.
-/

@[expose] public section

namespace Cslib.Algorithms.SAT.UnitPropagation

open Cslib.Logic.PL

/-- Unit-propagation conflict derivation: either the formula already contains the empty
clause, or it has a unit clause `[l]` and the formula restricted by `l` derives a
conflict. -/
inductive UPConflict : CNF → Prop
  | empty (formula : CNF) (hempty : [] ∈ formula) : UPConflict formula
  | step (formula : CNF) (literal : Nat × Bool) (hunit : [literal] ∈ formula)
      (hconflict : UPConflict (formula.restrict literal)) : UPConflict formula

/-- Soundness of unit propagation: a formula from which unit propagation derives a
conflict is unsatisfiable. -/
theorem not_cnfSat_of_upConflict {formula : CNF} (h : UPConflict formula) :
    ¬CNFSat formula := by
  induction h with
  | empty formula hempty => exact DPLL.not_sat_of_mem_empty hempty
  | step formula literal hunit _ ih =>
      exact fun hsat => ih ((CNF.sat_iff_restrict_of_unit hunit).mp hsat)

/-- Soundness of unit propagation for the named CNF semantics: no assignment satisfies a
formula from which unit propagation derives a conflict. -/
theorem upConflict_unsat {formula : CNF} (h : UPConflict formula) :
    ¬∃ assignment, formula.Satisfies assignment := by
  rw [← cnfSat_iff_exists_satisfies]
  exact not_cnfSat_of_upConflict h

end Cslib.Algorithms.SAT.UnitPropagation
