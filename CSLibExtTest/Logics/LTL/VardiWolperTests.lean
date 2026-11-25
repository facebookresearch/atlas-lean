/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.VardiWolper

namespace Cslib.LTL.VardiWolperTests

open Cslib.LTL

/-- Doubly nested until over a one-element atom type. -/
def nestedUntil : Formula (Fin 1) := .until (.until .top .top) .top

/-- A single atom has exactly the two Boolean annotations. -/
example : Nat.card (Tableau.State (Formula.atom (0 : Fin 1))) = 2 :=
  Tableau.card_state _

/-- The doubly nested until has two obligations. -/
example : Tableau.obligationCount nestedUntil = 2 := rfl

/-- Its size is five. -/
example : Tableau.formulaSize nestedUntil = 5 := rfl

/-- The degeneralized state count for that formula is exactly `2 ^ 5 * 3`. -/
example :
    Nat.card (Tableau.State nestedUntil ×
      Fin (Tableau.obligationCount nestedUntil + 1)) = 96 := by
  have hsize : Tableau.formulaSize nestedUntil = 5 := rfl
  have hob : Tableau.obligationCount nestedUntil = 2 := rfl
  rw [Nat.card_prod, Tableau.card_state, Nat.card_fin, hsize, hob]
  rfl

/-- The Vardi-Wolper theorem applies to a concrete formula. -/
example :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set (Fin 1))),
      Automata.ωAcceptor.language a =
          Word.language (fun s a => a ∈ s) (Formula.atom (0 : Fin 1)) ∧
        Nat.card S ≤ 2 ^ (2 * Tableau.formulaSize (Formula.atom (0 : Fin 1))) :=
  vardi_wolper _

/-- The safety theorem applies to `G (p ∨ X q)`, the shape the restricted
safety fragment cannot state. -/
example :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set (Fin 2))),
      Automata.ωAcceptor.language a =
        Word.language (fun s a => a ∈ s)
          (SafetyExt.always
            (SafetyExt.or (SafetyExt.prop (.atom 0))
              (SafetyExt.next (SafetyExt.prop (.atom 1))))).toLTL :=
  safety_general_buchi _



/-- The bound also applies at a higher atom universe (`Formula Type`). -/
example :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set Type)),
      Automata.ωAcceptor.language a =
          Word.language (fun s a => a ∈ s) (Formula.atom (ℕ : Type)) ∧
        Nat.card S ≤ 2 ^ (2 * Tableau.formulaSize (Formula.atom (ℕ : Type))) :=
  vardi_wolper _
end Cslib.LTL.VardiWolperTests
