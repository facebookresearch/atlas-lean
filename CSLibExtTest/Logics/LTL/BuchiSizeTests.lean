/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.BuchiSize

/-!
# Tests for the exponential bound on LTL Büchi automata

Concrete sizes, the exact tableau count `2 ^ |φ|`, and the bound instantiated at Vardi's
alphabet `2^Prop` (`Set Atom` read by membership).
-/

@[expose] public section

namespace Cslib.LTL.BuchiSizeTests

open Automata.ωAcceptor

/-- `p U q` has three occurrences and `2 ^ 3 = 8` tableau states. -/
example : (Formula.until (.atom 0) (.atom 1) : Formula ℕ).size = 3 := rfl

example : Nat.card (Tableau.State (.until (.atom 0) (.atom 1) : Formula ℕ)) = 8 := by
  rw [Tableau.natCard_state]
  rfl

/-- `G F p` unfolds to `¬ (⊤ U ¬ (⊤ U p))`, of size 7, with two until obligations. -/
example : (Formula.always (Formula.eventually (.atom 0)) : Formula ℕ).size = 7 := rfl

example : Nat.card (Tableau.State (Formula.always (Formula.eventually (.atom 0)) : Formula ℕ) ×
    Fin (Tableau.obligationCount
      (Formula.always (Formula.eventually (.atom 0)) : Formula ℕ) + 1)) = 384 := by
  rw [Nat.card_prod, Tableau.natCard_state, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

example : Nat.card (Tableau.State (Formula.always (Formula.eventually (.atom 0)) : Formula ℕ) ×
    Fin (Tableau.obligationCount
      (Formula.always (Formula.eventually (.atom 0)) : Formula ℕ) + 1)) ≤ 4 ^ 7 :=
  Tableau.natCard_buchi_state_le _

/-- Vardi's form: letters are sets of atoms, read by membership. -/
example (φ : Formula ℕ) :
    ∃ (S : Type) (_ : Finite S) (a : Automata.NA.Buchi S (Set ℕ)),
      Nat.card S ≤ 4 ^ φ.size ∧ language a = Word.language (fun x p => p ∈ x) φ :=
  exists_buchi_card_le _ φ

end Cslib.LTL.BuchiSizeTests
