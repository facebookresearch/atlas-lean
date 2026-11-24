/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean

open MetaMathlibExt

-- Before negation, `x 0 && !x 1` is increasing in coordinate 0 and decreasing in coordinate 1.
example : IsUnateBoolFun (fun x : Fin 2 → Bool => !(x 0 && !x 1)) := by
  apply isUnateBoolFun_not
  unfold IsUnateBoolFun IsBoolFunIncreasingIn IsBoolFunDecreasingIn
  decide

-- With no variables the unique input gives one function of each weight, zero and one.
example : Nat.card {f : (Fin 0 → Bool) → Bool // Monotone f ∧ boolFunWeight f = 0} = 1 := by
  rw [card_monotone_boolFun_weight_symm 0 0 (by decide), Nat.card_eq_fintype_card]
  decide

-- On two variables the unique monotone functions of weights one and three are AND and OR.
example : Nat.card {f : (Fin 2 → Bool) → Bool // Monotone f ∧ boolFunWeight f = 3} = 1 := by
  rw [card_monotone_boolFun_weight_symm 2 3 (by decide), Nat.card_eq_fintype_card]
  decide

-- At arity zero, output negation exchanges the two constant functions.
example : Nat.card {f : (Fin 0 → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = 1} = 1 := by
  rw [card_unate_boolFun_weight_symm 0 1 (by decide)]
  unfold IsUnateBoolFun IsBoolFunIncreasingIn IsBoolFunDecreasingIn
  rw [Nat.card_eq_fintype_card]
  decide

-- The function true only at (true, false) gives a weight-three witness by symmetry.
example : 0 < Nat.card {f : (Fin 2 → Bool) → Bool // IsUnateBoolFun f ∧ boolFunWeight f = 3} := by
  rw [card_unate_boolFun_weight_symm 2 3 (by decide), Nat.card_pos_iff]
  refine ⟨⟨⟨fun x => x 0 && !x 1, ?_, ?_⟩⟩, inferInstance⟩
  · unfold IsUnateBoolFun IsBoolFunIncreasingIn IsBoolFunDecreasingIn
    decide
  · decide

example : boolFunWeight (boolFunConcat (fun _ : Fin 1 → Bool => false) (fun x => x 0)) = 1 := by
  decide

-- With an empty tail, monotonicity is exactly the order of the two constant values.
example (a b : Bool) :
    Monotone (boolFunConcat (fun _ : Fin 0 → Bool => a) (fun _ => b)) ↔ a ≤ b := by
  rw [monotone_boolFunConcat_iff]
  exact ⟨fun h => h.2.2 Fin.elim0, fun hab => ⟨monotone_const, monotone_const, fun _ => hab⟩⟩

-- Concatenating a projection with constant true gives the disjunction of the two inputs.
example : Monotone (boolFunConcat (fun x : Fin 1 → Bool => x 0) (fun _ => true)) :=
  (monotone_boolFunConcat_iff _ _).2 ⟨fun _ _ hxy => hxy 0, monotone_const, fun _ => le_top⟩
