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

-- With no tail coordinates, either order of the two values gives a unate concatenation.
example (a b : Bool) :
    IsUnateBoolFun (boolFunConcat (fun _ : Fin 0 → Bool => a) (fun _ => b)) := by
  apply (isUnateBoolFun_boolFunConcat_iff _ _).2
  refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  exact (le_total a b).imp (fun hab _ => hab) (fun hba _ => hba)

-- The projections increase in every coordinate but are incomparable as functions.
example : ¬ IsUnateBoolFun (boolFunConcat (fun x : Fin 2 → Bool => x 0) (fun x => x 1)) := by
  intro hu
  have horder := ((isUnateBoolFun_boolFunConcat_iff _ _).1 hu).2.2.2
  revert horder
  decide

-- AND lies below implication, but they have opposite directions in the first tail coordinate.
example : ¬ IsUnateBoolFun
    (boolFunConcat (fun x : Fin 2 → Bool => x 0 && x 1) (fun x => !x 0 || x 1)) := by
  intro hu
  have hdir := ((isUnateBoolFun_boolFunConcat_iff _ _).1 hu).2.2.1 0
  revert hdir
  unfold IsBoolFunIncreasingIn IsBoolFunDecreasingIn
  decide

-- A projection is its only monotone NN-equivalent function, even with unused coordinates.
example {n : ℕ} (i : Fin n) {g : (Fin n → Bool) → Bool} (hg : Monotone g)
    (h : IsBoolFunNNEquiv (fun x => x i) g) : g = fun x => x i := by
  rcases (isBoolFunNNEquiv_monotone_iff (fun _ _ hxy => hxy i) hg).1 h with heq | ⟨a, ha, heq⟩
  · exact heq
  · funext x
    simpa [(ha i).2 (isBoolFunNondegenerateOn_proj i)] using heq x

-- AND and OR on the first two of three inputs are distinct monotone NN-equivalent functions.
example : IsBoolFunNNEquiv (fun x : Fin 3 → Bool => x 0 && x 1) (fun x => x 0 || x 1) := by
  apply (isBoolFunNNEquiv_monotone_iff (by decide) (by decide)).2
  right
  refine ⟨fun i => decide (i ≠ 2), ?_, ?_⟩
  · unfold IsBoolFunNondegenerateOn
    decide
  · decide

-- Renaming variables keeps the all-false input, so the functions vanishing there qualify.
example (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv
        (fun f : (Fin (n + 1) → Bool) → Bool =>
          IsNondegenerateBoolFun f ∧ f (fun _ => false) = false)
      = boolFunClassCount IsBoolFunVarPermEquiv
          (fun f : (Fin (n + 1) → Bool) → Bool => f (fun _ => false) = false)
        - boolFunClassCount IsBoolFunVarPermEquiv
          (fun f : (Fin n → Bool) → Bool => f (fun _ => false) = false) :=
  boolFunClassCount_varPerm_nondegenerate_eq_sub (fun _ f => f (fun _ => false) = false)
    (fun _ _ _ _ => Iff.rfl) n

-- Over all functions, the non-degenerate classes are the classes not coming from one variable
-- fewer.
example (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (IsNondegenerateBoolFun (n := n + 1))
      = boolFunClassCount IsBoolFunVarPermEquiv (fun _ : (Fin (n + 1) → Bool) → Bool => True)
        - boolFunClassCount IsBoolFunVarPermEquiv (fun _ : (Fin n → Bool) → Bool => True) := by
  simpa using
    boolFunClassCount_varPerm_nondegenerate_eq_sub (fun _ _ => True) (fun _ _ _ _ => Iff.rfl) n
