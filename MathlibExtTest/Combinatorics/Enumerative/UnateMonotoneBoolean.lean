/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Set.Card
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

namespace MetaMathlibExt.boolFunClassCount_varPerm_unate_le

-- At arity zero or one, every permutation class is a singleton.
private theorem classCount_subsingleton {n : ℕ} [Subsingleton (Fin n)]
    (P : ((Fin n → Bool) → Bool) → Prop) :
    boolFunClassCount IsBoolFunVarPermEquiv P = Nat.card {f // P f} := by
  have hsingle (f) (hf : P f) : {g | P g ∧ IsBoolFunVarPermEquiv f g} = {f} := by
    ext g
    constructor
    · rintro ⟨_, σ, hσ⟩
      simpa [Subsingleton.elim σ 1] using funext hσ
    · rintro (rfl : g = f)
      exact ⟨hf, isBoolFunVarPermEquiv_refl _⟩
  have hclasses : {S | ∃ f, P f ∧ S = {g | P g ∧ IsBoolFunVarPermEquiv f g}} =
      singleton '' {f | P f} := by
    ext S
    exact exists_congr fun f => and_congr_right fun hf => by rw [hsingle f hf, eq_comm]
  exact (congrArg Set.ncard hclasses).trans (Set.ncard_image_of_injective _ Set.singleton_injective)

-- At arity zero, both constant functions contribute to the sum.
example : boolFunClassCount (n := 0) IsBoolFunVarPermEquiv (fun _ => True) = 2 := by
  rw [boolFunClassCount_varPerm_eq_sum_nondegenerate (fun _ _ => True)
    (fun _ _ _ _ => Iff.rfl) 0, Finset.sum_range_one, classCount_subsingleton]
  unfold IsNondegenerateBoolFun IsBoolFunNondegenerateOn
  rw [Nat.card_eq_fintype_card]
  decide

-- On one variable the sum has separate zero- and one-variable contributions, even when
-- restricting to functions that vanish at the all-false input.
example :
    boolFunClassCount (n := 1) IsBoolFunVarPermEquiv (fun f => f (fun _ => false) = false) =
      boolFunClassCount (n := 0) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ f (fun _ => false) = false) +
      boolFunClassCount (n := 1) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ f (fun _ => false) = false) := by
  rw [boolFunClassCount_varPerm_eq_sum_nondegenerate (fun _ f => f (fun _ => false) = false)
    (fun _ _ _ _ => Iff.rfl) 1, Finset.sum_range_succ, Finset.sum_range_one]

-- At arity zero, both constants contribute non-degenerate classes and the factor is one.
example : boolFunClassCount (n := 0) IsBoolFunVarPermEquiv
    (fun f => IsNondegenerateBoolFun f ∧ IsUnateBoolFun f) = 2 := by
  rw [classCount_subsingleton]
  unfold IsNondegenerateBoolFun IsBoolFunNondegenerateOn IsUnateBoolFun
    IsBoolFunIncreasingIn IsBoolFunDecreasingIn
  rw [Nat.card_eq_fintype_card]
  decide

-- On one variable the bound for balanced functions is sharp:
-- the identity is monotone, and both the identity and its negation are unate.
example : boolFunClassCount (n := 1) IsBoolFunVarPermEquiv
    (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2) = 2 := by
  apply Nat.le_antisymm
  · have h := (boolFunClassCount_varPerm_unate_le 1).2.2.2
    refine h.trans ?_
    rw [classCount_subsingleton]
    rw [Nat.card_eq_fintype_card]
    decide
  · rw [classCount_subsingleton]
    let literal (b : Bool) : {f : (Fin 1 → Bool) → Bool //
        IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2} :=
      ⟨fun x => xor (x 0) b, by
        unfold IsUnateBoolFun IsBoolFunIncreasingIn IsBoolFunDecreasingIn
        cases b <;> decide⟩
    calc
      2 = Nat.card Bool := by simp [Nat.card_eq_fintype_card]
      _ ≤ _ := Nat.card_le_card_of_injective literal fun b c h => by
        simpa [literal] using congrArg (fun f => f.val (fun _ => false)) h

-- Flipping either one of the two inputs of AND gives distinct functions in the same class.
example :
    let f := fun x : Fin 2 → Bool => (!x 0) && x 1
    let g := fun x : Fin 2 → Bool => x 0 && (!x 1)
    f ≠ g ∧ IsBoolFunVarPermEquiv f g := by
  dsimp only
  constructor
  · decide
  · exact ⟨Equiv.swap 0 1, by decide⟩

end MetaMathlibExt.boolFunClassCount_varPerm_unate_le

-- With no variables, both constant functions are non-degenerate.
example :
    Nat.card {f : (Fin 0 → Bool) → Bool // IsNondegenerateBoolFun f ∧ IsUnateBoolFun f} = 2 := by
  rw [(card_unate_boolFun_relations 0).1, pow_zero, one_mul]
  unfold IsNondegenerateBoolFun IsBoolFunNondegenerateOn
  rw [Nat.card_eq_fintype_card]
  decide

-- On one variable, the identity is the only balanced monotone function.
example : Nat.card {f : (Fin 1 → Bool) → Bool //
    IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ 1} ≤ 2 := by
  refine (card_unate_boolFun_relations 1).2.2.2.trans ?_
  rw [Nat.card_eq_fintype_card]
  decide
