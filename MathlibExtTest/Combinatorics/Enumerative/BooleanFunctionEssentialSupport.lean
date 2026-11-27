/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.BooleanFunctionEssentialSupport

open MetaMathlibExt

-- At arity zero the full count is exactly the count of non-degenerate functions.
example (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g) :
    Nat.card {f : (Fin 0 → Bool) → Bool // P 0 f} =
      Nat.card {f : (Fin 0 → Bool) → Bool // IsNondegenerateBoolFun f ∧ P 0 f} := by
  simpa using card_boolFun_eq_sum_choose_card_nondegenerate P hP 0

private def zeroPreserving (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  f (fun _ => false) = false

private theorem two_mul_card_zeroPreserving (n : ℕ) :
    2 * Nat.card {f : (Fin n → Bool) → Bool // zeroPreserving n f} = 2 ^ (2 ^ n) := by
  classical
  let negate : ((Fin n → Bool) → Bool) ≃ ((Fin n → Bool) → Bool) :=
    { toFun := fun f x => !f x
      invFun := fun f x => !f x
      left_inv := fun f => funext fun x => Bool.not_not (f x)
      right_inv := fun f => funext fun x => Bool.not_not (f x) }
  have heq := Nat.card_congr (negate.subtypeEquiv (p := zeroPreserving n)
    (q := fun f => ¬ zeroPreserving n f) fun f => by
      change f (fun _ => false) = false ↔ ¬ (!f (fun _ => false)) = false
      cases f (fun _ => false) <;> decide)
  have htotal := Nat.card_congr (Equiv.sumCompl (zeroPreserving n))
  rw [Nat.card_sum, ← heq, ← two_mul] at htotal
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool] using htotal

-- Five of the eight zero-preserving binary functions depend on both variables:
-- one has empty support, and each singleton support accounts for one more.
example :
    Nat.card {f : (Fin 2 → Bool) → Bool // IsNondegenerateBoolFun f ∧ zeroPreserving 2 f} = 5 := by
  have h := card_boolFun_eq_sum_choose_card_nondegenerate zeroPreserving (fun _ _ _ _ => Iff.rfl)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have htotal0 := two_mul_card_zeroPreserving 0
  have htotal1 := two_mul_card_zeroPreserving 1
  have htotal2 := two_mul_card_zeroPreserving 2
  norm_num [Finset.sum_range_succ] at h0 h1 h2 htotal0 htotal1 htotal2
  omega
