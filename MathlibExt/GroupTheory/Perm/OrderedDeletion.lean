/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Ordered permutation coordinates for the original endpoint signs. -/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Permutations grouped by their first or last value

The ordered deletion permutation sends the remaining positions through
`Fin.succAbove`, preserving the original order of the omitted coordinate.
The constructions include the degree-one case and have the actual signs
`(-1)^i` and `(-1)^(n+i)`. They support the two endpoint terms of the
antisymmetric bar differential, without changing the source coordinates.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Insert the distinguished value in the first position and permute the
remaining ordered positions. The native positive-degree construction is reused. -/
def orderedFirst {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) : Perm (Fin (n + 1)) := by
  cases n with
  | zero => exact 1
  | succ n => exact decomposeFin'Symm i π

/-- The first position has exactly the distinguished original value. -/
@[simp]
theorem orderedFirst_zero {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedFirst i π 0 = i := by
  cases n with
  | zero => exact (Fin.eq_zero (orderedFirst i π 0)).trans (Fin.eq_zero i).symm
  | succ n => exact decomposeFin'Symm_zero i π

/-- Every remaining position is the original ordered deletion embedding. -/
@[simp]
theorem orderedFirst_succ {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) (j : Fin n) :
    orderedFirst i π j.succ = i.succAbove (π j) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => exact decomposeFin'Symm_succ i π j

/-- The actual sign of first insertion is the signed deletion coefficient. -/
theorem sign_orderedFirst {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    (orderedFirst i π).sign = (-1 : ℤˣ) ^ i.val * π.sign := by
  cases n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    have hπ : π = 1 := by
      apply Equiv.ext
      intro j
      exact Fin.elim0 j
    have hσ : orderedFirst i π = 1 := by
      apply Equiv.ext
      intro j
      exact (Fin.eq_zero (orderedFirst i π j)).trans (Fin.eq_zero _).symm
    rw [hσ, sign_one, hi, hπ, sign_one]
    simp only [Fin.val_zero, pow_zero, one_mul]
  | succ n => exact sign_decomposeFin'Symm i π

/-- The distinguished coordinate and its remaining permutation determine the full permutation. -/
theorem orderedFirst_uncurry_injective (n : ℕ) :
    Function.Injective (Function.uncurry (orderedFirst (n := n))) := by
  rintro ⟨i, π⟩ ⟨j, τ⟩ h
  have hij : i = j := by
    simpa only [Function.uncurry_apply_pair, orderedFirst_zero] using
      congrArg (fun p : Perm (Fin (n + 1)) => p 0) h
  subst j
  have hπτ : π = τ := by
    apply Equiv.ext
    intro a
    exact Fin.succAbove_right_injective
      (by simpa only [Function.uncurry_apply_pair, orderedFirst_succ] using
        congrArg (fun p : Perm (Fin (n + 1)) => p a.succ) h)
  subst τ
  rfl

/-- The first-value decomposition is a bijection in every degree. -/
def orderedFirstEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective (Function.uncurry (orderedFirst (n := n))) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨orderedFirst_uncurry_injective n, ?_⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
      Fintype.card_fin, Nat.factorial_succ])

/-- The inverse decomposition keeps the actual native insertion function. -/
theorem orderedFirstEquiv_apply (n : ℕ) (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedFirstEquiv n (i, π) = orderedFirst i π := rfl

/-- Group a complete permutation sum by its first original value. -/
theorem sum_orderedFirst {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ π : Perm (Fin (n + 1)), f π =
      ∑ i : Fin (n + 1), ∑ π : Perm (Fin n), f (orderedFirst i π) := by
  rw [← (orderedFirstEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Insert the distinguished original value in the final position. -/
def orderedLast {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  orderedFirst i π * finRotate (n + 1)

/-- The final position has the distinguished original value. -/
@[simp]
theorem orderedLast_last {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedLast i π (Fin.last n) = i := by
  rw [orderedLast, mul_apply, finRotate_last, orderedFirst_zero]

/-- The unchanged initial positions are the original ordered deletion embedding. -/
@[simp]
theorem orderedLast_castSucc {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) (j : Fin n) :
    orderedLast i π j.castSucc = i.succAbove (π j) := by
  rw [orderedLast, mul_apply]
  have hr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  rw [hr, orderedFirst_succ]

/-- The final-value decomposition has the original signed rotation factor. -/
theorem sign_orderedLast {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    (orderedLast i π).sign = (-1 : ℤˣ) ^ n * ((-1 : ℤˣ) ^ i.val * π.sign) := by
  rw [orderedLast, sign_mul, sign_orderedFirst, sign_finRotate]
  simp only [Nat.add_sub_cancel]
  ac_rfl

/-- The final-value decomposition is the first-value decomposition followed by the
actual native rotation. -/
def orderedLastEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  (orderedFirstEquiv n).trans (Equiv.mulRight (finRotate (n + 1)))

/-- The equivalence uses exactly the actual ordered last insertion. -/
theorem orderedLastEquiv_apply (n : ℕ) (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedLastEquiv n (i, π) = orderedLast i π := rfl

/-- Group a complete permutation sum by its final original value. -/
theorem sum_orderedLast {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ π : Perm (Fin (n + 1)), f π =
      ∑ i : Fin (n + 1), ∑ π : Perm (Fin n), f (orderedLast i π) := by
  rw [← (orderedLastEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Integer signs retain the exact first-deletion coefficient. -/
theorem sign_orderedFirst_int {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    ((orderedFirst i π).sign : ℤ) = (-1 : ℤ) ^ i.val * (π.sign : ℤ) := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (sign_orderedFirst i π)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

/-- Integer signs retain both the last-rotation and deletion coefficients. -/
theorem sign_orderedLast_int {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    ((orderedLast i π).sign : ℤ) = (-1 : ℤ) ^ n * ((-1 : ℤ) ^ i.val * (π.sign : ℤ)) := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (sign_orderedLast i π)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

end Equiv.Perm
