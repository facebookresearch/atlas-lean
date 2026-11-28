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
# Permutations decomposed by an endpoint value

For `i : Fin(n+1)` and `π ∈ S_n`, first insertion is the permutation with `0 ↦ i` and `j+1 ↦
i.succAbove(π j)`. Last insertion has `n ↦ i` and `j.castSucc ↦ i.succAbove(π j)`. Both give
bijections `Fin(n+1) × S_n ≃ S_(n+1)`.

Their signs are `(-1)^i * sign π` and `(-1)^n * ((-1)^i * sign π)`. Summing over permutations
can therefore be grouped by either endpoint value. The case `n=0` gives the identity
permutation of `Fin 1`.

These endpoint signs occur in Hochschild antisymmetrization; see Loday, *Cyclic Homology*,
Section 1.1.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedFirst i π` is the permutation of `Fin(n+1)`
determined by `orderedFirst i π 0 = i` and `orderedFirst i π j.succ = ν_i(π j)` for `j : Fin
n`. -/
def orderedFirst {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) : Perm (Fin (n + 1)) := by
  cases n with
  | zero => exact 1
  | succ n => exact decomposeFin'Symm i π

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. The first-position value is `orderedFirst i π 0 = i`. -/
@[simp]
theorem orderedFirst_zero {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedFirst i π 0 = i := by
  cases n with
  | zero => exact (Fin.eq_zero (orderedFirst i π 0)).trans (Fin.eq_zero i).symm
  | succ n => exact decomposeFin'Symm_zero i π

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. For `j : Fin n`, `orderedFirst i π j.succ = ν_i(π
j)`. -/
@[simp]
theorem orderedFirst_succ {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) (j : Fin n) :
    orderedFirst i π j.succ = i.succAbove (π j) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => exact decomposeFin'Symm_succ i π j

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. In `ℤˣ`, `(orderedFirst i π).sign = (-1)^i.val *
π.sign`. -/
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

/-- For every `n : ℕ`, the function `(i,π) ↦ orderedFirst i π` from `Fin(n+1) × Equiv.Perm (Fin
n)` to `Equiv.Perm (Fin(n+1))` is injective. Equality of the inserted permutations forces
equality of both the distinguished first value and the remaining permutation. -/
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

/-- For every `n : ℕ`, `orderedFirstEquiv n` is the bijection `Fin(n+1) × S_n ≃ S_(n+1)` sending
`(i,π)` to `orderedFirst i π`. Its inverse records the first value and the permutation
obtained by deleting that value and reindexing the remaining values in ascending order. -/
def orderedFirstEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective (Function.uncurry (orderedFirst (n := n))) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨orderedFirst_uncurry_injective n, ?_⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
      Fintype.card_fin, Nat.factorial_succ])

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedFirstEquiv n (i,π) = orderedFirst i π`. -/
theorem orderedFirstEquiv_apply (n : ℕ) (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedFirstEquiv n (i, π) = orderedFirst i π := rfl

/-- Let `T` be a commutative additive monoid, `n : ℕ`, and `f : S_(n+1) → T`. The complete
permutation sum is `∑ σ ∈ S_(n+1), f σ = ∑ i : Fin(n+1), ∑ π ∈ S_n, f(orderedFirst i π)`. -/
theorem sum_orderedFirst {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ π : Perm (Fin (n + 1)), f π =
      ∑ i : Fin (n + 1), ∑ π : Perm (Fin n), f (orderedFirst i π) := by
  rw [← (orderedFirstEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedLast i π = orderedFirst i π *
finRotate(n+1)`. It sends the last position to `i` and each `j.castSucc` to `ν_i(π j)`, with
permutation multiplication `(p*q)(j) = p(q(j))`. -/
def orderedLast {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  orderedFirst i π * finRotate (n + 1)

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. The last-position value is `orderedLast i π (Fin.last
n) = i`. -/
@[simp]
theorem orderedLast_last {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedLast i π (Fin.last n) = i := by
  rw [orderedLast, mul_apply, finRotate_last, orderedFirst_zero]

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. For `j : Fin n`, `orderedLast i π j.castSucc = ν_i(π
j)`. -/
@[simp]
theorem orderedLast_castSucc {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) (j : Fin n) :
    orderedLast i π j.castSucc = i.succAbove (π j) := by
  rw [orderedLast, mul_apply]
  have hr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  rw [hr, orderedFirst_succ]

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. In `ℤˣ`, `(orderedLast i π).sign = (-1)^n *
((-1)^i.val * π.sign)`. -/
theorem sign_orderedLast {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    (orderedLast i π).sign = (-1 : ℤˣ) ^ n * ((-1 : ℤˣ) ^ i.val * π.sign) := by
  rw [orderedLast, sign_mul, sign_orderedFirst, sign_finRotate]
  simp only [Nat.add_sub_cancel]
  ac_rfl

/-- For every `n : ℕ`, `orderedLastEquiv n : Fin(n+1) × S_n ≃ S_(n+1)` sends `(i,π)` to
`orderedLast i π`. Its inverse records the last value and the permutation of the remaining
values after ascending reindexing. -/
def orderedLastEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  (orderedFirstEquiv n).trans (Equiv.mulRight (finRotate (n + 1)))

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. `orderedLastEquiv n (i,π) = orderedLast i π`. -/
theorem orderedLastEquiv_apply (n : ℕ) (i : Fin (n + 1)) (π : Perm (Fin n)) :
    orderedLastEquiv n (i, π) = orderedLast i π := rfl

/-- Let `T` be a commutative additive monoid, `n : ℕ`, and `f : S_(n+1) → T`. Then `∑ σ ∈ S_(n+1),
f σ = ∑ i : Fin(n+1), ∑ π ∈ S_n, f(orderedLast i π)`. -/
theorem sum_orderedLast {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ π : Perm (Fin (n + 1)), f π =
      ∑ i : Fin (n + 1), ∑ π : Perm (Fin n), f (orderedLast i π) := by
  rw [← (orderedLastEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. After coercing signs to `ℤ`, `((orderedFirst i
π).sign : ℤ) = (-1 : ℤ)^i.val * (π.sign : ℤ)`. -/
theorem sign_orderedFirst_int {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    ((orderedFirst i π).sign : ℤ) = (-1 : ℤ) ^ i.val * (π.sign : ℤ) := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (sign_orderedFirst i π)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

/-- Let `n : ℕ`, `i : Fin(n+1)`, and `π : Equiv.Perm (Fin n)`. Write `ν_i(j) = i.succAbove j` for
the increasing embedding that omits `i`. After coercing signs to `ℤ`, `((orderedLast i π).sign
: ℤ) = (-1 : ℤ)^n * ((-1 : ℤ)^i.val * (π.sign : ℤ))`. -/
theorem sign_orderedLast_int {n : ℕ} (i : Fin (n + 1)) (π : Perm (Fin n)) :
    ((orderedLast i π).sign : ℤ) = (-1 : ℤ) ^ n * ((-1 : ℤ) ^ i.val * (π.sign : ℤ)) := by
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (sign_orderedLast i π)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using h

end Equiv.Perm
