/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicDescentNumber
public import MathlibExt.GroupTheory.Perm.OrderedDeletion
public import MathlibExt.Logic.Equiv.Fin.Rotate
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic rotation and fixed-head permutation coordinates

For `N=n+1`, the cycle `ρ=finRotate N` acts on `Fin N` by addition of one. Its `r`-th power
adds `r` modulo `N`.

The embedding `H_n : S_n → S_N` fixes zero and acts on the tail by `H_n(π)(j+1)=π(j)+1`. Every
permutation has a unique decomposition `ρ^r H_n(π)`, with `r=σ(0)`. This gives `Fin N × S_n ≃
S_N` and the corresponding decomposition of a finite permutation sum.

The closing-edge coordinate is `r ↦ n+r` modulo `N`.

Reference: Stanley, *Enumerative Combinatorics*, Volume 1, Chapter 1.
-/

@[expose] public section
noncomputable section

open scoped BigOperators
open Fin.NatCast

namespace Equiv.Perm

open Fin.NatCast in
/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : ℕ` and `i : Fin N`, `(ρ^r) i = i + (r : Fin N)`. -/
theorem rotationPower_apply (n r : ℕ) (i : Fin (n + 1)) :
    (finRotate (n + 1) ^ r) i = i + (r : Fin (n + 1)) := by
  induction r with
  | zero => simp
  | succ r hr =>
    simp only [pow_succ', Equiv.Perm.mul_apply, hr, finRotate_apply,
      Nat.cast_succ, add_assoc]

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r,i : Fin N`, `(ρ^r.val) i = i+r`. -/
theorem rotationPower_atFin_apply (n : ℕ) (r i : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) i = i + r := by
  rw [rotationPower_apply]
  congr 1
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `(ρ^r.val)⁻¹ = ρ^(-r).val`, where `-r` is modular negation in `Fin N`. -/
theorem rotationPower_inverse (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val)⁻¹ = finRotate (n + 1) ^ (-r).val := by
  apply Equiv.ext
  intro i
  have h : (finRotate (n + 1) ^ r.val) ((finRotate (n + 1) ^ (-r).val) i) = i := by
    rw [rotationPower_atFin_apply, rotationPower_atFin_apply]
    simp only [add_assoc, neg_add_cancel, add_zero]
  exact ((finRotate (n + 1) ^ r.val).injective
    ((Equiv.apply_symm_apply _ i).trans h.symm))

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `(ρ^r.val) 0 = r`. -/
theorem rotationPower_zero (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) 0 = r := by
  rw [rotationPower_apply, zero_add]
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `(ρ^r.val)(Fin.last n) = Fin.last n + r`. -/
theorem rotationPower_last (n : ℕ) (r : Fin (n + 1)) :
    (finRotate (n + 1) ^ r.val) (Fin.last n) = Fin.last n + r := by
  rw [rotationPower_apply]
  congr 1
  apply Fin.ext
  change r.val % (n + 1) = r.val
  exact Nat.mod_eq_of_lt r.isLt

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. `closingCutEquiv n : Fin N ≃ Fin N` is modular translation `r ↦ Fin.last n + r`, with
inverse translation by `-Fin.last n`. -/
def closingCutEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.addLeft (Fin.last n)

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For `r : Fin N`, `closingCutEquiv n r = (ρ^r.val)(Fin.last n)`. -/
theorem closingCutEquiv_apply (n : ℕ) (r : Fin (n + 1)) :
    closingCutEquiv n r = (finRotate (n + 1) ^ r.val) (Fin.last n) :=
  (rotationPower_last n r).symm

/-- For `n : ℕ` and `π ∈ S_n`, `headFixingPermutation n π ∈ S_(n+1)` fixes zero and sends `j.succ`
to `(π j).succ` for `j : Fin n`. -/
def headFixingPermutation (n : ℕ) (π : Perm (Fin n)) : Perm (Fin (n + 1)) := orderedFirst 0 π

@[simp]
theorem headFixingPermutation_zero (n : ℕ) (π : Perm (Fin n)) : headFixingPermutation n π 0 = 0 :=
  orderedFirst_zero 0 π

@[simp]
theorem headFixingPermutation_succ (n : ℕ) (π : Perm (Fin n)) (i : Fin n) :
    headFixingPermutation n π i.succ = (π i).succ := by
  rw [headFixingPermutation, orderedFirst_succ,
    Fin.succAbove_of_le_castSucc 0 (π i) (Fin.zero_le _)]

/-- For `n : ℕ` and `π ∈ S_n`, `(headFixingPermutation n π).sign = π.sign` in `ℤˣ`. -/
theorem headFixingPermutation_sign (n : ℕ) (π : Perm (Fin n)) :
    (headFixingPermutation n π).sign = π.sign := by
  rw [headFixingPermutation, sign_orderedFirst, Fin.val_zero, pow_zero, one_mul]

/-- For `n : ℕ`, `headFixingHom n : S_n →* S_(n+1)` sends `π` to the permutation fixing zero and
acting by `j+1 ↦ π(j)+1` on the tail. -/
def headFixingHom (n : ℕ) : Perm (Fin n) →* Perm (Fin (n + 1)) where
  toFun := headFixingPermutation n
  map_one' := by
    ext i
    cases i using Fin.cases with
    | zero => rw [headFixingPermutation_zero]; rfl
    | succ i => rw [headFixingPermutation_succ]; rfl
  map_mul' π τ := by
    ext i
    cases i using Fin.cases with
    | zero => simp only [Equiv.Perm.mul_apply, headFixingPermutation_zero]
    | succ i => simp only [Equiv.Perm.mul_apply, headFixingPermutation_succ]

/-- For every `n : ℕ`, `headFixingHom n : S_n → S_(n+1)` is injective: equal fixed-head
permutations have equal tail permutations. -/
theorem headFixingHom_injective (n : ℕ) : Function.Injective (headFixingHom n) := by
  intro π τ h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Perm (Fin (n + 1)) => p i.succ) h
  change headFixingPermutation n π i.succ = headFixingPermutation n τ i.succ at hi
  rw [headFixingPermutation_succ, headFixingPermutation_succ] at hi
  exact (Fin.succ_injective n) hi

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. The function `(r,π) ↦ ρ^r.val * headFixingHom n π` from `Fin N × S_n` to `S_N` is
injective. The first value recovers `r` and the remaining fixed-head action recovers `π`. -/
theorem rotationHead_uncurry_injective (n : ℕ) :
    Function.Injective (fun z : Fin (n + 1) × Perm (Fin n) =>
      finRotate (n + 1) ^ z.1.val * headFixingHom n z.2) := by
  rintro ⟨r, π⟩ ⟨s, τ⟩ h
  have hrs : r = s := by
    have h0 := congrArg (fun p : Perm (Fin (n + 1)) => p 0) h
    change (finRotate (n + 1) ^ r.val) (headFixingPermutation n π 0) =
      (finRotate (n + 1) ^ s.val) (headFixingPermutation n τ 0) at h0
    rw [headFixingPermutation_zero, headFixingPermutation_zero,
      rotationPower_zero, rotationPower_zero] at h0
    exact h0
  subst s
  have hπτ : π = τ := headFixingHom_injective n (mul_left_cancel h)
  subst τ
  rfl

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. `rotationHeadEquiv n : Fin N × S_n ≃ S_N` sends `(r,π)` to `ρ^r.val * headFixingHom n π`.
The inverse records the first value and the tail permutation after rotating that value to
zero. -/
def rotationHeadEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective (fun z => finRotate (n + 1) ^ z.1.val * headFixingHom n z.2) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨rotationHead_uncurry_injective n, ?_⟩
    simp only [Nat.card_eq_fintype_card]
    calc
      Fintype.card (Fin (n + 1) × Perm (Fin n)) = (n + 1) * Nat.factorial n := by
        rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
      _ = Fintype.card (Perm (Fin (n + 1))) := by
        rw [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ])

/-- Let `n : ℕ`, `N=n+1`, and `ρ=finRotate N`. Addition and negation on `Fin N` are taken modulo
`N`. For a commutative additive monoid `T` and `f : S_N → T`, `∑ σ ∈ S_N, f σ = ∑ r : Fin N, ∑
π ∈ S_n, f(ρ^r.val * headFixingHom n π)`. -/
theorem sum_rotationHead {T : Type*} [AddCommMonoid T] (n : ℕ)
    (f : Perm (Fin (n + 1)) → T) :
    ∑ σ : Perm (Fin (n + 1)), f σ =
      ∑ r : Fin (n + 1), ∑ π : Perm (Fin n), f (finRotate (n + 1) ^ r.val * headFixingHom n π) := by
  rw [← (rotationHeadEquiv n).sum_comp f, Fintype.sum_prod_type]
  rfl

end Equiv.Perm
