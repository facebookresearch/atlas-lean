/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.GroupTheory.Perm.Fin
public import MathlibExt.Logic.Equiv.Fin.Rotate

/-!
# First-coordinate decomposition by finite cyclic rotation

For n : ℕ, extend a permutation σ of Fin n to fix 0 in Fin(n+1), and let shift_j add j modulo
n+1 to every input position. Every permutation τ of Fin(n+1) has the unique expression τ =
fixFirst(σ) · shift_j⁻¹, where j = τ⁻¹(0). Its remaining component is the tail permutation of τ
· shift_j, which fixes 0.

The sign of shift_j is (-1)^{n·j}, and the sign of the decomposition is sign(σ)·(-1)^{n·j}. The
formulas also include n=0, when Fin(n+1)=Fin1 and the tail permutation is empty.
-/

@[expose] public section

noncomputable section

open Equiv
open Fin.NatCast

namespace Equiv.Perm

/-- For n : ℕ and σ a permutation of Fin n, fixFirst n σ is the permutation of Fin(n+1) satisfying 0
↦ 0 and j+1 ↦ σ(j)+1 for every j ∈ Fin n. -/
def fixFirst (n : ℕ) (σ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  decomposeFin.symm (0, σ)

@[simp]
theorem fixFirst_zero (n : ℕ) (σ : Perm (Fin n)) : fixFirst n σ 0 = 0 :=
  decomposeFin_symm_apply_zero _ _

@[simp]
theorem fixFirst_succ (n : ℕ) (σ : Perm (Fin n)) (j : Fin n) :
    fixFirst n σ j.succ = (σ j).succ := by
  simp only [fixFirst, decomposeFin_symm_apply_succ, swap_self, refl_apply]

/-- For n : ℕ and any permutation τ of Fin(n+1), tailOfFixFirst n τ is the second component of
decomposeFin τ. When τ(0)=0, it is the tail permutation characterized by
τ(j+1)=tailOfFixFirst(τ)(j)+1. -/
def tailOfFixFirst (n : ℕ) (τ : Perm (Fin (n + 1))) : Perm (Fin n) :=
  (decomposeFin τ).2

theorem fixFirst_tailOfFixFirst (n : ℕ) (τ : Perm (Fin (n + 1))) (hτ : τ 0 = 0) :
    fixFirst n (tailOfFixFirst n τ) = τ := by
  have h : (decomposeFin τ).1 = 0 := by
    have hi := congrArg (fun σ : Perm (Fin (n + 1)) => σ 0)
      (decomposeFin.symm_apply_apply τ)
    rw [decomposeFin_symm_apply_zero] at hi
    exact hi.trans hτ
  have hp : decomposeFin τ = (0, tailOfFixFirst n τ) :=
    Prod.ext h rfl
  change decomposeFin.symm (0, tailOfFixFirst n τ) = τ
  exact (congrArg decomposeFin.symm hp).symm.trans (decomposeFin.symm_apply_apply τ)

/-- For n,j : ℕ and i ∈ Fin(n+1), (finRotate(n+1))ʲ(i) = i+j modulo n+1, where j is cast to its
residue in Fin(n+1). -/
theorem finRotate_pow_apply (n j : ℕ) (i : Fin (n + 1)) :
    (finRotate (n + 1) ^ j) i = i + (j : Fin (n + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply,
        Nat.cast_succ, add_assoc]

/-- For n : ℕ and j ∈ Fin(n+1), shiftFirst n j is the j-th power of the cyclic rotation of Fin(n+1).
It sends i to i+j modulo n+1. -/
def shiftFirst (n : ℕ) (j : Fin (n + 1)) : Perm (Fin (n + 1)) :=
  finRotate (n + 1) ^ j.val

@[simp]
theorem shiftFirst_zero (n : ℕ) (j : Fin (n + 1)) : shiftFirst n j 0 = j := by
  rw [shiftFirst, finRotate_pow_apply]
  simp

/-- For n : ℕ and j ∈ Fin(n+1), the permutation shiftFirst n j has sign (-1)^{n·j.val} in ℤˣ. This
includes n=0 and the one-element ordinal Fin1. -/
theorem shiftFirst_sign (n : ℕ) (j : Fin (n + 1)) :
    (shiftFirst n j).sign = (-1 : ℤˣ) ^ (n * j.val) := by
  rw [shiftFirst, map_pow, sign_finRotate, Nat.add_sub_cancel, ← pow_mul]

/-- For n : ℕ, cyclicFirstEquiv is a bijection Fin(n+1) × Perm(Fin n) ≃ Perm(Fin(n+1)). It sends
(j,σ) to fixFirst(σ)·shift_j⁻¹. Its inverse sends τ to j=τ⁻¹(0) and the tail permutation of
τ·shift_j, which fixes 0. -/
def cyclicFirstEquiv (n : ℕ) : Fin (n + 1) × Perm (Fin n) ≃ Perm (Fin (n + 1)) where
  toFun p := fixFirst n p.2 * (shiftFirst n p.1)⁻¹
  invFun τ :=
    let j := τ.symm 0
    let s := τ * shiftFirst n j
    (j, tailOfFixFirst n s)
  left_inv p := by
    rcases p with ⟨j, σ⟩
    have hpos : (fixFirst n σ * (shiftFirst n j)⁻¹).symm 0 = j := by
      apply (fixFirst n σ * (shiftFirst n j)⁻¹).injective
      rw [Equiv.apply_symm_apply]
      change 0 = fixFirst n σ ((shiftFirst n j).symm j)
      have hj : (shiftFirst n j).symm j = 0 :=
        (shiftFirst n j).symm_apply_eq.mpr (shiftFirst_zero n j).symm
      rw [hj, fixFirst_zero]
    apply Prod.ext
    · exact hpos
    · change tailOfFixFirst n
        ((fixFirst n σ * (shiftFirst n j)⁻¹) *
          shiftFirst n ((fixFirst n σ * (shiftFirst n j)⁻¹).symm 0)) = σ
      rw [hpos, mul_assoc, inv_mul_cancel, mul_one]
      exact congrArg Prod.snd (decomposeFin.apply_symm_apply (0, σ))
  right_inv τ := by
    change fixFirst n (tailOfFixFirst n (τ * shiftFirst n (τ.symm 0))) *
      (shiftFirst n (τ.symm 0))⁻¹ = τ
    rw [fixFirst_tailOfFixFirst n _ (by simp [Equiv.Perm.mul_apply]),
      mul_assoc, mul_inv_cancel, mul_one]

/-- For n : ℕ, j ∈ Fin(n+1) and σ ∈ Perm(Fin n), the sign of cyclicFirstEquiv n (j,σ) equals
sign(σ)·(-1)^{n·j.val} in ℤˣ. -/
theorem cyclicFirstEquiv_sign (n : ℕ) (j : Fin (n + 1)) (σ : Perm (Fin n)) :
    (cyclicFirstEquiv n (j, σ)).sign = σ.sign * (-1 : ℤˣ) ^ (n * j.val) := by
  change (fixFirst n σ * (shiftFirst n j)⁻¹).sign = _
  rw [map_mul, map_inv, shiftFirst_sign]
  have hs : (fixFirst n σ).sign = σ.sign := by
    simp [fixFirst, decomposeFin.symm_sign]
  rw [hs]
  have hunit : ((-1 : ℤˣ) ^ (n * j.val))⁻¹ = (-1 : ℤˣ) ^ (n * j.val) := by
    exact (inv_pow (-1 : ℤˣ) (n * j.val)).symm.trans
      (congrArg (fun x : ℤˣ => x ^ (n * j.val)) (by rfl))
  exact congrArg (fun x : ℤˣ => σ.sign * x) hunit

end Equiv.Perm

end
