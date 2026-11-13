/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusKacWard
import Code.Onsager.KWSpinFourier





open scoped BigOperators Matrix

namespace StatMech.FrontierA

open StatMech.Onsager

abbrev triangularTorusDart (L : Nat) :=
  (ZMod L × ZMod L) × Fin 6


def triangularTorusDirectionStep (L : Nat) : Fin 6 → ZMod L × ZMod L :=
  ![(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)]

def triangularTorusDirectionWeight
    (t1 t2 t3 : Complex) : Fin 6 -> Complex :=
  ![t1, t1, t2, t2, t3, t3]

noncomputable def triangularTorusDirectionPhase
    (u v : Complex) : Fin 6 -> Complex :=
  ![u, u⁻¹, v, v⁻¹, u * v, (u * v) ⁻¹]



noncomputable def triangularTorusKWBlock
    (L : Nat) (t1 t2 t3 rho u v : Complex)
    (g : ZMod L × ZMod L) : Matrix (Fin 6) (Fin 6) Complex :=
  fun a b =>
    if g = triangularTorusDirectionStep L a then
      triangularTorusDirectionPhase u v a *
        triangularTorusDirectionWeight t1 t2 t3 a *
          triangularKacWardTurnMatrix rho a b
    else 0


noncomputable def triangularTorusKWMatrix
    (L : Nat) (t1 t2 t3 rho u v : Complex) :
    Matrix (triangularTorusDart L) (triangularTorusDart L) Complex :=
  ons_blockCirculant2D L 6
    (triangularTorusKWBlock L t1 t2 t3 rho u v)

theorem one_sub_triangularTorusKWMatrix_eq_blockCirculant
    (L : Nat) (t1 t2 t3 rho u v : Complex) :
    1 - triangularTorusKWMatrix L t1 t2 t3 rho u v =
      ons_blockCirculant2D L 6 (fun g =>
        (if g = 0 then (1 : Matrix (Fin 6) (Fin 6) Complex) else 0) -
          triangularTorusKWBlock L t1 t2 t3 rho u v g) := by
  ext p q
  unfold triangularTorusKWMatrix ons_blockCirculant2D
  simp only [Matrix.sub_apply]
  congr 1
  rw [Matrix.one_apply]
  by_cases hpq : p = q
  · subst p
    simp [Matrix.one_apply]
  · rw [if_neg hpq]
    by_cases hg : (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0
    · rw [if_pos hg, Matrix.one_apply]
      have hdir : p.2 ≠ q.2 := by
        intro hdir
        apply hpq
        apply Prod.ext
        · apply Prod.ext <;> dsimp only at hg ⊢
          · exact sub_eq_zero.mp (congrArg Prod.fst hg)
          · exact sub_eq_zero.mp (congrArg Prod.snd hg)
        · exact hdir
      rw [if_neg hdir]
    · rw [if_neg hg]
      simp

theorem triangularTorusKWBlock_symbol
    (L : Nat) [NeZero L]
    (t1 t2 t3 rho u v root : Complex)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 6 root (fun g =>
      (if g = 0 then (1 : Matrix (Fin 6) (Fin 6) Complex) else 0) -
        triangularTorusKWBlock L t1 t2 t3 rho u v g) j =
      triangularKacWardSymbolMatrix t1 t2 t3 rho
        (u * root ^ j.1.val) (v * root ^ j.2.val)
        ((u * root ^ j.1.val) * (v * root ^ j.2.val)) := by
  have hrootne : root ≠ 0 := hroot.ne_zero (NeZero.ne L)
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    rw [ZMod.val_neg_one]
  have hbase : root ^ ((-1 : ZMod L).val) = root ⁻¹ := by
    have hmul : root ^ ((-1 : ZMod L).val) * root = 1 := by
      rw [← pow_succ, hval, hroot.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left hmul).symm
  have hinv (m : Nat) :
      root ^ ((-1 : ZMod L).val * m) = (root ^ m) ⁻¹ := by
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hid : (∑ g : ZMod L × ZMod L,
      root ^ (g.1.val * j.1.val + g.2.val * j.2.val) *
        (if g = 0 then (1 : Matrix (Fin 6) (Fin 6) Complex) else 0) a b) =
      (if a = b then 1 else 0 : Complex) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp [Matrix.one_apply]
    · intro g _ hg
      rw [if_neg hg]
      simp
    · exact fun h => absurd (Finset.mem_univ _) h
  have hkw : (∑ g : ZMod L × ZMod L,
      root ^ (g.1.val * j.1.val + g.2.val * j.2.val) *
        triangularTorusKWBlock L t1 t2 t3 rho u v g a b) =
      root ^ ((triangularTorusDirectionStep L a).1.val * j.1.val +
        (triangularTorusDirectionStep L a).2.val * j.2.val) *
        (triangularTorusDirectionPhase u v a *
          triangularTorusDirectionWeight t1 t2 t3 a *
            triangularKacWardTurnMatrix rho a b) := by
    have hentry (g : ZMod L × ZMod L) :
        triangularTorusKWBlock L t1 t2 t3 rho u v g a b =
          if g = triangularTorusDirectionStep L a then
            triangularTorusDirectionPhase u v a *
              triangularTorusDirectionWeight t1 t2 t3 a *
                triangularKacWardTurnMatrix rho a b
          else 0 := by
      unfold triangularTorusKWBlock
      rfl
    simp only [hentry]
    rw [Finset.sum_eq_single (triangularTorusDirectionStep L a)]
    · rw [if_pos rfl]
    · intro g _ hg
      rw [if_neg hg, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  unfold triangularKacWardSymbolMatrix triangularKacWardWeightDiagonal
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.mul_sum, ite_mul, zero_mul]
  rw [Fintype.sum_ite_eq]
  have huv : u * v ≠ 0 := mul_ne_zero hu hv
  have hone : Nat.ModEq L (1 : ZMod L).val 1 := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [ZMod.natCast_zmod_val]
    norm_num
  have hpowOne (m : Nat) :
      root ^ (m * (1 : ZMod L).val) = root ^ m :=
    pow_eq_pow_of_modEq (by simpa using hone.mul_left m) hroot.pow_eq_one
  fin_cases a <;>
    simp only [triangularTorusDirectionStep, triangularTorusDirectionPhase,
      triangularTorusDirectionWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.empty_val',
      ZMod.val_one, ZMod.val_zero, Nat.zero_mul, Nat.mul_zero,
      add_zero, zero_add, pow_zero, one_mul] <;>
    simp_all [hpowOne, hinv, pow_add, mul_assoc, mul_left_comm, mul_comm,
      mul_inv_rev, hrootne, huv]



theorem triangularTorusKWMatrix_det
    (L : Nat) [NeZero L]
    (t1 t2 t3 rho u v root : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + t1 ^ 2) * (1 + t2 ^ 2) * (1 + t3 ^ 2) +
          8 * t1 * t2 * t3 -
          t1 * (1 - t2 ^ 2) * (1 - t3 ^ 2) *
            (u * root ^ j.1.val + (u * root ^ j.1.val) ⁻¹) -
          t2 * (1 - t1 ^ 2) * (1 - t3 ^ 2) *
            (v * root ^ j.2.val + (v * root ^ j.2.val) ⁻¹) -
          t3 * (1 - t1 ^ 2) * (1 - t2 ^ 2) *
            ((u * root ^ j.1.val) * (v * root ^ j.2.val) +
              ((u * root ^ j.1.val) * (v * root ^ j.2.val)) ⁻¹)) := by
  rw [one_sub_triangularTorusKWMatrix_eq_blockCirculant,
    ons_det_blockCirculant2D L 6 root hroot]
  apply Finset.prod_congr rfl
  intro j _
  rw [triangularTorusKWBlock_symbol L t1 t2 t3 rho u v root hroot hu hv j]
  exact triangularKacWardSymbolMatrix_det t1 t2 t3 rho _ _ _ hrho
    (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero
      (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
      (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))) rfl

end StatMech.FrontierA
