/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.IsingCylinderTransfer

open Finset Matrix
open scoped BigOperators

namespace StatMech.Ising




theorem dot_mulVec_pow_eq_sum_path
    {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (ell a : E -> R) (n : Nat) :
    (∑ s, ell s * ((A ^ n) *ᵥ a) s) =
      ∑ q : Fin (n + 1) -> E,
        ell (q 0) *
          (∏ k : Fin n, A (q k.castSucc) (q k.succ)) *
          a (q (Fin.last n)) := by
  induction n generalizing a with
  | zero =>
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin 1 => E)]
      rw [Fintype.sum_prod_type]
      simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih]
      simp only [Matrix.mulVec, dotProduct]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [← Fintype.sum_prod_type']
      rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 2) => E)]
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨s, q⟩ := x
      rw [show (Fin.snocEquiv fun _ : Fin (n + 2) => E) (s, q) =
          Fin.snoc q s from rfl]
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.succ_last,
        Fin.snoc_last, Fin.snoc_apply_zero]
      have hsnoc (i : Fin n) :
          (Fin.snoc q s : Fin (n + 2) -> E) i.castSucc.succ = q i.succ := by
        rw [show i.castSucc.succ = i.succ.castSucc by rfl,
          Fin.snoc_castSucc]
      simp_rw [hsnoc]
      ring



theorem isingCylinderPartition_eq_sum_path
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real)
    (leftBoundary rightBoundary : ConfigSpace W -> Real) (n : Nat) :
    isingCylinderPartition E J h Jvertical leftBoundary rightBoundary n =
      ∑ q : Fin (n + 1) -> ConfigSpace W,
        Real.exp
          (rightBoundary (q 0) + leftBoundary (q (Fin.last n)) +
            (∑ k : Fin (n + 1),
              cylinderLayerInteraction E J h (q k)) +
            ∑ k : Fin n,
              cylinderInterLayerInteraction Jvertical
                (q k.castSucc) (q k.succ)) := by
  rw [isingCylinderPartition]
  rw [dot_mulVec_pow_eq_sum_path]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [isingCylinderBoundaryVector, isingCylinderTransfer]
  rw [← Real.exp_sum]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hfirst := Fin.sum_univ_succ
    (f := fun k : Fin (n + 1) => cylinderLayerInteraction E J h (q k))
  have hlast := Fin.sum_univ_castSucc
    (f := fun k : Fin (n + 1) => cylinderLayerInteraction E J h (q k))
  linear_combination -(1 / 2 : Real) * hfirst - (1 / 2 : Real) * hlast

end StatMech.Ising
