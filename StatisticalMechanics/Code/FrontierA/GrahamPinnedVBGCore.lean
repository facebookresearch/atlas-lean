/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.GHSVertexPartition
import Code.Ising.IsingFKGLayer
import Code.Walls.vbgtriangle

open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamZeroProb
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (s : ConfigSpace V) : Real :=
  wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0)

theorem grahamZeroProb_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) :
    (0 : ConfigSpace V -> Real) <= grahamZeroProb E J := by
  intro s
  exact div_nonneg (wJ_nonneg E J (fun _ => 0) s)
    (ZJ_pos E J (fun _ => 0)).le

theorem grahamZeroProb_sum_eq_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) :
    ∑ s, grahamZeroProb E J s = 1 := by
  unfold grahamZeroProb ZJ
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun s _ => wJ_pos E J (fun _ => 0) s)
    Finset.univ_nonempty).ne'


theorem vbg_exp_grahamZeroProb_eq_expJ
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (f : ConfigSpace V -> Real) :
    vbg_exp (grahamZeroProb E J) f = expJ E J (fun _ => 0) f := by
  unfold vbg_exp grahamZeroProb expJ
  calc
    (∑ s, (wJ E J (fun _ => 0) s / ZJ E J (fun _ => 0)) * f s) =
        ∑ s, (f s * wJ E J (fun _ => 0) s) / ZJ E J (fun _ => 0) := by
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = _ := by rw [← Finset.sum_div]


theorem graham_wJ_zero_logSupermodular
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) :
    StatMech.FKGLatticeCondition (wJ E J (fun _ => 0)) := by
  intro a b
  unfold wJ
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hbond :
      (∑ e ∈ E, J e * bond a e) + (∑ e ∈ E, J e * bond b e) <=
        (∑ e ∈ E, J e * bond (a ⊔ b) e) +
          (∑ e ∈ E, J e * bond (a ⊓ b) e) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e he
    have hb := ifk_bond_supermodular a b e
    have hm := mul_le_mul_of_nonneg_left hb (hJ e he)
    nlinarith
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  exact hbond


theorem grahamZeroProb_FKG
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ E, 0 <= J e) :
    StatMech.FKGLatticeCondition (grahamZeroProb E J) := by
  intro a b
  unfold grahamZeroProb
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right
    (graham_wJ_zero_logSupermodular E J hJ a b)
    (mul_nonneg (ZJ_pos E J (fun _ => 0)).le
      (ZJ_pos E J (fun _ => 0)).le)


theorem expJ_zero_spin_eq_zero
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (x : V) :
    expJ E J (fun _ => 0) (fun s => spin s x) = 0 := by
  unfold expJ
  have hweight : ∀ s : ConfigSpace V,
      wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) =
        wJ E J (fun _ => 0) s := by
    intro s
    simpa using (ghsvp_wJ_negField_flip E J (fun _ => 0) s)
  let S : Real := ∑ s : ConfigSpace V, spin s x * wJ E J (fun _ => 0) s
  have key : ∀ s : ConfigSpace V,
      spin (StatMech.Sharpness.FieldGhostDict.flipV s) x *
          wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) =
        -(spin s x * wJ E J (fun _ => 0) s) := by
    intro s
    rw [StatMech.Sharpness.FieldGhostDict.spin_flipV, hweight]
    ring
  have hneg : S = -S := by
    have hS : S = ∑ s : ConfigSpace V,
        spin (StatMech.Sharpness.FieldGhostDict.flipV s) x *
          wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) :=
      (Equiv.sum_comp
        (StatMech.Sharpness.FieldGhostDict.flipV_involutive (V := V)).toPerm
        (fun s : ConfigSpace V => spin s x * wJ E J (fun _ => 0) s)).symm
    rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_neg_distrib] at hS
    exact hS
  have hS : S = 0 := by linarith
  rw [show (∑ s : ConfigSpace V, spin s x * wJ E J (fun _ => 0) s) = S from rfl,
    hS, zero_div]



theorem expJ_zero_spinProd_odd_eq_zero
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (A : Finset V) (hA : Odd A.card) :
    expJ E J (fun _ => 0) (spinProd A) = 0 := by
  unfold expJ
  have hweight : ∀ s : ConfigSpace V,
      wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) =
        wJ E J (fun _ => 0) s := by
    intro s
    simpa using (ghsvp_wJ_negField_flip E J (fun _ => 0) s)
  let S : Real := ∑ s : ConfigSpace V, spinProd A s * wJ E J (fun _ => 0) s
  have key : ∀ s : ConfigSpace V,
      spinProd A (StatMech.Sharpness.FieldGhostDict.flipV s) *
          wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) =
        -(spinProd A s * wJ E J (fun _ => 0) s) := by
    intro s
    rw [StatMech.Sharpness.FieldGhostDict.spinProd_flipV_odd A hA, hweight]
    ring
  have hneg : S = -S := by
    have hS : S = ∑ s : ConfigSpace V,
        spinProd A (StatMech.Sharpness.FieldGhostDict.flipV s) *
          wJ E J (fun _ => 0) (StatMech.Sharpness.FieldGhostDict.flipV s) :=
      (Equiv.sum_comp
        (StatMech.Sharpness.FieldGhostDict.flipV_involutive (V := V)).toPerm
        (fun s : ConfigSpace V => spinProd A s * wJ E J (fun _ => 0) s)).symm
    rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_neg_distrib] at hS
    exact hS
  have hS : S = 0 := by linarith
  rw [show (∑ s : ConfigSpace V, spinProd A s * wJ E J (fun _ => 0) s) = S from rfl,
    hS, zero_div]

end StatMech.FrontierA
