/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamPinnedVBGCore

open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamPinnedProb
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    ConfigSpace V -> Real :=
  vbg_condPlus (grahamZeroProb E J) (vbg_coordUp m)


theorem vbg_exp_grahamPinnedProb_eq
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V)
    (f : ConfigSpace V -> Real) :
    vbg_exp (grahamPinnedProb E J m) f =
      vbg_exp (grahamZeroProb E J)
        (fun s => vbg_coordUp m s * f s) /
          vbg_exp (grahamZeroProb E J) (vbg_coordUp m) := by
  unfold grahamPinnedProb
  rw [vbg_expPlus_eq]
  congr 1
  unfold vbg_exp
  apply Finset.sum_congr rfl
  intro s _
  ring


theorem grahamZeroProb_coordUp_eq_half
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    vbg_exp (grahamZeroProb E J) (vbg_coordUp m) = (1 : Real) / 2 := by
  have hzero : vbg_exp (grahamZeroProb E J) (fun s => spin s m) = 0 := by
    rw [vbg_exp_grahamZeroProb_eq_expJ, expJ_zero_spin_eq_zero]
  have hrel : vbg_exp (grahamZeroProb E J) (fun s => spin s m) =
      2 * vbg_exp (grahamZeroProb E J) (vbg_coordUp m) - 1 := by
    unfold vbg_exp
    rw [show (∑ s, grahamZeroProb E J s * spin s m) =
        2 * (∑ s, grahamZeroProb E J s * vbg_coordUp m s) -
          ∑ s, grahamZeroProb E J s by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      rw [vbg_spin_eq_coordUp]
      ring]
    rw [grahamZeroProb_sum_eq_one]
  linarith



theorem grahamPinnedProb_spin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m x : V) :
    vbg_exp (grahamPinnedProb E J m) (fun s => spin s x) =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s m) := by
  rw [vbg_exp_grahamPinnedProb_eq, grahamZeroProb_coordUp_eq_half]
  have hfun : (fun s : ConfigSpace V => vbg_coordUp m s * spin s x) =
      (fun s => ((1 : Real) / 2) *
        ((spin s x * spin s m) + spin s x)) := by
    funext s
    unfold vbg_coordUp spin
    by_cases hm : s m <;> by_cases hx : s x <;> simp [hm, hx] <;> norm_num
  rw [hfun, vbg_exp_const_mul, vbg_exp_add,
    vbg_exp_grahamZeroProb_eq_expJ, vbg_exp_grahamZeroProb_eq_expJ,
    expJ_zero_spin_eq_zero]
  ring



theorem grahamPinnedProb_twoSpin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    {m x y : V} (hxy : x ≠ y) (hxm : x ≠ m) (hym : y ≠ m) :
    vbg_exp (grahamPinnedProb E J m) (fun s => spin s x * spin s y) =
      expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
  rw [vbg_exp_grahamPinnedProb_eq, grahamZeroProb_coordUp_eq_half]
  have hfun : (fun s : ConfigSpace V =>
      vbg_coordUp m s * (spin s x * spin s y)) =
      (fun s => ((1 : Real) / 2) *
        ((spin s x * spin s y * spin s m) + spin s x * spin s y)) := by
    funext s
    unfold vbg_coordUp spin
    by_cases hm : s m <;> by_cases hx : s x <;>
      by_cases hy : s y <;> simp [hm, hx, hy] <;> norm_num
  have htriple : expJ E J (fun _ => 0)
      (fun s => spin s x * spin s y * spin s m) = 0 := by
    have hcard : #({x, y, m} : Finset V) = 3 := by
      simp [hxy, hxm, hym]
    have hodd : Odd (#({x, y, m} : Finset V)) := by rw [hcard]; decide
    have hzero := expJ_zero_spinProd_odd_eq_zero E J {x, y, m} hodd
    rw [show spinProd ({x, y, m} : Finset V) =
        (fun s => spin s x * spin s y * spin s m) by
      funext s
      simp [spinProd, hxy, hxm, hym]
      ring] at hzero
    exact hzero
  rw [hfun, vbg_exp_const_mul, vbg_exp_add,
    vbg_exp_grahamZeroProb_eq_expJ, vbg_exp_grahamZeroProb_eq_expJ, htriple]
  ring

end StatMech.FrontierA
