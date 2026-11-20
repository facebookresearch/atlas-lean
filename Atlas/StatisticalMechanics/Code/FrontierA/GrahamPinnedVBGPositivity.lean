/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamPinnedVBGMoments

open Finset
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace
open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem grahamPinnedProb_nonneg
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    (0 : ConfigSpace V -> Real) <= grahamPinnedProb E J m := by
  unfold grahamPinnedProb
  apply vbg_condPlus_nonneg
  · exact grahamZeroProb_nonneg E J
  · intro s
    unfold vbg_coordUp
    by_cases h : s m <;> simp [h]
  · rw [grahamZeroProb_coordUp_eq_half]
    norm_num

theorem grahamPinnedProb_sum_eq_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    ∑ s, grahamPinnedProb E J m s = 1 := by
  unfold grahamPinnedProb
  apply vbg_condPlus_norm
  rw [grahamZeroProb_coordUp_eq_half]
  norm_num



theorem grahamPinned_coordUp_pos_lt_one
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    {m k : V} (hmk : m ≠ k) :
    0 < vbg_exp (grahamPinnedProb E J m) (vbg_coordUp k) ∧
      vbg_exp (grahamPinnedProb E J m) (vbg_coordUp k) < 1 := by
  let sUp : ConfigSpace V := fun _ => true
  let sDown : ConfigSpace V := fun x => if x = k then false else true
  have hmassUp : 0 < grahamPinnedProb E J m sUp := by
    unfold grahamPinnedProb vbg_condPlus
    rw [grahamZeroProb_coordUp_eq_half]
    unfold grahamZeroProb
    simp [sUp, vbg_coordUp]
    exact div_pos (wJ_pos E J (fun _ => 0) sUp)
      (ZJ_pos E J (fun _ => 0))
  have hmassDown : 0 < grahamPinnedProb E J m sDown := by
    unfold grahamPinnedProb vbg_condPlus
    have hm : sDown m = true := by simp [sDown, hmk]
    rw [show vbg_coordUp m sDown = 1 by simp [vbg_coordUp, hm]]
    rw [grahamZeroProb_coordUp_eq_half]
    unfold grahamZeroProb
    simp only [mul_one]
    exact div_pos
      (div_pos (wJ_pos E J (fun _ => 0) sDown)
        (ZJ_pos E J (fun _ => 0))) (by norm_num)
  constructor
  · unfold vbg_exp
    apply Finset.sum_pos'
    · intro s _
      exact mul_nonneg (grahamPinnedProb_nonneg E J m s)
        (by unfold vbg_coordUp; by_cases h : s k <;> simp [h])
    · refine ⟨sUp, Finset.mem_univ _, ?_⟩
      simpa [sUp, vbg_coordUp] using hmassUp
  · have hcomp : 0 < vbg_exp (grahamPinnedProb E J m)
        (fun s => 1 - vbg_coordUp k s) := by
      unfold vbg_exp
      apply Finset.sum_pos'
      · intro s _
        exact mul_nonneg (grahamPinnedProb_nonneg E J m s)
          (by unfold vbg_coordUp; by_cases h : s k <;> simp [h])
      · refine ⟨sDown, Finset.mem_univ _, ?_⟩
        have hk : sDown k = false := by simp [sDown]
        simpa [vbg_coordUp, hk] using hmassDown
    rw [vbg_exp_one_sub (grahamPinnedProb_sum_eq_one E J m)] at hcomp
    linarith

end StatMech.FrontierA
