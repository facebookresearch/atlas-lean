/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Ising.Magnetization
import Code.Sharpness.TildeBc

open Set

namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {d : ℕ}


theorem tildeBetaCIsing_nonneg : 0 ≤ tildeBetaCIsing d := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  unfold tildeBetaCIsing
  by_cases hbdd : BddAbove (tildeBetaCIsingSet d)
  · exact le_csSup hbdd hzero
  · rw [csSup_of_not_bddAbove hbdd, Real.sSup_empty]

















theorem bc_le_tildeBc_ising
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β) :
    betaC d ≤ tildeBetaCIsing d := by
  unfold betaC
  
  
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro β' hβ'
  exact csInf_le hbdd
    ⟨(tildeBetaCIsing_nonneg (d := d)).trans hβ'.le, hpos β' hβ'⟩

















theorem tildeBc_le_bc_ising
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    tildeBetaCIsing d ≤ betaC d := by
  unfold betaC
  refine le_csInf hne ?_
  intro β hβ
  by_contra hcon
  rw [not_le] at hcon
  
  rw [mem_positiveMagnetizationSet] at hβ
  have hz := hzero β hβ.1 hcon
  rw [hz] at hβ
  exact lt_irrefl 0 hβ.2
















theorem bc_eq_ising
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d :=
  le_antisymm (bc_le_tildeBc_ising hbdd hpos) (tildeBc_le_bc_ising hne hzero)















theorem posMag_of_meanfield_sqrt (htc_pos : 0 < tildeBetaCIsing d)
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
    ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
  intro β hβ
  have hβpos : 0 < β := lt_trans htc_pos hβ
  
  have hlt1 : (tildeBetaCIsing d / β) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    apply sq_lt_sq'
    · nlinarith [htc_pos]
    · exact hβ
  have hsqrtpos : 0 < Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) :=
    Real.sqrt_pos.mpr (by linarith)
  exact lt_of_lt_of_le hsqrtpos (hsqrt β hβ.le)



theorem posMag_of_meanfield_sqrt_nonneg
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
    ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
  rcases (tildeBetaCIsing_nonneg (d := d)).eq_or_lt with hzero | hpos
  · intro β hβ
    have htc : tildeBetaCIsing d = 0 := hzero.symm
    have hβpos : 0 < β := by simpa [htc] using hβ
    have hone : (1 : ℝ) ≤ magnetization d β := by
      simpa [htc] using hsqrt β hβ.le
    linarith
  · exact posMag_of_meanfield_sqrt hpos hsqrt



theorem positiveMagnetizationSet_bddBelow :
    BddBelow (positiveMagnetizationSet d) := by
  refine ⟨0, ?_⟩
  intro β hβ
  exact (mem_positiveMagnetizationSet.mp hβ).1





theorem bc_eq_ising_of_items
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d := by
  have hpos := posMag_of_meanfield_sqrt_nonneg (d := d) hsqrt
  have hbdd := positiveMagnetizationSet_bddBelow (d := d)
  have hne : (positiveMagnetizationSet d).Nonempty := by
    refine ⟨tildeBetaCIsing d + 1, ?_⟩
    exact ⟨by linarith [tildeBetaCIsing_nonneg (d := d)], hpos _ (by linarith)⟩
  exact bc_eq_ising hbdd hne hpos hzero








theorem bc_eq_ising_of_meanfield (htc_pos : 0 < tildeBetaCIsing d)
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d :=
  bc_eq_ising hbdd hne (posMag_of_meanfield_sqrt htc_pos hsqrt) hzero

end Sharpness

end StatMech
