/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Ising.Transition
import Code.Ising.TransitionUncond
import Code.Ising.TransitionFK

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK StatMech.FK






















theorem abstract_ising_transition_regime (mStar : ℝ → ℝ) (pc : ℝ)
    (hmag_nonneg_pos : ∀ β, 0 < β → 0 ≤ mStar β)
    (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
    (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    0 < pToBeta 2 pc ∧
      (∀ β, 0 < β → β < pToBeta 2 pc → mStar β = 0) ∧
      (∀ β, pToBeta 2 pc < β → 0 < mStar β) := by
  have hβc_pos : 0 < pToBeta 2 pc := pToBeta_two_pos hpc0 hpc1
  refine ⟨hβc_pos, ?_, ?_⟩
  · 
    intro β hβ0 hββc
    have hnotpos : ¬ (0 < mStar β) := by
      rw [htransition β hβ0]; exact not_lt.mpr hββc.le
    exact le_antisymm (not_lt.mp hnotpos) (hmag_nonneg_pos β hβ0)
  · 
    intro β hββc
    exact (htransition β (lt_trans hβc_pos hββc)).mpr hββc












theorem betaC_eq_regime (mStar : ℝ → ℝ) (pc : ℝ)
    (hmag_nonneg_pos : ∀ β, 0 < β → 0 ≤ mStar β)
    (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
    (hpos : 0 < pToBeta 2 pc) :
    IsingFK.betaC mStar = pToBeta 2 pc := by
  unfold IsingFK.betaC
  have hset : {β : ℝ | 0 < β ∧ mStar β = 0} = Set.Ioc 0 (pToBeta 2 pc) := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_Ioc]
    refine and_congr_right fun hβ => ?_
    have hzero_iff : mStar β = 0 ↔ ¬ (0 < mStar β) := by
      constructor
      · intro h; rw [h]; exact lt_irrefl 0
      · intro h; exact le_antisymm (not_lt.mp h) (hmag_nonneg_pos β hβ)
    rw [hzero_iff, htransition β hβ, not_lt]
  rw [hset, csSup_Ioc hpos]

















theorem magnetization_nonneg_of_percoId (d : ℕ)
    (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
    ∀ β, 0 < β → 0 ≤ magnetization d β := by
  intro β hβ
  have hppos : 0 < pOfBeta β := pOfBeta_pos hβ
  have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
  rw [hmagPercoId β hβ hppos hp1]
  exact FK.fkTheta_nonneg d hppos hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)





































theorem ising_transition_of_fkPc_lt_one (d : ℕ) (hd : 2 ≤ d)
    (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ⟨pToBeta 2 (FK.fkPc d 2),
    abstract_ising_transition_regime (magnetization d) (FK.fkPc d 2)
      (magnetization_nonneg_of_percoId d hmagPercoId)
      (htransition_fk_of_identity d hmagPercoId hFKsub hpc1)
      (fkPc_two_pos_of_two_le hd) hpc1⟩









theorem isingBetaC_eq_of_fkPc_lt_one (d : ℕ) (hd : 2 ≤ d)
    (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  have hpos : 0 < pToBeta 2 (FK.fkPc d 2) :=
    pToBeta_two_pos (fkPc_two_pos_of_two_le hd) hpc1
  rw [betaC_eq_regime (magnetization d) (FK.fkPc d 2)
      (magnetization_nonneg_of_percoId d hmagPercoId)
      (htransition_fk_of_identity d hmagPercoId hFKsub hpc1) hpos,
    pToBeta_two]





theorem isingBetaC_pos_of_fkPc_lt_one (d : ℕ) (hd : 2 ≤ d)
    (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) := by
  have hpos : 0 < pToBeta 2 (FK.fkPc d 2) :=
    pToBeta_two_pos (fkPc_two_pos_of_two_le hd) hpc1
  rw [betaC_eq_regime (magnetization d) (FK.fkPc d 2)
      (magnetization_nonneg_of_percoId d hmagPercoId)
      (htransition_fk_of_identity d hmagPercoId hFKsub hpc1) hpos]
  exact hpos

end Ising

end StatMech
