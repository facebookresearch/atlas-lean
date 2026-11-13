/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Ising.Transition
import Code.Ising.TransitionUncond
import Code.FK.PcNontrivial
import Code.IsingFK.Q2

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK StatMech.FK










theorem pOfBeta_pos {β : ℝ} (hβ : 0 < β) : 0 < pOfBeta β := by
  unfold pOfBeta
  have : Real.exp (-2 * β) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith



theorem pOfBeta_lt_one (β : ℝ) : pOfBeta β < 1 := by
  unfold pOfBeta
  have : 0 < Real.exp (-2 * β) := Real.exp_pos _
  linarith




theorem fkRoute_pOfBeta_mem_Ioo {β : ℝ} (hβ : 0 < β) : pOfBeta β ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨pOfBeta_pos hβ, pOfBeta_lt_one β⟩




theorem fkRoute_pToBeta_pOfBeta (β : ℝ) : pToBeta 2 (pOfBeta β) = β := by
  rw [pToBeta_two]
  unfold pOfBeta
  rw [show (1 - (1 - Real.exp (-2 * β))) = Real.exp (-2 * β) by ring, Real.log_exp]
  ring

















theorem fkTheta_pos_of_fkPc_lt (d : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hpc : FK.fkPc d 2 < p) :
    0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  have hnn := FK.fkTheta_nonneg d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hmem : p ∈ FK.fkSubcriticalSet d 2 := ⟨hp, hp1, by norm_num, h.symm⟩
    exact absurd (FK.le_fkPc_of_mem hmem) (not_le.mpr hpc)

















theorem fkPc_lt_pOfBeta_iff (d : ℕ) {β : ℝ} (_hβ : 0 < β) (hpc1 : FK.fkPc d 2 < 1) :
    FK.fkPc d 2 < pOfBeta β ↔ pToBeta 2 (FK.fkPc d 2) < β := by
  have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
  have hbij : pToBeta 2 (FK.fkPc d 2) < β ↔ pToBeta 2 (FK.fkPc d 2) < pToBeta 2 (pOfBeta β) := by
    rw [fkRoute_pToBeta_pOfBeta β]
  rw [hbij]
  exact ((strictMonoOn_pToBeta 2 (by norm_num)).lt_iff_lt
    (Set.mem_Iio.mpr hpc1) (Set.mem_Iio.mpr hp1)).symm

















theorem fkTheta_pos_iff_fkPc_lt (d : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) ↔ FK.fkPc d 2 < p := by
  constructor
  · intro hθ
    by_contra hcon
    exact (ne_of_gt hθ) (hFKsub p hp hp1 (not_lt.mp hcon))
  · intro hpc
    exact fkTheta_pos_of_fkPc_lt d hp hp1 hpc





















theorem htransition_fk (d : ℕ)
    (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      (0 < magnetization d β ↔
        0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) := by
  intro β hβ
  have hppos : 0 < pOfBeta β := pOfBeta_pos hβ
  have hp1 : pOfBeta β < 1 := pOfBeta_lt_one β
  rw [hmagPerco β hβ hppos hp1,
    fkTheta_pos_iff_fkPc_lt d hppos hp1 hFKsub,
    fkPc_lt_pOfBeta_iff d hβ hpc1]







theorem htransition_fk_of_identity (d : ℕ)
    (hmagPercoId : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) :=
  htransition_fk d
    (fun β hβ hp hp1 => by rw [hmagPercoId β hβ hp hp1]) hFKsub hpc1
























theorem ising_transition_fk (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      (0 < magnetization d β ↔
        0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition_uncond d hd hmag_nonneg
    (htransition_fk d hmagPerco hFKsub hpc1) hpc1









theorem isingBetaC_eq_fk (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      (0 < magnetization d β ↔
        0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  isingBetaC_eq_uncond d hd hmag_nonneg
    (htransition_fk d hmagPerco hFKsub hpc1) hpc1





theorem isingBetaC_pos_fk (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hmagPerco : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      (0 < magnetization d β ↔
        0 < FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos_uncond d hd hmag_nonneg
    (htransition_fk d hmagPerco hFKsub hpc1) hpc1

end Ising

end StatMech
