/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.IsingFK.BetacPc

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK








theorem pToBeta_two_pos {pc : ℝ} (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    0 < pToBeta 2 pc := by
  rw [pToBeta_two]
  have hlt : Real.log (1 - pc) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith [hlt]




















theorem abstract_ising_transition (mStar : ℝ → ℝ) (pc : ℝ)
    (hmag_nonneg : ∀ β, 0 ≤ mStar β)
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
    exact le_antisymm (not_lt.mp hnotpos) (hmag_nonneg β)
  · 
    intro β hββc
    exact (htransition β (lt_trans hβc_pos hββc)).mpr hββc

























theorem ising_transition (d : ℕ)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ⟨pToBeta 2 (FK.fkPc d 2),
    abstract_ising_transition (magnetization d) (FK.fkPc d 2)
      hmag_nonneg htransition hpc0 hpc1⟩











theorem ising_betaC_eq (d : ℕ)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  rw [betaC_eq_log (magnetization d) 2 (FK.fkPc d 2) hmag_nonneg htransition
        (pToBeta_two_pos hpc0 hpc1)]
  norm_num





theorem isingBetaC_pos (d : ℕ)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) := by
  rw [betaC_eq (magnetization d) 2 (FK.fkPc d 2) hmag_nonneg htransition
        (pToBeta_two_pos hpc0 hpc1)]
  exact pToBeta_two_pos hpc0 hpc1

end Ising

end StatMech
