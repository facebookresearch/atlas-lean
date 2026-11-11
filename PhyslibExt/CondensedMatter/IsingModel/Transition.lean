/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BetacPc

/-!
# The Ising phase transition from the FK critical point

If the magnetization is positive exactly above the inverse temperature of the FK critical point, the
Ising model has a phase transition there.

## i. Overview

For `q = 2`, the FK edge parameter `p` corresponds to `β = -½ log (1 - p)`. If the magnetization is
nonnegative and is positive exactly when `β > β(p_c)`, with `0 < p_c < 1`, then `β_c = -½ log (1 -
p_c) > 0`, the magnetization vanishes below `β_c` and is positive above.

The statements here are conditional: they take as hypotheses the identification of the Ising
magnetization with the FK percolation probability and the nontriviality of the FK critical point.
The unconditional phase transition for `d ≥ 2` is `ising_phase_transition_of_two_le` in
`FKRepresentation.PcUpperAllDimensions`.

## ii. Key results

- `StatMech.Ising.abstract_ising_transition` : an abstract phase transition from a threshold
- `StatMech.Ising.ising_transition` : the phase transition under the FK hypotheses
- `StatMech.Ising.ising_betaC_eq` : `β_c = -½ log (1 - p_c)`

## iii. Table of contents

- A. The FK parameter
- B. The phase transition

## iv. References

- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, PIMS–CRM
  Summer School in Probability (2017), arXiv:1707.00520
- G. Grimmett, *The Random-Cluster Model*, Springer (2006)
-/

@[expose] public section

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK

/-! ## A. The FK parameter -/

lemma pToBeta_two_pos {pc : ℝ} (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    0 < pToBeta 2 pc := by
  rw [pToBeta_two]
  have hlt : Real.log (1 - pc) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith [hlt]

/-! ## B. The phase transition -/

lemma abstract_ising_transition (mStar : ℝ → ℝ) (pc : ℝ)
    (hmag_nonneg : ∀ β, 0 ≤ mStar β)
    (htransition : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta 2 pc < β))
    (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    0 < pToBeta 2 pc ∧
      (∀ β, 0 < β → β < pToBeta 2 pc → mStar β = 0) ∧
      (∀ β, pToBeta 2 pc < β → 0 < mStar β) := by
  have hβc_pos : 0 < pToBeta 2 pc := pToBeta_two_pos hpc0 hpc1
  refine ⟨hβc_pos, ?_, ?_⟩
  · intro β hβ0 hββc
    have hnotpos : ¬ (0 < mStar β) := by
      rw [htransition β hβ0]; exact not_lt.mpr hββc.le
    exact le_antisymm (not_lt.mp hnotpos) (hmag_nonneg β)
  · intro β hββc
    exact (htransition β (lt_trans hβc_pos hββc)).mpr hββc

lemma ising_transition (d : ℕ)
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

lemma ising_betaC_eq (d : ℕ)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  rw [betaC_eq_log (magnetization d) 2 (FK.fkPc d 2) hmag_nonneg htransition
        (pToBeta_two_pos hpc0 hpc1)]
  norm_num

lemma isingBetaC_pos (d : ℕ)
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
