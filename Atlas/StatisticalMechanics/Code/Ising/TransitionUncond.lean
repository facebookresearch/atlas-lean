/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Ising.Transition
import Code.FK.PcNontrivial

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK












theorem fkPc_two_pos_of_two_le {d : ℕ} (hd : 2 ≤ d) : 0 < FK.fkPc d 2 :=
  FK.fkPc_pos_of_two_le hd (by norm_num)




























theorem ising_transition_uncond (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1













theorem isingBetaC_eq_uncond (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  ising_betaC_eq d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1






theorem isingBetaC_pos_uncond (d : ℕ) (hd : 2 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (htransition : ∀ β, 0 < β →
      (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos d hmag_nonneg htransition (fkPc_two_pos_of_two_le hd) hpc1

end Ising

end StatMech
