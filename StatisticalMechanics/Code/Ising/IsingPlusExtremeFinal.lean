/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Ising.IsingCrossBoxCap
import Code.Ising.IsingPlusTIClose
import Code.Ising.IsingPlusErgodicClose




























namespace StatMech.Ising

open StatMech StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}





theorem ipx_plusState_isInvariantExtremePoint_of_homogeneous
    (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hhom : ∀ g : Multiplicative (Lattice.Site d), iti_PlusMultiHomogeneous β h g) :
    StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Lattice.Site d))
      (plusState d β h : Measure (ConfigSpace (Lattice.Site d))) := by
  have hti := iti_plusState_isTranslationInvariant_of_homogeneous β h hhom
  have hdecay := icb_plusState_upperDecay hd hβ hh hti
  exact ipe_plusState_isInvariantExtremePoint_of_upperDecay hβ h hti hdecay



theorem ipx_plusState_isErgodic_of_homogeneous
    (hd : 1 ≤ d) {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (hhom : ∀ g : Multiplicative (Lattice.Site d), iti_PlusMultiHomogeneous β h g) :
    IsErgodic (G := Multiplicative (Lattice.Site d))
      (plusState d β h : Measure (ConfigSpace (Lattice.Site d))) := by
  have hti := iti_plusState_isTranslationInvariant_of_homogeneous β h hhom
  have hdecay := icb_plusState_upperDecay hd hβ hh hti
  exact ipe_plusState_isErgodic_of_upperDecay hβ h hti hdecay

end StatMech.Ising
