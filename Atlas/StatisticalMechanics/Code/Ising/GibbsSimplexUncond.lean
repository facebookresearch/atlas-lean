/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Ising.AeTailInvariantProve2
import Code.Ising.PlusStateTI
import Code.Ising.FVConsistencyProve

























open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}










theorem gsu_plusState_ergodic_extreme_of_decay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pst_PlusIntegralShiftDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  atip2_plusState_isErgodic_extremePoint β h hd hβ hh
    (pst_plusState_isTranslationInvariant_of_decay β h hdecay)
    (psdlr_plusState_isDLR_uncond β h)



theorem gsu_minusState_ergodic_extreme_of_decay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pst_MinusIntegralShiftDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  atip2_minusState_isErgodic_extremePoint β h hd hβ hh
    (pst_minusState_isTranslationInvariant_of_decay β h hdecay) hdlr

end Ising

end StatMech
