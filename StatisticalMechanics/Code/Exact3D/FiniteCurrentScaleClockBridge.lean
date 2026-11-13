/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FiniteCurrentToExponent
import Code.Exact3D.ScaleClockBridge










namespace StatMech
namespace Exact3D

set_option linter.style.longLine false in








structure FreePositiveSubcriticalMassScaleClockNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  logError : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  clock_ratio_tendsto :
    Filter.Tendsto
      (fun β : ℝ =>
        clock β / (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds ((Real.log relevantEigenvalue)⁻¹))
  logError_negligible :
    Filter.Tendsto
      (fun β : ℝ => logError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_scaleClock :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + logError β

namespace FreePositiveSubcriticalMassScaleClockNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical D hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  logError := h.logError
  mass_pos := h.mass_pos
  clock_ratio_tendsto := h.clock_ratio_tendsto
  logError_negligible := h.logError_negligible
  log_mass_scaleClock := h.log_mass_scaleClock

end FreePositiveSubcriticalMassScaleClockNearCritical

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassAnnulusScaleClockNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  cLo : ℝ
  cLo_pos : 0 < cLo
  cHi : ℝ
  cHi_pos : 0 < cHi
  clock_annulus :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ∧
        Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ≤ cHi
  logError : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  logError_negligible :
    Filter.Tendsto
      (fun β : ℝ => logError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_scaleClock :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + logError β

namespace FreePositiveSubcriticalMassAnnulusScaleClockNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical D hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  logError := h.logError
  mass_pos := h.mass_pos
  logError_negligible := h.logError_negligible
  log_mass_scaleClock := h.log_mass_scaleClock

end FreePositiveSubcriticalMassAnnulusScaleClockNearCritical

set_option linter.style.longLine false in







structure FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  cLo : ℝ
  cLo_pos : 0 < cLo
  cHi : ℝ
  cHi_pos : 0 < cHi
  clock_annulus :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ∧
        Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ≤ cHi
  terminalLog : ℝ → ℝ
  terminalLogBound : ℝ
  terminalLog_eventually_abs_le :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      |terminalLog β| ≤ terminalLogBound
  accumulatedError : ℝ → ℝ
  averageAccumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_averageError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  terminalLog := h.terminalLog
  terminalLogBound := h.terminalLogBound
  terminalLog_eventually_abs_le := h.terminalLog_eventually_abs_le
  accumulatedError := h.accumulatedError
  averageAccumulatedError_negligible :=
    h.averageAccumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_averageError := h.log_mass_averageError

set_option linter.style.longLine false in


theorem clockError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        (h.clock β -
            criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
      Ising3DModel h.clock h.relevantEigenvalue h.cLo h.cHi
      h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus))

set_option linter.style.longLine false in


theorem accumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_log_betaC_sub_of_annulus_clock_average
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue h.cLo
      h.cHi h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus)
      (by simpa [Ising3DModel] using h.averageAccumulatedError_negligible))

end FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  cLo := havg.cLo
  cLo_pos := havg.cLo_pos
  cHi := havg.cHi
  cHi_pos := havg.cHi_pos
  clock_annulus := havg.clock_annulus
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogBound havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus)
        (by simpa [Ising3DModel] using havg.terminalLog_eventually_abs_le)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_averageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  cLo : ℝ
  cLo_pos : 0 < cLo
  cHi : ℝ
  cHi_pos : 0 < cHi
  clock_annulus :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ∧
        Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ≤ cHi
  terminalLog : ℝ → ℝ
  terminalLogLimit : ℝ
  terminalLog_tendsto :
    Filter.Tendsto terminalLog
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds terminalLogLimit)
  accumulatedError : ℝ → ℝ
  averageAccumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_terminalAverageError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  terminalLog := h.terminalLog
  terminalLogLimit := h.terminalLogLimit
  terminalLog_tendsto := h.terminalLog_tendsto
  accumulatedError := h.accumulatedError
  averageAccumulatedError_negligible :=
    h.averageAccumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_terminalAverageError := h.log_mass_terminalAverageError

set_option linter.style.longLine false in


theorem clockError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        (h.clock β -
            criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
      Ising3DModel h.clock h.relevantEigenvalue h.cLo h.cHi
      h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus))

set_option linter.style.longLine false in


theorem accumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_log_betaC_sub_of_annulus_clock_average
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue h.cLo
      h.cHi h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus)
      (by simpa [Ising3DModel] using h.averageAccumulatedError_negligible))

end FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  cLo : ℝ
  cLo_pos : 0 < cLo
  cHi : ℝ
  cHi_pos : 0 < cHi
  clock_annulus :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ∧
        Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ≤ cHi
  terminalLog : ℝ → ℝ
  terminalLogLimit : ℝ
  terminalLog_tendsto :
    Filter.Tendsto terminalLog
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds terminalLogLimit)
  accumulatedError : ℝ → ℝ
  accumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_terminalError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  terminalLog := h.terminalLog
  terminalLogLimit := h.terminalLogLimit
  terminalLog_tendsto := h.terminalLog_tendsto
  accumulatedError := h.accumulatedError
  accumulatedError_negligible := h.accumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_terminalError := h.log_mass_terminalError

set_option linter.style.longLine false in


theorem clockError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        (h.clock β -
            criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
      Ising3DModel h.clock h.relevantEigenvalue h.cLo h.cHi
      h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus))

set_option linter.style.longLine false in


theorem averageAccumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / h.clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue h.cLo
      h.cHi h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus)
      (by simpa [Ising3DModel] using h.accumulatedError_negligible))

end FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  cLo : ℝ
  cLo_pos : 0 < cLo
  cHi : ℝ
  cHi_pos : 0 < cHi
  clock_annulus :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      cLo ≤ Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ∧
        Real.exp (clock β * Real.log relevantEigenvalue) *
            (Ising.betaC 3 - β) ≤ cHi
  terminalLog : ℝ → ℝ
  terminalLogBound : ℝ
  terminalLog_eventually_abs_le :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      |terminalLog β| ≤ terminalLogBound
  accumulatedError : ℝ → ℝ
  accumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_boundedTerminalError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  terminalLog := h.terminalLog
  terminalLogBound := h.terminalLogBound
  terminalLog_eventually_abs_le := h.terminalLog_eventually_abs_le
  accumulatedError := h.accumulatedError
  accumulatedError_negligible := h.accumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_boundedTerminalError := h.log_mass_boundedTerminalError

set_option linter.style.longLine false in


theorem clockError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        (h.clock β -
            criticalDistanceScaleClock Ising3DModel h.relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
      Ising3DModel h.clock h.relevantEigenvalue h.cLo h.cHi
      h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus))

set_option linter.style.longLine false in


theorem averageAccumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / h.clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue h.cLo
      h.cHi h.relevantEigenvalue_gt_one h.cLo_pos h.cHi_pos
      (by simpa [Ising3DModel] using h.clock_annulus)
      (by simpa [Ising3DModel] using h.accumulatedError_negligible))

end FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  logError := fun β => hterm.terminalLog β + hterm.accumulatedError β
  mass_pos := hterm.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogLimit
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_terminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  logError := fun β => hterm.terminalLog β + hterm.accumulatedError β
  mass_pos := hterm.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogBound
        (by simpa [Ising3DModel] using hterm.terminalLog_eventually_abs_le)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_boundedTerminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  terminalLog := hterm.terminalLog
  terminalLogBound := |hterm.terminalLogLimit| + 1
  terminalLog_eventually_abs_le := by
    exact
      eventually_abs_le_abs_limit_add_one_of_tendsto
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_boundedTerminalError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockTerminalAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  terminalLog := hterm.terminalLog
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue hterm.cLo hterm.cHi
        hterm.relevantEigenvalue_gt_one hterm.cLo_pos hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_terminalAverageError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  cLo := hterm.cLo
  cLo_pos := hterm.cLo_pos
  cHi := hterm.cHi
  cHi_pos := hterm.cHi_pos
  clock_annulus := hterm.clock_annulus
  terminalLog := hterm.terminalLog
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub_of_annulus
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue hterm.cLo hterm.cHi
        hterm.relevantEigenvalue_gt_one hterm.cLo_pos hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_averageError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  cLo := havg.cLo
  cLo_pos := havg.cLo_pos
  cHi := havg.cHi
  cHi_pos := havg.cHi_pos
  clock_annulus := havg.clock_annulus
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogLimit havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus)
        (by simpa [Ising3DModel] using havg.terminalLog_tendsto)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_terminalAverageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass where
  δ := hann.δ
  δ_pos := hann.δ_pos
  δ_le_betaC := hann.δ_le_betaC
  scaleBase := hann.scaleBase
  scaleBase_gt_one := hann.scaleBase_gt_one
  relevantEigenvalue := hann.relevantEigenvalue
  relevantEigenvalue_gt_one := hann.relevantEigenvalue_gt_one
  predictedExponent_eq := hann.predictedExponent_eq
  clock := hann.clock
  logError := hann.logError
  mass_pos := hann.mass_pos
  clock_ratio_tendsto := by
    exact
      (tendsto_scaleClock_ratio_of_eventually_annulus
        Ising3DModel hann.clock hann.relevantEigenvalue hann.cLo hann.cHi
        hann.relevantEigenvalue_gt_one hann.cLo_pos hann.cHi_pos
        (by simpa [Ising3DModel] using hann.clock_annulus))
  logError_negligible := hann.logError_negligible
  log_mass_scaleClock := hann.log_mass_scaleClock

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  logError : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  logError_negligible :
    Filter.Tendsto
      (fun β : ℝ => logError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_criticalDistanceScaleClock :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) *
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β +
          logError β

namespace FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  logError := h.logError
  mass_pos := h.mass_pos
  logError_negligible := h.logError_negligible
  log_mass_criticalDistanceScaleClock :=
    h.log_mass_criticalDistanceScaleClock

end FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := hcal.δ
  δ_pos := hcal.δ_pos
  δ_le_betaC := hcal.δ_le_betaC
  scaleBase := hcal.scaleBase
  scaleBase_gt_one := hcal.scaleBase_gt_one
  relevantEigenvalue := hcal.relevantEigenvalue
  relevantEigenvalue_gt_one := hcal.relevantEigenvalue_gt_one
  predictedExponent_eq := hcal.predictedExponent_eq
  clock := criticalDistanceScaleClock Ising3DModel hcal.relevantEigenvalue
  cLo := 1
  cLo_pos := zero_lt_one
  cHi := 1
  cHi_pos := zero_lt_one
  clock_annulus := by
    simpa [Ising3DModel] using
      criticalDistanceScaleClock_annulus_eventually
        Ising3DModel hcal.relevantEigenvalue_gt_one
  logError := hcal.logError
  mass_pos := hcal.mass_pos
  logError_negligible := hcal.logError_negligible
  log_mass_scaleClock := hcal.log_mass_criticalDistanceScaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in





structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  logError : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  logError_negligible :
    Filter.Tendsto
      (fun β : ℝ => logError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_scaleClock :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + logError β

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  clockError_negligible := h.clockError_negligible
  logError := h.logError
  mass_pos := h.mass_pos
  logError_negligible := h.logError_negligible
  log_mass_scaleClock := h.log_mass_scaleClock

set_option linter.style.longLine false in

theorem clock_ratio_tendsto
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ =>
        h.clock β / (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds ((Real.log h.relevantEigenvalue)⁻¹)) := by
  exact
    (tendsto_scaleClock_ratio_of_sublinear_criticalDistanceScaleClock
      Ising3DModel h.clock h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hcal.δ
  δ_pos := hcal.δ_pos
  δ_le_betaC := hcal.δ_le_betaC
  scaleBase := hcal.scaleBase
  scaleBase_gt_one := hcal.scaleBase_gt_one
  relevantEigenvalue := hcal.relevantEigenvalue
  relevantEigenvalue_gt_one := hcal.relevantEigenvalue_gt_one
  predictedExponent_eq := hcal.predictedExponent_eq
  clock := criticalDistanceScaleClock Ising3DModel hcal.relevantEigenvalue
  clockError_negligible := by
    simp [Ising3DModel]
  logError := hcal.logError
  mass_pos := hcal.mass_pos
  logError_negligible := hcal.logError_negligible
  log_mass_scaleClock := hcal.log_mass_criticalDistanceScaleClock

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hclock.δ
  δ_pos := hclock.δ_pos
  δ_le_betaC := hclock.δ_le_betaC
  scaleBase := hclock.scaleBase
  scaleBase_gt_one := hclock.scaleBase_gt_one
  relevantEigenvalue := hclock.relevantEigenvalue
  relevantEigenvalue_gt_one := hclock.relevantEigenvalue_gt_one
  predictedExponent_eq := hclock.predictedExponent_eq
  clock := hclock.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_scaleClock_ratio
        Ising3DModel hclock.clock hclock.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hclock.clock_ratio_tendsto))
  logError := hclock.logError
  mass_pos := hclock.mass_pos
  logError_negligible := hclock.logError_negligible
  log_mass_scaleClock := hclock.log_mass_scaleClock

set_option linter.style.longLine false in




noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hann.δ
  δ_pos := hann.δ_pos
  δ_le_betaC := hann.δ_le_betaC
  scaleBase := hann.scaleBase
  scaleBase_gt_one := hann.scaleBase_gt_one
  relevantEigenvalue := hann.relevantEigenvalue
  relevantEigenvalue_gt_one := hann.relevantEigenvalue_gt_one
  predictedExponent_eq := hann.predictedExponent_eq
  clock := hann.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hann.clock hann.relevantEigenvalue hann.cLo hann.cHi
        hann.relevantEigenvalue_gt_one hann.cLo_pos hann.cHi_pos
        (by simpa [Ising3DModel] using hann.clock_annulus))
  logError := hann.logError
  mass_pos := hann.mass_pos
  logError_negligible := hann.logError_negligible
  log_mass_scaleClock := hann.log_mass_scaleClock

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass where
  δ := hcmp.δ
  δ_pos := hcmp.δ_pos
  δ_le_betaC := hcmp.δ_le_betaC
  scaleBase := hcmp.scaleBase
  scaleBase_gt_one := hcmp.scaleBase_gt_one
  relevantEigenvalue := hcmp.relevantEigenvalue
  relevantEigenvalue_gt_one := hcmp.relevantEigenvalue_gt_one
  predictedExponent_eq := hcmp.predictedExponent_eq
  clock := hcmp.clock
  logError := hcmp.logError
  mass_pos := hcmp.mass_pos
  clock_ratio_tendsto := hcmp.clock_ratio_tendsto
  logError_negligible := hcmp.logError_negligible
  log_mass_scaleClock := hcmp.log_mass_scaleClock

set_option linter.style.longLine false in







structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  terminalLog : ℝ → ℝ
  terminalLogLimit : ℝ
  terminalLog_tendsto :
    Filter.Tendsto terminalLog
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds terminalLogLimit)
  accumulatedError : ℝ → ℝ
  accumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_terminalError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  clockError_negligible := h.clockError_negligible
  terminalLog := h.terminalLog
  terminalLogLimit := h.terminalLogLimit
  terminalLog_tendsto := h.terminalLog_tendsto
  accumulatedError := h.accumulatedError
  accumulatedError_negligible := h.accumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_terminalError := h.log_mass_terminalError

set_option linter.style.longLine false in


theorem averageAccumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / h.clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_clock_of_log_betaC_sub
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible)
      (by simpa [Ising3DModel] using h.accumulatedError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  logError := fun β => hterm.terminalLog β + hterm.accumulatedError β
  mass_pos := hterm.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogLimit
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_terminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in







structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  terminalLog : ℝ → ℝ
  terminalLogBound : ℝ
  terminalLog_eventually_abs_le :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      |terminalLog β| ≤ terminalLogBound
  accumulatedError : ℝ → ℝ
  accumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_boundedTerminalError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  clockError_negligible := h.clockError_negligible
  terminalLog := h.terminalLog
  terminalLogBound := h.terminalLogBound
  terminalLog_eventually_abs_le := h.terminalLog_eventually_abs_le
  accumulatedError := h.accumulatedError
  accumulatedError_negligible := h.accumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_boundedTerminalError := h.log_mass_boundedTerminalError

set_option linter.style.longLine false in


theorem averageAccumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / h.clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_clock_of_log_betaC_sub
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible)
      (by simpa [Ising3DModel] using h.accumulatedError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  terminalLog := hterm.terminalLog
  terminalLogBound := |hterm.terminalLogLimit| + 1
  terminalLog_eventually_abs_le := by
    exact
      eventually_abs_le_abs_limit_add_one_of_tendsto
        (by simpa [Ising3DModel] using hterm.terminalLog_tendsto)
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_boundedTerminalError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  logError := fun β => hterm.terminalLog β + hterm.accumulatedError β
  mass_pos := hterm.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub
        Ising3DModel hterm.terminalLog hterm.accumulatedError
        hterm.terminalLogBound
        (by simpa [Ising3DModel] using hterm.terminalLog_eventually_abs_le)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            hterm.terminalLog β + hterm.accumulatedError β :=
        hterm.log_mass_boundedTerminalError β hβ
      _ =
          -(Real.log hterm.scaleBase) * hterm.clock β +
            (hterm.terminalLog β + hterm.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hterm.clock hterm.relevantEigenvalue hterm.cLo
        hterm.cHi hterm.relevantEigenvalue_gt_one hterm.cLo_pos
        hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus))
  terminalLog := hterm.terminalLog
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_terminalError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel hterm.clock hterm.relevantEigenvalue hterm.cLo
        hterm.cHi hterm.relevantEigenvalue_gt_one hterm.cLo_pos
        hterm.cHi_pos
        (by simpa [Ising3DModel] using hterm.clock_annulus))
  terminalLog := hterm.terminalLog
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  accumulatedError_negligible := hterm.accumulatedError_negligible
  mass_pos := hterm.mass_pos
  log_mass_boundedTerminalError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassBoundedTerminalError_of_annulusScaleClockBoundedTerminalError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in








structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  terminalLog : ℝ → ℝ
  terminalLogBound : ℝ
  terminalLog_eventually_abs_le :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      |terminalLog β| ≤ terminalLogBound
  accumulatedError : ℝ → ℝ
  averageAccumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_averageError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  clockError_negligible := h.clockError_negligible
  terminalLog := h.terminalLog
  terminalLogBound := h.terminalLogBound
  terminalLog_eventually_abs_le := h.terminalLog_eventually_abs_le
  accumulatedError := h.accumulatedError
  averageAccumulatedError_negligible :=
    h.averageAccumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_averageError := h.log_mass_averageError

set_option linter.style.longLine false in


theorem accumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_log_betaC_sub_of_clock_average
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible)
      (by simpa [Ising3DModel] using h.averageAccumulatedError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel havg.clock havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus))
  terminalLog := havg.terminalLog
  terminalLogBound := havg.terminalLogBound
  terminalLog_eventually_abs_le := havg.terminalLog_eventually_abs_le
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_averageError := havg.log_mass_averageError

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_annulusScaleClockAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockAverageError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in






structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  terminalLog : ℝ → ℝ
  terminalLogLimit : ℝ
  terminalLog_tendsto :
    Filter.Tendsto terminalLog
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds terminalLogLimit)
  accumulatedError : ℝ → ℝ
  averageAccumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_terminalAverageError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

namespace FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  clockError_negligible := h.clockError_negligible
  terminalLog := h.terminalLog
  terminalLogLimit := h.terminalLogLimit
  terminalLog_tendsto := h.terminalLog_tendsto
  accumulatedError := h.accumulatedError
  averageAccumulatedError_negligible :=
    h.averageAccumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_terminalAverageError := h.log_mass_terminalAverageError

set_option linter.style.longLine false in


theorem accumulatedError_negligible
    {hmass : FreePositiveSubcriticalMassBridge}
    (h :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    Filter.Tendsto
      (fun β : ℝ => h.accumulatedError β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0) := by
  exact
    (tendsto_error_div_log_betaC_sub_of_clock_average
      Ising3DModel h.clock h.accumulatedError h.relevantEigenvalue_gt_one
      (by simpa [Ising3DModel] using h.clockError_negligible)
      (by simpa [Ising3DModel] using h.averageAccumulatedError_negligible))

end FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  terminalLog := hterm.terminalLog
  terminalLogLimit := hterm.terminalLogLimit
  terminalLog_tendsto := hterm.terminalLog_tendsto
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hterm.clockError_negligible)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_terminalAverageError := hterm.log_mass_terminalError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_boundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass where
  δ := hterm.δ
  δ_pos := hterm.δ_pos
  δ_le_betaC := hterm.δ_le_betaC
  scaleBase := hterm.scaleBase
  scaleBase_gt_one := hterm.scaleBase_gt_one
  relevantEigenvalue := hterm.relevantEigenvalue
  relevantEigenvalue_gt_one := hterm.relevantEigenvalue_gt_one
  predictedExponent_eq := hterm.predictedExponent_eq
  clock := hterm.clock
  clockError_negligible := hterm.clockError_negligible
  terminalLog := hterm.terminalLog
  terminalLogBound := hterm.terminalLogBound
  terminalLog_eventually_abs_le := hterm.terminalLog_eventually_abs_le
  accumulatedError := hterm.accumulatedError
  averageAccumulatedError_negligible := by
    exact
      (tendsto_error_div_clock_of_log_betaC_sub
        Ising3DModel hterm.clock hterm.accumulatedError
        hterm.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using hterm.clockError_negligible)
        (by simpa [Ising3DModel] using hterm.accumulatedError_negligible))
  mass_pos := hterm.mass_pos
  log_mass_averageError := hterm.log_mass_boundedTerminalError

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassAverageError_of_terminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassAverageError_of_boundedTerminalError
    C hmass
    (freePositiveSubcriticalMassBoundedTerminalError_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := by
    exact
      (tendsto_sublinear_criticalDistanceScaleClock_of_eventually_annulus
        Ising3DModel havg.clock havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus))
  terminalLog := havg.terminalLog
  terminalLogLimit := havg.terminalLogLimit
  terminalLog_tendsto := havg.terminalLog_tendsto
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_terminalAverageError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in



noncomputable def freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass :=
  freePositiveSubcriticalMassTerminalAverageError_of_annulusScaleClockTerminalAverageError
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClockTerminalAverageError_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := havg.clockError_negligible
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_terminal_add_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogLimit havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by simpa [Ising3DModel] using havg.terminalLog_tendsto)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_terminalAverageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassTerminalError_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogLimit := havg.terminalLogLimit
  terminalLog_tendsto := havg.terminalLog_tendsto
  accumulatedError := havg.accumulatedError
  accumulatedError_negligible := by
    exact
      (tendsto_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.accumulatedError
        havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  mass_pos := havg.mass_pos
  log_mass_terminalError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAverageError_of_terminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogBound := |havg.terminalLogLimit| + 1
  terminalLog_eventually_abs_le := by
    exact
      eventually_abs_le_abs_limit_add_one_of_tendsto
        (by simpa [Ising3DModel] using havg.terminalLog_tendsto)
  accumulatedError := havg.accumulatedError
  averageAccumulatedError_negligible :=
    havg.averageAccumulatedError_negligible
  mass_pos := havg.mass_pos
  log_mass_averageError := havg.log_mass_terminalAverageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := havg.clockError_negligible
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogBound havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by simpa [Ising3DModel] using havg.terminalLog_eventually_abs_le)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_averageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassBoundedTerminalError_of_averageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  clockError_negligible := havg.clockError_negligible
  terminalLog := havg.terminalLog
  terminalLogBound := havg.terminalLogBound
  terminalLog_eventually_abs_le := havg.terminalLog_eventually_abs_le
  accumulatedError := havg.accumulatedError
  accumulatedError_negligible := by
    exact
      (tendsto_error_div_log_betaC_sub_of_clock_average
        Ising3DModel havg.clock havg.accumulatedError
        havg.relevantEigenvalue_gt_one
        (by simpa [Ising3DModel] using havg.clockError_negligible)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  mass_pos := havg.mass_pos
  log_mass_boundedTerminalError := havg.log_mass_averageError

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassScaleClockNearCritical C hmass :=
  freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in





noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hclock.δ
  δ_pos := hclock.δ_pos
  δ_le_betaC := hclock.δ_le_betaC
  mass_pos := hclock.mass_pos
  log_mass_ratio_tendsto := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hlog :
        ∀ᶠ β in L,
          Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
            -(Real.log hclock.scaleBase) * hclock.clock β +
              hclock.logError β := by
      filter_upwards
        [Ioo_mem_nhdsLT
          (show Ising.betaC 3 - hclock.δ < Ising.betaC 3 by
            linarith [hclock.δ_pos])]
        with β hβ
      exact hclock.log_mass_scaleClock β hβ
    have hratio :=
      tendsto_log_mass_div_log_betaC_sub_of_scaleClock
        Ising3DModel
        (freeSelectedPositiveSubcriticalMass hmass)
        hclock.clock hclock.logError
        hclock.scaleBase hclock.relevantEigenvalue
        (by
          simpa [L, Ising3DModel] using hclock.clock_ratio_tendsto)
        (by
          simpa [L, Ising3DModel] using hclock.logError_negligible)
        (by
          simpa [L, Ising3DModel] using hlog)
    simpa [hclock.predictedExponent_eq] using hratio

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_annulusScaleClock
    C hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_scaleClock
    C hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_criticalDistanceClockComparison
    C hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C hmass hclock)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_annulusScaleClock
      C hmass hann)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockBoundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceScaleClock
      C hmass hcal)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree hmass
    (freePositiveSubcriticalMassScaleClock_of_criticalDistanceClockComparison
      C hmass hcmp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_terminalAverageError
      C hmass havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_boundedTerminalError
      C hmass hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree hmass
    (freePositiveSubcriticalMassCriticalDistanceClockComparison_of_averageError
      C hmass havg)

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_scaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree I.massBridge hclock

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_scaleClock C hagree hclock)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree I.massBridge hann

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_annulusScaleClock C hagree hann)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockAverageError
      C hagree havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalAverageError
      C hagree havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalError
      C hagree hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockBoundedTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockBoundedTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockBoundedTerminalError
      C hagree hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceScaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceScaleClock
    C hagree I.massBridge hcal

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceScaleClock
      C hagree hcal)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparison
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree I.massBridge hcmp

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparison
      C hagree hcmp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalError
      C hagree hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in



theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalAverageError
      C hagree havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonBoundedTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonBoundedTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonBoundedTerminalError
      C hagree hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonAverageError
      C hagree havg)

end FiniteCurrentMassBridgeInputs

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_scaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree I.massBridge hclock

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_scaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_scaleClock
      C I.massBridge hclock

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_scaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_scaleClock C hagree hclock)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree I.massBridge hann

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClock
      C I.massBridge hann

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_annulusScaleClock C hagree hann)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClockAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockAverageError
      C I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockAverageError
      C hagree havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClockTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalAverageError
      C I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalAverageError
      C hagree havg)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClockTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockTerminalError
      C I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockTerminalError
      C hagree hterm)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_annulusScaleClockBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockBoundedTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_annulusScaleClockBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_annulusScaleClockBoundedTerminalError
      C I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_annulusScaleClockBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_annulusScaleClockBoundedTerminalError
      C hagree hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceScaleClock
    C hagree I.massBridge hcal

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceScaleClock
      C I.massBridge hcal

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceScaleClock
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceScaleClock
      C hagree hcal)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparison
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree I.massBridge hcmp

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceClockComparison
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparison
      C I.massBridge hcmp

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparison
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hcmp :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparison
      C hagree hcmp)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceClockComparisonTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalError
      C I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalError
      C hagree hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceClockComparisonTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonTerminalAverageError
      C I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonTerminalAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonTerminalAverageError
      C hagree havg)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonBoundedTerminalError
    C hagree I.massBridge hterm

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceClockComparisonBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonBoundedTerminalError
      C I.massBridge hterm

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonBoundedTerminalError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonBoundedTerminalError
      C hagree hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonAverageError
    C hagree I.massBridge havg

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_criticalDistanceClockComparisonAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        I.massBridge) :
    AnalyticLogRatioBridge I C where
  plus_free_agree := hagree
  free_mass_log_ratio :=
    freePositiveSubcriticalMassLogRatioLimit_of_criticalDistanceClockComparisonAverageError
      C I.massBridge havg

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_criticalDistanceClockComparisonAverageError
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_criticalDistanceClockComparisonAverageError
      C hagree havg)

end FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassScaleClock
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hclock

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hclock :
      FreePositiveSubcriticalMassScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_scaleClock
      C hagree hlim hfixed hone hboundary hcmp hprojection hclock)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClock
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hann

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hann :
      FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClock
      C hagree hlim hfixed hone hboundary hcmp hprojection hann)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockAverageError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    havg

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockAverageError
      C hagree hlim hfixed hone hboundary hcmp hprojection havg)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalAverageError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    havg

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalAverageError
      C hagree hlim hfixed hone hboundary hcmp hprojection havg)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockTerminalError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hterm

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError
      C hagree hlim hfixed hone hboundary hcmp hprojection hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAnnulusScaleClockBoundedTerminalError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hterm

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockBoundedTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockBoundedTerminalError
      C hagree hlim hfixed hone hboundary hcmp hprojection hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceScaleClock
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hcal

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hcal :
      FreePositiveSubcriticalMassCriticalDistanceScaleClockNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceScaleClock
      C hagree hlim hfixed hone hboundary hcmp hprojection hcal)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hclock :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparison
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hclock

set_option linter.style.longLine false in





theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hclock :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparison
      C hagree hlim hfixed hone hboundary hcmp hprojection hclock)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hterm

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalError
      C hagree hlim hfixed hone hboundary hcmp hprojection hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonTerminalAverageError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    havg

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonTerminalAverageError
      C hagree hlim hfixed hone hboundary hcmp hprojection havg)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonBoundedTerminalError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hterm

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hterm :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonBoundedTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonBoundedTerminalError
      C hagree hlim hfixed hone hboundary hcmp hprojection hterm)

set_option linter.style.longLine false in



noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassCriticalDistanceClockComparisonAverageError
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    havg

set_option linter.style.longLine false in




theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (havg :
      FreePositiveSubcriticalMassCriticalDistanceClockComparisonAverageErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_criticalDistanceClockComparisonAverageError
      C hagree hlim hfixed hone hboundary hcmp hprojection havg)

end Exact3D
end StatMech
