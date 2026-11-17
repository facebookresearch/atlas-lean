/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.IncidenceObservation.Law

/-! Tests for the reporting-law fixtures. -/

namespace MathlibExtTest.Biology.Epidemiology.IncidenceObservation.Law

open MathlibExt.Biology.Epidemiology.IncidenceObservation.Law
open scoped NNReal

/-- Background-only at `rho = 0`. -/
example {S I : ℝ → ℝ} :
    (0 : ℝ) * (∫ t in (0:ℝ)..2, 3 * S t * I t / 100) + (1/10) * (2 - 0) =
      (1/10) * (2 - 0) :=
  epi_intensity_background_only

/-- Same intensity, same law: two model intensities that agree
(here both `background * width = 0.1 * 2`) give the same law under
any law constructor `L`. -/
example (L : ℝ → MeasureTheory.Measure ℕ) :
    L ((0:ℝ) * 5 + (1/10) * (2 - 0)) = L ((0:ℝ) * 7 + (1/10) * (2 - 0)) := by
  norm_num
/-- The zero-reporting estimand is not identified. -/
example :
    ¬ MathlibExt.Probability.Statistics.IsIdentifiedBy
      (fun incidence : Fin 2 → ℝ≥0 =>
        reportingLaw (intensityAt 0 (fun _ => 1) incidence))
      (fun incidence : Fin 2 → ℝ≥0 => (incidence 0 : ℝ)) :=
  epi_nonidentified_at_zero_reporting (fun _ => 1)

end MathlibExtTest.Biology.Epidemiology.IncidenceObservation.Law
