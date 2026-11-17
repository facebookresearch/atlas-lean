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

/-- The reporting law determines its intensity vector. -/
example {lam lam' : Fin 2 → ℝ≥0}
    (h : reportingLaw lam = reportingLaw lam') : lam = lam' :=
  reportingLaw_injective h

/-- The zero-reporting estimand is not identified. -/
example :
    ¬ MathlibExt.Probability.Statistics.IsIdentifiedBy
      (fun incidence : Fin 2 → ℝ≥0 =>
        reportingLaw (intensityAt 0 zero_le_one (fun _ => 1) incidence))
      (fun incidence : Fin 2 → ℝ≥0 => (incidence 0 : ℝ)) :=
  epi_nonidentified_at_zero_reporting (fun _ => 1)

end MathlibExtTest.Biology.Epidemiology.IncidenceObservation.Law
