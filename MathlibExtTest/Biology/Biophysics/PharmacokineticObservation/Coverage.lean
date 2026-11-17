/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.PharmacokineticObservation.Coverage

/-! Tests: coverage transfer on a one-point space. -/

namespace MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.Coverage

open MathlibExt.Biology.Biophysics.PharmacokineticObservation.Coverage

/-- Dirac law, everything covered: the transferred bound is `1`. -/
example : 1 - (0:ℝ) ≤ (MeasureTheory.Measure.dirac ((): Unit)).real
    {ω | (fun z : ℝ => z + 1) ((fun _ => (0:ℝ)) ω) ∈ (fun _ => Set.univ) ω} :=
  coverage_transfer_image (MeasureTheory.Measure.dirac ())
    (fun _ => Set.univ) (fun _ => Set.univ) (fun _ => 0)
    (fun z : ℝ => z + 1) 0 (fun _ _ => Set.mem_univ _) (by simp)

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.Coverage
