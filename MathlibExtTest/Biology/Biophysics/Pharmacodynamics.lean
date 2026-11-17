/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.Pharmacodynamics

/-! Tests for the normalized pharmacodynamic response, through the
`response` definition as an importing client. -/

namespace MathlibExtTest.Biology.Biophysics.Pharmacodynamics

open MathlibExt.Biology.Biophysics.Pharmacodynamics Filter Topology

/-- At zero concentration the response is the baseline. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    response E0 Emax K h 0 = E0 :=
  response_at_zero hK hh hEmax

/-- At `C = K` the response is half the maximal increment above baseline. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    response E0 Emax K h K = E0 + Emax / 2 :=
  response_at_half hK hh hEmax

/-- Boundary `Emax = 0`: the response is constantly the baseline. -/
example {E0 K h : ℝ} (hK : 0 < K) (hh : 0 < h) (C : ℝ) (hC : 0 ≤ C) :
    response E0 0 K h C = E0 := by
  have hb := response_bounds (E0 := E0) hK hh (le_refl 0) C hC
  linarith [hb.1, hb.2]

/-- High-concentration limit through `response`. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    Tendsto (response E0 Emax K h) atTop (𝓝 (E0 + Emax)) :=
  response_tendsto hK hh hEmax

/-- Monotonicity through `response`, including the zero boundary. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    MonotoneOn (response E0 Emax K h) (Set.Ici 0) :=
  response_monotoneOn hK hh hEmax

/-- Pointwise bounds through `response` at zero concentration. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    E0 ≤ response E0 Emax K h 0 ∧ response E0 Emax K h 0 ≤ E0 + Emax :=
  response_bounds hK hh hEmax 0 (le_refl 0)

/-- Strict monotonicity through `response` for positive increment. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 < Emax) :
    StrictMonoOn (response E0 Emax K h) (Set.Ici 0) :=
  response_strictMonoOn hK hh hEmax

end MathlibExtTest.Biology.Biophysics.Pharmacodynamics
