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
    response E0 Emax K h 0 = E0 := by
  rw [response_eq]
  exact (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h) hK hh hEmax).1

/-- At `C = K` the response is half-maximal. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    response E0 Emax K h K = E0 + Emax / 2 := by
  rw [response_eq]
  exact (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h) hK hh hEmax).2.1

/-- Boundary `Emax = 0`: the response is constantly the baseline. -/
example {E0 K h : ℝ} (hK : 0 < K) (hh : 0 < h) (C : ℝ) (hC : 0 ≤ C) :
    response E0 0 K h C = E0 := by
  have hb := (pd_response_characterization (E0 := E0) (K := K) (h := h) hK hh (le_refl 0)).2.2.2.1 C hC
  rw [response_eq]
  linarith [hb.1, hb.2]

/-- High-concentration limit through `response`. -/
example {E0 Emax K h : ℝ} (hK : 0 < K) (hh : 0 < h) (hEmax : 0 ≤ Emax) :
    Tendsto (response E0 Emax K h) atTop (𝓝 (E0 + Emax)) := by
  have hlim := (pd_response_characterization (E0 := E0) (Emax := Emax) (K := K) (h := h)
    hK hh hEmax).2.2.2.2
  refine hlim.congr (fun C => ?_)
  exact (response_eq E0 Emax K h C).symm

end MathlibExtTest.Biology.Biophysics.Pharmacodynamics
