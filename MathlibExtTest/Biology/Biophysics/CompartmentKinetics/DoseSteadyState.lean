/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseSteadyState

/-! Tests: steady-state limits at `q = 1/2`, `D = 3`. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseSteadyState

open MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseSteadyState
open Filter Topology

/-- Peak tends to `3 / (1 - 1/2) = 6`. -/
example : Filter.Tendsto
    (fun n : ℕ => (1/2:ℝ)^n * 5 + 3 * ∑ j ∈ Finset.range n, (1/2:ℝ)^j)
    Filter.atTop (𝓝 (3 / (1 - 1/2))) :=
  post_dose_tendsto (by norm_num) (by norm_num)

/-- Boundary `q = 0`: peak tends to `D = 3`. -/
example : Filter.Tendsto
    (fun n : ℕ => (0:ℝ)^n * 5 + 3 * ∑ j ∈ Finset.range n, (0:ℝ)^j)
    Filter.atTop (𝓝 (3 / (1 - 0))) :=
  post_dose_tendsto (by norm_num) (by norm_num)

/-- Trough tends to `(1/2) * 6 = 3` in closed form. -/
example : Filter.Tendsto
    (fun n : ℕ => (1/2:ℝ) * ((1/2:ℝ)^n * 5 + 3 * ∑ j ∈ Finset.range n, (1/2:ℝ)^j))
    Filter.atTop (𝓝 ((1/2) * 3 / (1 - 1/2))) :=
  trough_tendsto (by norm_num) (by norm_num)

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseSteadyState
