/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseBudget

/-! Tests: one dose of `5` at time `1`, no elimination. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseBudget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseBudget intervalIntegral

/-- One included dose contributes `5` by `T = 2`. -/
example :
    (fun t : ℝ => (0:ℝ) +
      (∑ i ∈ Finset.range 1, if (fun _ : ℕ => (1:ℝ)) i ≤ t then (fun _ : ℕ => (5:ℝ)) i else 0)) 2 -
    (fun t : ℝ => (0:ℝ) +
      (∑ i ∈ Finset.range 1, if (fun _ : ℕ => (1:ℝ)) i ≤ t then (fun _ : ℕ => (5:ℝ)) i else 0)) 0 = 5 := by
  have h := dose_budget_from_integral_equation
    (A := fun t : ℝ => (0:ℝ) +
      (∑ i ∈ Finset.range 1, if (fun _ : ℕ => (1:ℝ)) i ≤ t then (fun _ : ℕ => (5:ℝ)) i else 0))
    (A0 := (0:ℝ)) (k := (0:ℝ)) (T := (2:ℝ))
    (m := 1) (fun _ : ℕ => (1:ℝ)) (fun _ : ℕ => (5:ℝ))
    (by intro i hi; simp [Finset.mem_range] at hi; subst hi; norm_num)
    (fun _ => by simp)
  simpa using h

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.DoseBudget
