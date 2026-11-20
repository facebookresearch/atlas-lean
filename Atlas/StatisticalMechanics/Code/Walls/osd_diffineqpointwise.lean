/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Code.OSSS.SharpnessFK

namespace StatMech.Walls
















theorem osd_diff_ineq_pointwise (n : ℕ) (c₀ cR D θ θ' S : ℝ)
    (hD : 0 < D)
    (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
    (hRusso : cR * S ≤ θ')
    (hcR : 0 ≤ cR) :
    (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' :=
  StatMech.OSSS.SharpnessFK.differential_inequality n c₀ cR D θ θ' S hD hcov hRusso hcR







theorem osd_diff_ineq_pointwise_eq_dep :
    @osd_diff_ineq_pointwise
      = @StatMech.OSSS.SharpnessFK.differential_inequality :=
  rfl









theorem osd_diff_ineq_pointwise_direct (n : ℕ) (c₀ cR D θ θ' S : ℝ)
    (hD : 0 < D)
    (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
    (hRusso : cR * S ≤ θ')
    (hcR : 0 ≤ cR) :
    (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
  
  have hSlb : (n : ℝ) * c₀ * (θ * (1 - θ)) / D ≤ S := by
    rw [div_le_iff₀ hD]; linarith [hcov]
  
  have hmul : cR * ((n : ℝ) * c₀ * (θ * (1 - θ)) / D) ≤ cR * S :=
    mul_le_mul_of_nonneg_left hSlb hcR
  
  calc (n : ℝ) * c₀ * cR / D * (θ * (1 - θ))
      = cR * ((n : ℝ) * c₀ * (θ * (1 - θ)) / D) := by ring
    _ ≤ cR * S := hmul
    _ ≤ θ' := hRusso

end StatMech.Walls
