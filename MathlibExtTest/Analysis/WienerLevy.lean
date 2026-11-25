/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.WienerLevy

open MathlibExt.Analysis.WienerLevyWanted.Analysis.WienerLevy

-- The range is the unit circle, so the analytic domain can omit the pole it surrounds.
example {T : ℝ} [Fact (0 < T)] :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = (fourier 1 x)⁻¹) ∧ InWienerAlgebra g := by
  apply wiener_levy_analytic_calculus (fourier 1) (fun z => z⁻¹) ({0}ᶜ : Set ℂ)
  · change Summable (fourierCoeff (fourier 1 : C(AddCircle T, ℂ)))
    rw [fourierCoeff_fourier]
    exact (hasSum_ite_eq (1 : ℤ) (1 : ℂ)).summable.congr (fun n => by
      simp [Pi.single_apply])
  · exact isClosed_singleton.isOpen_compl
  · rintro _ ⟨x, rfl⟩
    rw [fourier_apply]
    exact Circle.coe_ne_zero _
  · intro z hz
    exact analyticAt_id.inv hz
