/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors

/-! Original square-root normalization as an exact rational scaled physical tensor packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- The complete original integer factor packet has the exact rational scaled coordinates. -/
theorem generatedAxisGlobalTensorFactor_rational
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (D : ℕ) :
    generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D =
      fun t j => ((((u (generatedAxisGlobalSpinLabel t) : ℚ) * (v j : ℚ)) /
        (D : ℚ) : ℚ) : ℝ) / Real.sqrt 2 := by
  funext t j
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient,
    generatedAxisGlobalSpinLabel_coeff]
  simp only [generatedAxisGlobalOddTensorFactor, Int.cast_mul,
    Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
  rw [div_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
