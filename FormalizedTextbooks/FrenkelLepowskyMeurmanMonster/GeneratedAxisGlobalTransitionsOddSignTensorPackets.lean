/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorSignFactors

/-! Complete original low-code sign actions on the physical factor packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every physical tensor coordinate of an arbitrary original low-code sign is exact. -/
theorem generatedAxisGlobalOddSignTensorFactor_actual (a : Fin 2048)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0)
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddSignSpinInteger a u)
          (generatedAxisGlobalOddSignSpatialInteger a v)) (2 * D) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  have h := generatedAxisGlobalSignIntegerAction_coefficient
    (generatedAxisGlobalOddTensorFactor u v) D (generatedAxisGlobalSignLowCode a) 0 k i
  rw [generatedAxisGlobalOddSignInteger_factor] at h
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  linear_combination h / 2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
