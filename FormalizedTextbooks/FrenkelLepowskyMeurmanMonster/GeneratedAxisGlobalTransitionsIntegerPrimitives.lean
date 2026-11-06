/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignInteger

/-! Complete actual integer packets for the two nonmonomial source primitives. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine source sign transports the whole physical tensor with its exact factor two. -/
theorem generatedAxisGlobalSignInteger_packet
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) (a : Fin 4096) (ε : ZMod 2) :
    localTensorRepresentation (generatedFifthSignFiber a ε)
      (generatedAxisGlobalTensorIntegerPacket N D) =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalSignIntegerAction N a ε)
          (2 * D) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = (2 * localTensorRepresentation (generatedFifthSignFiber a ε)
        (generatedAxisGlobalTensorIntegerPacket N D) (golayLabelCoefficients k) i) / 2 := by
      ring
    _ = ((generatedAxisGlobalSignIntegerAction N a ε k i : ℝ) /
        ((D : ℝ) * Real.sqrt 2)) / 2 := by
      rw [generatedAxisGlobalSignIntegerAction_coefficient]
    _ = _ := by
      rw [div_div]
      congr 1
      ring

/-- The genuine Xi transports every physical tensor coordinate with its exact factor sixteen. -/
theorem generatedAxisGlobalXiInteger_packet
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation xiSpinLocalFiber (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalXiIntegerAction N) (16 * D) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = (16 * localTensorRepresentation xiSpinLocalFiber
        (generatedAxisGlobalTensorIntegerPacket N D) (golayLabelCoefficients k) i) / 16 := by
      ring
    _ = ((generatedAxisGlobalXiIntegerAction N k i : ℝ) /
        ((D : ℝ) * Real.sqrt 2)) / 16 := by
      rw [generatedAxisGlobalXiIntegerAction_coefficient]
    _ = _ := by
      rw [div_div]
      congr 1
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
