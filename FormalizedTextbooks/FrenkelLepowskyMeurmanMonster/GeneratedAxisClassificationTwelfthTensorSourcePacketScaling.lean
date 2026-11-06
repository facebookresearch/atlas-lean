/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages

/-! Exact common-factor cancellation for complete original tensor packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Cancelling a nonzero spin factor retains every complete physical tensor coordinate. -/
theorem generatedTwelfth_tensor_source_packet_spin_scale (c : ℕ) (hc : c ≠ 0)
    (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (D : ℕ) :
    generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (fun a => (c : ℤ) * u a) v) (c * D) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D := by
  funext t i
  have hr : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only [generatedAxisGlobalTensorIntegerPacket, generatedAxisGlobalOddTensorFactor,
    Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  simpa only [mul_assoc] using mul_div_mul_left
    ((u (generatedAxisGlobalSpinLabel t) : ℝ) * (v i : ℝ))
    ((D : ℝ) * Real.sqrt 2) hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
