/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors

/-! Complete actual tensor transports from exact normalized factor certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Cross multiplication of complete integer packets gives equality of every physical coordinate. -/
theorem generatedAxisGlobalOddTensorPacket_eq_of_cross
    (N M : Fin 4096 → Fin 24 → ℤ) (D E : ℕ) (hD : 0 < D) (hE : 0 < E)
    (hc : ∀ k i, (E : ℤ) * N k i = (D : ℤ) * M k i) :
    generatedAxisGlobalTensorIntegerPacket N D = generatedAxisGlobalTensorIntegerPacket M E := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  have he : (E : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient,
    generatedAxisGlobalTensorIntegerPacket_coefficient]
  apply (div_eq_div_iff (mul_ne_zero hd hn) (mul_ne_zero he hn)).2
  have h := congrArg (fun z : ℤ => (z : ℝ)) (hc k i)
  simp only [Int.cast_mul, Int.cast_natCast] at h
  calc
    (N k i : ℝ) * ((E : ℝ) * Real.sqrt 2) =
        ((E : ℝ) * (N k i : ℝ)) * Real.sqrt 2 := by ring
    _ = ((D : ℝ) * (M k i : ℝ)) * Real.sqrt 2 := by rw [h]
    _ = (M k i : ℝ) * ((D : ℝ) * Real.sqrt 2) := by ring

/-- Every original signed source denominator factor is positive. -/
theorem generatedAxisGlobalOddIntegerLetterFactor_pos (l : Fin 10) :
    0 < generatedAxisGlobalOddIntegerLetterFactor l := by
  fin_cases l <;> decide +kernel

/-- A normalized complete integer certificate proves the actual entire signed-letter transport. -/
theorem generatedAxisGlobalOddIntegerLetter_transport_of_certificate (l : Fin 10)
    (N M : Fin 4096 → Fin 24 → ℤ) (D E : ℕ) (hD : 0 < D) (hE : 0 < E)
    (hc : ∀ k i, (E : ℤ) * generatedAxisGlobalOddIntegerLetter l N k i =
      (generatedAxisGlobalOddIntegerLetterFactor l : ℤ) * (D : ℤ) * M k i) :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter l)
        (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket M E := by
  rw [generatedAxisGlobalOddIntegerLetter_packet]
  apply generatedAxisGlobalOddTensorPacket_eq_of_cross
    _ _ _ _ (Nat.mul_pos (generatedAxisGlobalOddIntegerLetterFactor_pos l) hD) hE
  intro k i
  simpa only [Nat.cast_mul, mul_assoc] using hc k i

/-- Separate complete spin and spatial certificates give the full original three-bases transport. -/
theorem generatedAxisGlobalOddXiFactor_transport
    (u U : Fin 4096 → ℤ) (v V : Fin 24 → ℤ) (Ds Dv Es Ev : ℕ)
    (hDs : 0 < Ds) (hDv : 0 < Dv) (hEs : 0 < Es) (hEv : 0 < Ev)
    (hs : ∀ k, (Es : ℤ) * generatedAxisGlobalOddXiSpinInteger u k = 8 * (Ds : ℤ) * U k)
    (hv : ∀ i, (Ev : ℤ) * generatedAxisGlobalOddXiSpatialInteger v i = 2 * (Dv : ℤ) * V i) :
    localTensorRepresentation xiSpinLocalFiber
        (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v)
          (Ds * Dv)) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor U V)
        (Es * Ev) := by
  apply generatedAxisGlobalXi_packet_of_certificate _ _ _ _
    (Nat.mul_pos hDs hDv) (Nat.mul_pos hEs hEv)
  intro k i
  rw [generatedAxisGlobalOddXiInteger_factor]
  simp only [generatedAxisGlobalOddTensorFactor, Nat.cast_mul]
  calc
    ((Es : ℤ) * (Ev : ℤ)) *
        (generatedAxisGlobalOddXiSpinInteger u k * generatedAxisGlobalOddXiSpatialInteger v i) =
      ((Es : ℤ) * generatedAxisGlobalOddXiSpinInteger u k) *
        ((Ev : ℤ) * generatedAxisGlobalOddXiSpatialInteger v i) := by ring
    _ = (8 * (Ds : ℤ) * U k) * (2 * (Dv : ℤ) * V i) := by rw [hs, hv]
    _ = 16 * ((Ds : ℤ) * (Dv : ℤ)) * (U k * V i) := by ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
