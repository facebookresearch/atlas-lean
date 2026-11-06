/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthTensorInteger
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsXiTetrad

/-! Exact finite integer packets certify the genuine real Xi action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A complete integer physical tensor packet with its true dyadic denominator. -/
def generatedAxisGlobalTensorIntegerPacket (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) :
    SpinIndex → Fin 24 → ℝ :=
  fun t i => (N (generatedAxisGlobalSpinLabel t) i : ℝ) / ((D : ℝ) * Real.sqrt 2)

/-- A displayed packet coefficient is exactly the displayed physical coordinate. -/
theorem generatedAxisGlobalTensorIntegerPacket_coefficient
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalTensorIntegerPacket N D (golayLabelCoefficients k) i =
      (N k i : ℝ) / ((D : ℝ) * Real.sqrt 2) := by
  simp only [generatedAxisGlobalTensorIntegerPacket, generatedAxisGlobalSpinLabel_coeff]

/-- The genuine fifth starting tensor is precisely the complete denominator-one integer packet. -/
theorem generatedAxisGlobalFifthTensorInteger_packet :
    (griessConwayEncode generatedFifthAxis).2.2 =
      generatedAxisGlobalTensorIntegerPacket generatedAxisGlobalFifthTensorInteger 1 := by
  rw [generatedAxisGlobalFifthTensorInteger_eq]
  unfold generatedAxisGlobalTensorIntegerPacket
  simp only [Nat.cast_one, one_mul]

/-- Executable exact numerator of the true sixty-four by four Xi coordinate formula. -/
def generatedAxisGlobalXiIntegerAction (N : Fin 4096 → Fin 24 → ℤ)
    (k : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : XiGrayIndex, ∑ b : Fin 4,
    generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a (golayLabelCoefficients k)) *
      co1XiNumerator i (generatedAxisGlobalXiColumn i b) *
        N (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode a))
          (generatedAxisGlobalXiColumn i b)

/-- The integer checker numerator is exactly the actual real operator coefficient. -/
theorem generatedAxisGlobalXiIntegerAction_coefficient
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) (k : Fin 4096) (i : Fin 24) :
    16 * localTensorRepresentation xiSpinLocalFiber (generatedAxisGlobalTensorIntegerPacket N D)
      (golayLabelCoefficients k) i =
        (generatedAxisGlobalXiIntegerAction N k i : ℝ) / ((D : ℝ) * Real.sqrt 2) := by
  rw [generatedAxisGlobalXi_tensor_tetrad]
  simp only [generatedAxisGlobalTensorIntegerPacket, generatedAxisGlobalXiIntegerAction,
    Int.cast_sum, Int.cast_mul, generatedAxisGlobalIntSign_real]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Complete finite integer equalities imply the full genuine real packet transport. -/
theorem generatedAxisGlobalXi_packet_of_certificate
    (N M : Fin 4096 → Fin 24 → ℤ) (D E : ℕ) (hD : 0 < D) (hE : 0 < E)
    (hcert : ∀ k : Fin 4096, ∀ i : Fin 24,
      (E : ℤ) * generatedAxisGlobalXiIntegerAction N k i = 16 * (D : ℤ) * M k i) :
    localTensorRepresentation xiSpinLocalFiber (generatedAxisGlobalTensorIntegerPacket N D) =
      generatedAxisGlobalTensorIntegerPacket M E := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have he : (E : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
  have hc := congrArg (fun z : ℤ => (z : ℝ)) (hcert k i)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at hc
  calc
    _ = (16 * localTensorRepresentation xiSpinLocalFiber
        (generatedAxisGlobalTensorIntegerPacket N D) (golayLabelCoefficients k) i) / 16 := by
      ring
    _ = ((generatedAxisGlobalXiIntegerAction N k i : ℝ) / ((D : ℝ) * Real.sqrt 2)) / 16 := by
      rw [generatedAxisGlobalXiIntegerAction_coefficient]
    _ = ((E : ℝ) * (generatedAxisGlobalXiIntegerAction N k i : ℝ)) /
        (16 * (D : ℝ) * (E : ℝ) * Real.sqrt 2) := by
      field_simp [hd, he, hn]
    _ = _ := by
      rw [hc]
      field_simp [hd, he, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
