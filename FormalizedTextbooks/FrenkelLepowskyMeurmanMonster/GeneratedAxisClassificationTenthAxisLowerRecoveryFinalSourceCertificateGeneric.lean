/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateIncomingAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixLiteralActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortPackedCacheSourceGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerTensorCircuitData

/-! Ungated complete final-triality integer formulas; both incoming C and T remain present. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete C128 source formula uses actual incoming axis M32, not the physical word P. -/
def generatedTenthFinalSourceCertificateCInteger : GriessShortIndex → ℤ
  | Sum.inl (s, p) =>
      (if s = 0 then 4 else -4) * generatedTenthSourceIncomingMatrixLiteralNumerator
        (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
      4 * (generatedTenthFinalSourceCertificateIncomingC (Sum.inl (0, p)) -
        generatedTenthFinalSourceCertificateIncomingC (Sum.inl (1, p)))
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, trialityIntegerMatrix e f *
        generatedTenthFinalSourceCertificateIncomingC (Sum.inr (Sum.inl (o, f)))
  | Sum.inr (Sum.inr (d, i)) =>
      nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (generatedTenthIncomingTensorPackedCache ⟨d.val, by omega⟩ i +
          generatedTenthIncomingTensorPackedCache ⟨d.val + 2048, by omega⟩ i)

/-- The exact outgoing scale512sqrt2 numerator retains both original final-Xi source terms. -/
def generatedTenthFinalSourceCertificateTInteger (k : Fin 4096) (i : Fin 24) : ℤ :=
  let d := generatedAxisGlobalSpinLabelLow k
  let z : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
  32 * generatedAxisGlobalIntSign (golayLabelCoefficients k 11) * z *
      generatedTenthFinalSourceCertificateIncomingC (Sum.inr (Sum.inr (d, i))) +
    4 * generatedAxisGlobalIntSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * z *
      (generatedTenthIncomingTensorPackedCache ⟨d.val, by omega⟩ i -
        generatedTenthIncomingTensorPackedCache ⟨d.val + 2048, by omega⟩ i)

/-- Symbolic rational-to-integer C transport keeps the full original final triality formula. -/
theorem generatedTenth_final_source_certificate_C_rational (r : GriessShortIndex) :
    generatedTenthFinalShortSourceCalibratedFormula generatedTenthSourceIncomingMatrixLiteral
      generatedTenthIncomingTensorPackedCache r =
        (generatedTenthFinalSourceCertificateCInteger r : ℚ) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedTenthFinalShortSourceCalibratedFormula,
      generatedTenthFinalSourceCertificateCInteger, generatedTenthSourceIncomingMatrixLiteral,
      generatedTenthSourceIncomingMatrixLiteralDenominator]
    rw [generatedTenth_final_source_certificate_incoming_actual,
      generatedTenth_final_source_certificate_incoming_actual]
    push_cast
    split_ifs <;> ring
  · simp only [generatedTenthFinalShortSourceCalibratedFormula,
      generatedTenthFinalSourceCertificateCInteger, Int.cast_sum, Int.cast_mul]
    simp_rw [generatedTenth_final_source_certificate_incoming_actual]
  · simp only [generatedTenthFinalShortSourceCalibratedFormula,
      generatedTenthFinalSourceCertificateCInteger]
    push_cast
    ring

/-- Exact B64 calibration reduces final T without recomputing any original source factors. -/
theorem generatedTenth_final_source_certificate_T_rational
    (hB : GeneratedTenthFinalShortSourceTensorCalibration generatedTenthIncomingTensorPackedCache)
    (k : Fin 4096) (i : Fin 24) :
    8 * generatedTenthFinalTensorSourceQ k i =
      (generatedTenthFinalSourceCertificateTInteger k i : ℚ) := by
  unfold generatedTenthFinalTensorSourceQ generatedAxisGlobalTrialityScaledTensorQ
    generatedTenthFinalTensorSourceIncomingCQ generatedTenthFinalTensorSourceIncomingTQ
    generatedTenthFinalSourceCertificateTInteger
  simp only [generatedAxisGlobalSpinLabel_coeff, nortonUIntegerLabel_coeff]
  rw [hB, hB, generatedTenth_final_source_certificate_incoming_actual]
  push_cast
  split_ifs <;> ring

/-- Every original short address, including every zero, must equal the complete source integer. -/
def GeneratedTenthFinalSourceCertificateC (a : Fin 98280) : Prop :=
  generatedTenthFinalSourceCertificateCInteger (generatedNinthLowerSpinShortIndex a) =
    generatedTenthFinalShortPackedCacheAddressValue a

/-- Original tensor spin label recovered from the interleaved address. -/
def generatedTenthFinalSourceCertificateTensorK (a : Fin 98304) : Fin 4096 :=
  ⟨a.val / 24, by omega⟩

/-- Original physical coordinate recovered from the interleaved address. -/
def generatedTenthFinalSourceCertificateTensorI (a : Fin 98304) : Fin 24 :=
  ⟨a.val % 24, Nat.mod_lt _ (by decide)⟩

/-- The full original interleaved tensor source address is exactly 24*k+i. -/
def GeneratedTenthFinalSourceCertificateT (a : Fin 98304) : Prop :=
  generatedTenthFinalSourceCertificateTInteger
      (generatedTenthFinalSourceCertificateTensorK a)
      (generatedTenthFinalSourceCertificateTensorI a) =
    generatedTenthTwoFixerTensorInput
      (generatedTenthFinalSourceCertificateTensorK a)
      (generatedTenthFinalSourceCertificateTensorI a)

/-- Original complete short-coordinate packet address. -/
def generatedTenthFinalSourceCertificateCLabel (b : Fin 383) (u : Fin 256) : Fin 98280 :=
  ⟨256 * b.val + u.val, by omega⟩

/-- Exact final short-coordinate tail address. -/
def generatedTenthFinalSourceCertificateCTail (u : Fin 232) : Fin 98280 :=
  ⟨98048 + u.val, by omega⟩

/-- Original complete tensor-coordinate packet address. -/
def generatedTenthFinalSourceCertificateTLabel (b : Fin 384) (u : Fin 256) : Fin 98304 :=
  ⟨256 * b.val + u.val, by omega⟩

/-- Exact packets cover all 98,280 original C addresses, including the 232-address tail. -/
theorem generatedTenth_final_source_certificate_C_of_blocks
    (h : ∀ b u, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCLabel b u))
    (ht : ∀ u, GeneratedTenthFinalSourceCertificateC
      (generatedTenthFinalSourceCertificateCTail u)) :
    ∀ a, GeneratedTenthFinalSourceCertificateC a := by
  intro a
  by_cases ha : a.val < 98048
  · let b : Fin 383 := ⟨a.val / 256, by omega⟩
    let u : Fin 256 := ⟨a.val % 256, Nat.mod_lt _ (by decide)⟩
    have he : generatedTenthFinalSourceCertificateCLabel b u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceCertificateCLabel, b, u]
      omega
    simpa only [he] using h b u
  · let u : Fin 232 := ⟨a.val - 98048, by omega⟩
    have he : generatedTenthFinalSourceCertificateCTail u = a := by
      apply Fin.ext
      dsimp [generatedTenthFinalSourceCertificateCTail, u]
      omega
    simpa only [he] using ht u

/-- Complete 256-address packets cover all 98,304 original tensor addresses. -/
theorem generatedTenth_final_source_certificate_T_of_blocks
    (h : ∀ b u, GeneratedTenthFinalSourceCertificateT
      (generatedTenthFinalSourceCertificateTLabel b u)) :
    ∀ a, GeneratedTenthFinalSourceCertificateT a := by
  intro a
  let b : Fin 384 := ⟨a.val / 256, by omega⟩
  let u : Fin 256 := ⟨a.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthFinalSourceCertificateTLabel b u = a := by
    apply Fin.ext
    dsimp [generatedTenthFinalSourceCertificateTLabel, b, u]
    omega
  simpa only [he] using h b u

/-- Integer C certificates discharge precisely the complete function-valued final source cache. -/
theorem generatedTenth_final_source_certificate_C_cache
    (hB : GeneratedTenthFinalShortSourceTensorCalibration generatedTenthIncomingTensorPackedCache)
    (hC : ∀ a, GeneratedTenthFinalSourceCertificateC a) :
    GeneratedTenthFinalShortFunctionCacheCondition generatedTenthSourceIncomingMatrixLiteral
      generatedTenthFinalShortPackedCacheAddressValue := by
  apply generatedTenth_final_short_function_cache_of_tensor
    generatedTenthSourceIncomingMatrixLiteral hB generatedTenthFinalShortPackedCacheAddressValue
  intro a
  rw [generatedTenth_final_source_certificate_C_rational]
  exact_mod_cast hC a

/-- Interleaved tensor certificates retain every actual original spin and physical coordinate. -/
theorem generatedTenth_final_source_certificate_T_coordinates
    (hT : ∀ a, GeneratedTenthFinalSourceCertificateT a) (k : Fin 4096) (i : Fin 24) :
    generatedTenthFinalSourceCertificateTInteger k i = generatedTenthTwoFixerTensorInput k i := by
  let a : Fin 98304 := ⟨24 * k.val + i.val, by omega⟩
  have hk : generatedTenthFinalSourceCertificateTensorK a = k := by
    apply Fin.ext
    dsimp [generatedTenthFinalSourceCertificateTensorK, a]
    omega
  have hi : generatedTenthFinalSourceCertificateTensorI a = i := by
    apply Fin.ext
    dsimp [generatedTenthFinalSourceCertificateTensorI, a]
    omega
  simpa only [GeneratedTenthFinalSourceCertificateT, hk, hi] using hT a

/-- Full final T certificates discharge exactly the unchanged scale512sqrt2 input condition. -/
theorem generatedTenth_final_source_certificate_T_input
    (hB : GeneratedTenthFinalShortSourceTensorCalibration generatedTenthIncomingTensorPackedCache)
    (hT : ∀ a, GeneratedTenthFinalSourceCertificateT a) :
    GeneratedTenthTwoFixerTensorInputCondition := by
  intro k i
  rw [generatedTenth_final_source_certificate_T_rational hB]
  exact_mod_cast generatedTenth_final_source_certificate_T_coordinates hT k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
