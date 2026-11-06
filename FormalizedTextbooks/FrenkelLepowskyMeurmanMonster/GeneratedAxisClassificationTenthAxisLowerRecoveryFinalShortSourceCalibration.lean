/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceCache

/-! Ungated optional bounded tensor-cache interface. Its exact source calibration stays explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Optional incoming integer tensor at denominator64, bound to all actual eight source factors. -/
def GeneratedTenthFinalShortSourceTensorCalibration (B : Fin 4096 → Fin 24 → ℤ) : Prop :=
  ∀ k i, generatedTenthFinalShortSourceTensorQ k i = (B k i : ℚ) / 64

/-- Exact final formula with a calibrated incoming tensor; the matrix remains rational. -/
def generatedTenthFinalShortSourceCalibratedFormula
    (M : Matrix (Fin 24) (Fin 24) ℚ) (B : Fin 4096 → Fin 24 → ℤ) :
    GriessShortIndex → ℚ
  | Sum.inl (s, p) =>
      (if s = 0 then 128 else -128) *
        M (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
      4 * ((generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient (Sum.inl (0, p)) : ℚ) -
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient (Sum.inl (1, p)) : ℚ))
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) *
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
          (Sum.inr (Sum.inl (o, f))) : ℚ)
  | Sum.inr (Sum.inr (d, i)) =>
      (nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
        ((B ⟨d.val, by omega⟩ i : ℚ) + (B ⟨d.val + 2048, by omega⟩ i : ℚ))

/-- Exact calibration permits bounded tensor lookup while preserving every source equality. -/
theorem generatedTenth_final_short_source_calibrated_formula
    (M : Matrix (Fin 24) (Fin 24) ℚ) (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthFinalShortSourceTensorCalibration B) (r : GriessShortIndex) :
    generatedTenthFinalShortSourceFormula M r =
      generatedTenthFinalShortSourceCalibratedFormula M B r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · rfl
  · simp only [generatedTenthFinalShortSourceFormula,
      generatedTenthFinalShortSourceGenericFormula, generatedTenthFinalShortSourceCalibratedFormula]
    rw [hB, hB]
    ring

/-- Explicit calibrated formula checks imply the entire rational-to-integer cache certificate. -/
theorem generatedTenth_final_short_source_cache_of_calibrated
    (M : Matrix (Fin 24) (Fin 24) ℚ) (B : Fin 4096 → Fin 24 → ℤ)
    (hB : GeneratedTenthFinalShortSourceTensorCalibration B)
    (cache : Array ℤ) (hlen : cache.size = 98280)
    (hvalues : ∀ a : Fin 98280,
      generatedTenthFinalShortSourceCalibratedFormula M B (generatedNinthLowerSpinShortIndex a) =
        (cache[a.val]?.getD 0 : ℚ)) :
    GeneratedTenthFinalShortSourceCacheCertificate M cache := by
  refine ⟨hlen, ?_⟩
  intro a
  rw [generatedTenth_final_short_source_calibrated_formula M B hB]
  exact hvalues a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
