/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixLifts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedTensorMatrixBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorMatrixReplayGeneric

/-! A single complete circuit equation gives genuine whole integer tensor fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix

/-- The actual compatible candidate action preserves every retained integer tensor coefficient. -/
theorem generatedTwelfth_certified_tensor_integer_fix_of_circuit (g : Fin 12)
    (hcircuit : ∀ j : Fin 24,
      (generatedTwelfthSpinCompact g).val
        (nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorSpatialInteger g n j)) =
          (generatedTwelfthSpinTensorSpatialDenominator g : ℝ) •
            nortonUIntegerEmbed (fun n => generatedTwelfthSpinTensorInputInteger n j))
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedTwelfthCertifiedFiber g)
      (fun u j => (generatedTwelfthSpinTensorInputInteger (nortonUIntegerLabel u) j : ℝ)) t i =
      (generatedTwelfthSpinTensorInputInteger (nortonUIntegerLabel t) i : ℝ) := by
  have hd := generatedTwelfth_certified_denominator_ne_zero g
  have hspin (j : Fin 24) :
      (generatedTwelfthCertifiedFiber g).val.1.val
        (nortonUIntegerEmbed (fun n => ∑ k : Fin 24,
          generatedTwelfthCertifiedNumerator g j k * generatedTwelfthSpinTensorInputInteger n k)) =
        nortonUIntegerEmbed (fun n => (generatedTwelfthCertifiedDenominator g : ℤ) *
          generatedTwelfthSpinTensorInputInteger n j) := by
    change (generatedTwelfthSpinCompact g).val _ = _
    rw [← generatedTwelfth_certified_tensor_matrices]
    have h := hcircuit j
    rw [generatedTwelfth_certified_tensor_denominators] at h
    refine h.trans ?_
    ext u
    simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  have h := generatedTwelfth_tensor_matrix_column_replay (generatedTwelfthCertifiedFiber g)
    (generatedTwelfthCertifiedNumerator g) (generatedTwelfthCertifiedDenominator g) hd
    (generatedTwelfth_certified_isometry_numerator
      (generatedTwelfthCertifiedNumerator g) (generatedTwelfthCertifiedIntegral g)
      (generatedTwelfthCertifiedIntegralInverse g) (generatedTwelfthCertifiedDenominator g)
      (generatedTwelfth_certified_denominator_ne_zero g)
      (generatedTwelfth_certified_orthogonal_left g)
      (generatedTwelfth_certified_orthogonal_right g)
      (generatedTwelfth_certified_basis g) (generatedTwelfth_certified_integral_inverse g))
    generatedTwelfthSpinTensorInputInteger
    (fun n j => (generatedTwelfthCertifiedDenominator g : ℤ) *
      generatedTwelfthSpinTensorInputInteger n j) hspin t i
  rw [h]
  simp only [Int.cast_mul, Int.cast_natCast]
  have hdR : (generatedTwelfthCertifiedDenominator g : ℝ) ≠ 0 := by exact_mod_cast hd
  exact mul_div_cancel_left₀ _ hdR

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
