/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedTensorCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorSpinAction

/-! Actual full-coordinate tensor fixation retains the genuine central source ambiguity.
The actual tensor binding and complete short fixation must both be proved before whole-axis attainment. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- An actual coefficient binding identifies the entire tensor fixed by the genuine reduced models. -/
theorem generatedRootEight_mathieu_reduced_tensor_fixation_of_binding (j : Fin 2)
    (hT : ∀ t : SpinIndex, ∀ i : Fin 24,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (8192 * Real.sqrt 2)) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedRootEightMathieuReducedTensorFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i := by
  rw [generatedRootEight_mathieu_reduced_tensor_coordinate j
    (generatedRootEight_mathieu_reduced_tensor_coordinate_certificate j)]
  rw [generatedRootEight_canonical_tensor_cache_of_integer_binding hT,
    generatedRootEight_canonical_tensor_cache_of_integer_binding hT, nortonUIntegerLabel_coeff]
  have hc := generatedRootEight_mathieu_reduced_tensor_cache_fixation j (nortonUIntegerLabel t) i
  unfold generatedRootEightMathieuReducedTensorCachedFixCondition at hc
  have hr := congrArg (fun z : ℤ => (z : ℝ) / (8192 * Real.sqrt 2)) hc
  simpa only [Int.cast_mul, mul_div_assoc] using hr

/-- Entire actual matrix and short fixation transfer to the full-Q-equivalent rank-zero model. -/
theorem generatedRootEight_mathieu_reduced_tensor_matrix_short_fixation (j : Fin 2)
    (hC : generatedRootEightMathieuReducedShortCondition j) :
    localMatrixRepresentation (generatedRootEightMathieuReducedTensorFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 ∧
    localShortRepresentation (generatedRootEightMathieuReducedTensorFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 := by
  rcases generatedRootEight_mathieu_reduced_tensor_matrix_short j
    generatedRootEightCanonicalPositiveAxis with ⟨hm, hs⟩
  change (griessConwayEncode (localGriessRepresentation (generatedRootEightMathieuReducedTensorFiber j)
    generatedRootEightCanonicalPositiveAxis)).1 =
    (griessConwayEncode (localGriessRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      generatedRootEightCanonicalPositiveAxis)).1 at hm
  change (griessConwayEncode (localGriessRepresentation (generatedRootEightMathieuReducedTensorFiber j)
    generatedRootEightCanonicalPositiveAxis)).2.1 =
    (griessConwayEncode (localGriessRepresentation (generatedRootEightMathieuReducedCertifiedFiber j)
      generatedRootEightCanonicalPositiveAxis)).2.1 at hs
  rw [localGriessRepresentation_encode, localGriessRepresentation_encode,
    localConwayRawRepresentation_apply, localConwayRawRepresentation_apply] at hm hs
  exact ⟨hm.trans (generatedRootEight_mathieu_reduced_certified_matrix j), hs.trans (funext hC)⟩

/-- Whole actual-axis fixation follows from the proved complete tensor binding and full short action. -/
theorem generatedRootEight_mathieu_reduced_tensor_axis_of_binding (j : Fin 2)
    (hT : ∀ t : SpinIndex, ∀ i : Fin 24,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (8192 * Real.sqrt 2))
    (hC : generatedRootEightMathieuReducedShortCondition j) :
    rhoLocal (generatedRootEightMathieuReducedTensorLocal j)
      generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  change localGriessRepresentation (generatedRootEightMathieuReducedTensorFiber j)
    generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis
  rcases generatedRootEight_mathieu_reduced_tensor_matrix_short_fixation j hC with ⟨hm, hs⟩
  have ht := funext fun t => funext (generatedRootEight_mathieu_reduced_tensor_fixation_of_binding j hT t)
  have he : griessConwayEncode
      (localGriessRepresentation (generatedRootEightMathieuReducedTensorFiber j)
        generatedRootEightCanonicalPositiveAxis) =
      griessConwayEncode generatedRootEightCanonicalPositiveAxis := by
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change (localMatrixRepresentation (generatedRootEightMathieuReducedTensorFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1,
        (localShortRepresentation (generatedRootEightMathieuReducedTensorFiber j)
          (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1,
          localTensorRepresentation (generatedRootEightMathieuReducedTensorFiber j)
            (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2)) = _
    rw [hm, hs, ht]
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode] using hd

/-- The attained source fixer has a genuine explicitly allowed central Q phase, with no scalar assumption. -/
theorem generatedRootEight_mathieu_reduced_tensor_source_fixer_of_binding (j : Fin 2)
    (hT : ∀ t : SpinIndex, ∀ i : Fin 24,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (generatedRootEightCanonicalPositiveTensorNumerator (nortonUIntegerLabel t) i : ℝ) /
          (8192 * Real.sqrt 2))
    (hC : generatedRootEightMathieuReducedShortCondition j) :
    ∃ c : ZMod 2, rhoLocal (inclQ (qCentral c) * generatedRootEightMathieuReducedCertifiedLocal j)
      generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis := by
  have hf := generatedRootEight_mathieu_reduced_tensor_axis_of_binding j hT hC
  rcases generatedRootEight_mathieu_reduced_tensor_central_difference j with he | he
  · refine ⟨0, ?_⟩
    rw [show qCentral 0 = 1 from rfl, map_one, one_mul, he]
    exact hf
  · refine ⟨1, ?_⟩
    rw [show qCentral 1 = qCentralInvolution from rfl, he, ← mul_assoc, ← map_mul,
      show qCentralInvolution * qCentralInvolution = 1 from by decide +kernel,
      map_one, one_mul]
    exact hf


/-- Every actual tensor coordinate is fixed unconditionally by each genuine rank-zero reduced model. -/
theorem generatedRootEight_mathieu_reduced_tensor_fixation (j : Fin 2) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedRootEightMathieuReducedTensorFiber j)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i :=
  generatedRootEight_mathieu_reduced_tensor_fixation_of_binding j
    generatedRootEight_canonical_positive_tensor_integer t i

/-- Complete actual short fixation supplies an actual source fixer with a genuine central Q correction. -/
theorem generatedRootEight_mathieu_reduced_tensor_source_fixer_of_short (j : Fin 2)
    (hC : generatedRootEightMathieuReducedShortCondition j) :
    ∃ c : ZMod 2, rhoLocal (inclQ (qCentral c) * generatedRootEightMathieuReducedCertifiedLocal j)
      generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis :=
  generatedRootEight_mathieu_reduced_tensor_source_fixer_of_binding j
    generatedRootEight_canonical_positive_tensor_integer hC

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
