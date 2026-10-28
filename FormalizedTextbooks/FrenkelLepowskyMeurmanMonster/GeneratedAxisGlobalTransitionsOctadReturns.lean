/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFirstLayer

/-! Genuine inverse-triality returns of the fourth and fifth literal axis prototypes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal source code with zero label and zero phase is the actual identity. -/
theorem generatedAxisGlobal_source_zero : sourceQCode 0 0 = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change sourceExpectedCodeCoordinates (golayLabelCoefficients 0) = 0
    decide +kernel
  · apply Multiplicative.toAdd.injective
    change (0 : ZMod 2) + (golayMaskWeight (golayEncodedMask 0) / 4 : ℕ) = 0
    decide +kernel

/-- Its original triality-conjugated local sign lift is the actual local identity. -/
theorem generatedAxisGlobalSignLocal_zero : generatedFifthSignLocal 0 0 = 1 := by
  apply localIntoGenerated_injective
  rw [generatedFifth_sign_local_generated, map_one, sourceGeneratedY, sourceGeneratedCode,
    generatedAxisGlobal_source_zero, map_one]
  group

/-- All seven displayed stages of the actual Omega root are literal identity stages. -/
theorem generatedAxisGlobalFifthShort_omega_data : ∀ j : Fin 7,
    generatedAxisGlobalFifthShortNormalizationXi 11 j = false ∧
    generatedAxisGlobalFifthShortNormalizationSigns 11 j = 0 ∧
    generatedAxisGlobalFifthShortNormalizationWords 11 j = [] := by
  decide +kernel

/-- The actual local Omega root stages retain the literal identity, including source phases. -/
theorem generatedAxisGlobalFifthShort_omega_stage (j : Fin 7) :
    generatedAxisGlobalFifthShortNormalizationLocal 11 j = 1 := by
  rw [generatedAxisGlobalFifthShortNormalizationLocal,
    (generatedAxisGlobalFifthShort_omega_data j).1,
    (generatedAxisGlobalFifthShort_omega_data j).2.1,
    (generatedAxisGlobalFifthShort_omega_data j).2.2]
  simp only [Bool.false_eq_true, ↓reduceIte, generatedAxisGlobalSignLocal_zero,
    List.map_nil, List.prod_nil, map_one, one_mul]

/-- The Omega transition representative is exactly the actual local identity. -/
theorem generatedAxisGlobalFifthShort_omega_word :
    generatedAxisGlobalFifthShortLocalWord 11 = 1 := by
  unfold generatedAxisGlobalFifthShortLocalWord
  simp only [generatedAxisGlobalFifthShort_omega_stage]
  simp [generatedAxisGlobalWordChain]

/-- Removing the leading triality returns every such literal word to the true octad family. -/
theorem generatedAxisGlobal_octad_inverse_return (h : H) (o : Fin 759)
    (e : Fin 64) (c : ZMod 2) :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (sExtra (rhoLocal h
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))))) =
      generatedAxisOctadDestination := by
  change Quotient.mk (MulAction.orbitRel H GriessSpace)
    (sExtra.symm (sExtra _)) = _
  rw [LinearEquiv.symm_apply_apply]
  calc
    _ = Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)) := by
      apply (generatedAxis_local_class_eq_iff _ _).mpr
      refine ⟨h⁻¹, ?_⟩
      rw [map_inv]
      exact LinearEquiv.symm_apply_apply _ _
    _ = _ := (generatedAxis_triality_octad_class_iff _ _).mpr ⟨o, e, rfl⟩

/-- The inverse triality image of the actual fourth prototype has the true octad destination. -/
theorem generatedAxisGlobalFourth_inverse_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra⁻¹ generatedFourthAxis) =
      generatedAxisOctadDestination := by
  rw [generatedFourthAxis_local_expression]
  exact generatedAxisGlobal_octad_inverse_return _ _ _ _

/-- The inverse triality image of the actual fifth prototype has the true octad destination. -/
theorem generatedAxisGlobalFifth_inverse_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (sExtra⁻¹ generatedFifthAxis) =
      generatedAxisOctadDestination := by
  rw [generatedFifthAxis_local_expression]
  exact generatedAxisGlobal_octad_inverse_return _ _ _ _

/-- The actual fifth Omega-root inverse transition belongs to the proved first octad family. -/
theorem generatedAxisGlobalFifthShort_omega_inverse_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis)) =
      generatedAxisOctadDestination := by
  rw [generatedAxisGlobalFifthShort_omega_word, map_one]
  exact generatedAxisGlobalFifth_inverse_destination

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
