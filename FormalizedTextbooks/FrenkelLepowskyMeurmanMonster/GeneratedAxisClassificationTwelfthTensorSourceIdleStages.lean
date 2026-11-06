/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadReturns

/-! All four remaining original root-nine source stages fix the entire tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The four later original source slots have genuinely empty words and zero source signs. -/
theorem generatedTwelfth_tensor_source_idle_data : ∀ j : Fin 4,
    generatedAxisGlobalFifthShortNormalizationXi 9 ⟨j.val + 3, by omega⟩ = false ∧
    generatedAxisGlobalFifthShortNormalizationSigns 9 ⟨j.val + 3, by omega⟩ = 0 ∧
    generatedAxisGlobalFifthShortNormalizationWords 9 ⟨j.val + 3, by omega⟩ = [] := by
  decide +kernel

/-- Every later actual local source stage is exactly the local identity. -/
theorem generatedTwelfth_tensor_source_idle_local (j : Fin 4) :
    generatedAxisGlobalFifthShortNormalizationLocal 9 ⟨j.val + 3, by omega⟩ = 1 := by
  obtain ⟨hx, hs, hw⟩ := generatedTwelfth_tensor_source_idle_data j
  simp only [generatedAxisGlobalFifthShortNormalizationLocal, hx, hs, hw,
    Bool.false_eq_true, ↓reduceIte, List.map_nil, List.prod_nil, map_one,
    generatedAxisGlobalSignLocal_zero, mul_one]

/-- Their chosen genuine fibers are diagonal, so all original tensor coordinates are fixed. -/
theorem generatedTwelfth_tensor_source_idle_tensor (j : Fin 4) :
    localTensorRepresentation
      (generatedAxisGlobalFifthShortNormalizationFiber 9 ⟨j.val + 3, by omega⟩) = 1 := by
  have hh : localFiberIntoH
      (generatedAxisGlobalFifthShortNormalizationFiber 9 ⟨j.val + 3, by omega⟩) = 1 := by
    rw [generatedAxisGlobalFifthShortNormalizationFiber_local,
      generatedTwelfth_tensor_source_idle_local]
  exact localTensorRepresentation_diagonal _ ((QuotientGroup.eq_one_iff _).mp hh)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
