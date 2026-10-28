/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawInverse

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative

/-! The twelfth normalization root uses the exact identity local word on the entire Griess space. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fifth_root11_sign_zero : generatedFifthSignLocal 0 0 = 1 := by
  apply localIntoGenerated_injective
  rw [generatedFifth_sign_local_generated, map_one]
  have hc : sourceQCode 0 0 = 1 := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply Multiplicative.toAdd.injective
      funext i
      have hb : ∀ i : Fin 24, Multiplicative.toAdd (sourceQCode 0 0).base i = 0 := by
        decide +kernel
      exact hb i
    · apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (sourceQCode 0 0).coeff = 0
      decide +kernel
  simp only [sourceGeneratedY, sourceGeneratedCode, hc, map_one, mul_one, inv_mul_cancel]

private theorem fifth_root11_stage (j : Fin 7) :
    generatedAxisGlobalFifthShortNormalizationLocal 11 j = 1 := by
  have hx : ∀ j : Fin 7, generatedAxisGlobalFifthShortNormalizationXi 11 j = false := by
    decide +kernel
  have hs : ∀ j : Fin 7, generatedAxisGlobalFifthShortNormalizationSigns 11 j = 0 := by
    decide +kernel
  have hw : ∀ j : Fin 7, generatedAxisGlobalFifthShortNormalizationWords 11 j = [] := by
    decide +kernel
  simp [generatedAxisGlobalFifthShortNormalizationLocal, hx, hs, hw, fifth_root11_sign_zero]

/-- The actual chronological normalization word for root11 is precisely the identity in H. -/
theorem generatedAxisGlobalFifthRoot11_localWord :
    generatedAxisGlobalFifthShortLocalWord 11 = 1 := by
  unfold generatedAxisGlobalFifthShortLocalWord
  have hc : ∀ n, generatedAxisGlobalWordChain (fun j =>
      generatedAxisGlobalFifthShortNormalizationLocal 11
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [generatedAxisGlobalWordChain, fifth_root11_stage, ih, one_mul]
  exact hc 7

/-- The complete real packet at root11 is the original fifth axis, on all three constituents. -/
theorem generatedAxisGlobalFifthRoot11_packet :
    griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) =
      griessConwayEncode generatedFifthAxis := by
  rw [generatedAxisGlobalFifthRoot11_localWord, map_one]
  rfl

/-- The forward root11 transition is the exact original source triality formula on the full axis. -/
theorem generatedAxisGlobalFifthRoot11_triality_positive :
    griessConwayEncode
      (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis)) =
      generatedAxisGlobalRawTrialityFormula (griessConwayEncode generatedFifthAxis) := by
  rw [generatedAxisGlobalFifthRoot11_localWord, map_one]
  exact generatedAxisGlobalRawTrialityFormula_actual _

/-- The inverse root11 transition is the exact original inverse source formula on the full axis. -/
theorem generatedAxisGlobalFifthRoot11_triality_negative :
    griessConwayEncode
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis)) =
      generatedAxisGlobalRawInverseFormula (griessConwayEncode generatedFifthAxis) := by
  rw [generatedAxisGlobalFifthRoot11_localWord, map_one]
  exact generatedAxisGlobalRawInverseFormula_actual _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
