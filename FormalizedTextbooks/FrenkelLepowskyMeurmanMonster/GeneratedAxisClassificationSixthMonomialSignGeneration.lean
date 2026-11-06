/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignBasis

/-! The ten original sign words generate every actual equal-sign Golay isometry. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original Golay codeword encoded by an actual equal-sign coefficient vector. -/
def generatedSixthSignCoefficientCode (t : generatedSixthSignCoefficientSpace) : golayCode :=
  golayEncoder.rangeRestrict t.val

/-- Every equal-sign codeword is a binary sum of the ten original source basis codes. -/
theorem generatedSixth_sign_code_reconstruct (t : generatedSixthSignCoefficientSpace) :
    generatedSixthSignCoefficientCode t =
      ∑ j : Fin 10, (generatedSixthSignBasisLeftInverse *ᵥ t.val) j •
        sourceGeneratedSignCode (generatedSixthMonomialSignCode j) := by
  have h := congrArg golayEncoder.rangeRestrict (generatedSixth_sign_basis_reconstruct t)
  rw [Matrix.mulVec_eq_sum] at h
  simp only [op_smul_eq_smul, map_sum, map_smul] at h
  change (∑ j : Fin 10, (generatedSixthSignBasisLeftInverse *ᵥ t.val) j •
    sourceGeneratedSignCode (generatedSixthMonomialSignCode j)) =
      generatedSixthSignCoefficientCode t at h
  exact h.symm

private theorem binary_value : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel

/-- Containing the ten genuine source signs forces containment of every equal-sign code isometry. -/
theorem generatedSixth_sign_isometry_mem_of_generators (K : Subgroup leechIsomSubgroup)
    (hK : ∀ j : Fin 10,
      golaySignIsometry (sourceGeneratedSignCode (generatedSixthMonomialSignCode j)) ∈ K)
    (t : generatedSixthSignCoefficientSpace) :
    golaySignIsometry (generatedSixthSignCoefficientCode t) ∈ K := by
  classical
  change golaySignHom (Multiplicative.ofAdd (generatedSixthSignCoefficientCode t)) ∈ K
  rw [generatedSixth_sign_code_reconstruct, ← List.sum_ofFn, ofAdd_list_prod,
    map_list_prod, List.map_map, List.map_ofFn]
  apply K.list_prod_mem
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  dsimp only [Function.comp_apply]
  rcases binary_value ((generatedSixthSignBasisLeftInverse *ᵥ t.val) j) with h | h
  · rw [h, zero_smul]
    change golaySignHom 1 ∈ K
    rw [map_one]
    exact K.one_mem
  · rw [h, one_smul]
    exact hK j

/-- The criterion uses precisely the original coordinate-sign conditions for any source word. -/
theorem generatedSixth_source_sign_mem_of_generators (K : Subgroup leechIsomSubgroup)
    (hK : ∀ j : Fin 10,
      golaySignIsometry (sourceGeneratedSignCode (generatedSixthMonomialSignCode j)) ∈ K)
    (d : Fin 4096)
    (h17 : golayEncoder (golayLabelCoefficients d) 17 =
      golayEncoder (golayLabelCoefficients d) 16)
    (h19 : golayEncoder (golayLabelCoefficients d) 19 =
      golayEncoder (golayLabelCoefficients d) 16) :
    golaySignIsometry (sourceGeneratedSignCode d) ∈ K := by
  let t : generatedSixthSignCoefficientSpace :=
    ⟨golayLabelCoefficients d, (generatedSixth_sign_coefficient_mem _).mpr ⟨h17, h19⟩⟩
  exact generatedSixth_sign_isometry_mem_of_generators K hK t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
