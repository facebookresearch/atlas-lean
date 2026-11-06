/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthProjection

/-! The literal original spatial word transports the eight genuine lower directions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Actual inverse Xi, original Golay permutation word and original codeword sign. -/
def generatedNinthSectionTransport : leechIsomSubgroup :=
  co1XiIsometry⁻¹ * golayPermutationIsometry generatedNinthSectionPermutation *
    golaySignIsometry generatedNinthSectionSign

private theorem xi_real_numerator : co1XiMatrix =
    (1 / 2 : ℝ) • co1XiNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change (((co1XiNumerator i j : ℚ) / 2 : ℚ) : ℝ) =
    (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
  push_cast
  ring

/-- Every transported direction is the exact actual lattice isometry image. -/
theorem generatedNinth_section_root_action (r : Fin 8) :
    generatedNinthSectionTransport.val (generatedNinthLowRootMatrix r) =
      fun i => (generatedNinthSectionRootCoordinates r i : ℝ) := by
  let u := golayIntegerPermute generatedNinthSectionPermutation.val
    (golayIntegerSign generatedNinthSectionSign.val (generatedNinthLowRootCoordinates r))
  have hm : golayRealPermute generatedNinthSectionPermutation.val
      (golayRealSign generatedNinthSectionSign.val (generatedNinthLowRootMatrix r)) =
        fun i => (u i : ℝ) := by
    ext i
    by_cases h : generatedNinthSectionSign.val
        (generatedNinthSectionPermutation.val.symm i) = 0
    · simp [u, golayRealPermute_apply, golayRealSign_apply, generatedNinthLowRootMatrix,
        golayIntegerPermute, golayIntegerSign, qSign, h]
    · simp [u, golayRealPermute_apply, golayRealSign_apply, generatedNinthLowRootMatrix,
        golayIntegerPermute, golayIntegerSign, qSign, h]
  have hi : (co1XiNumerator.map (Int.castRingHom ℝ)).transpose *ᵥ
      (fun i => (u i : ℝ)) =
        (2 : ℝ) • (fun i => (generatedNinthSectionRootCoordinates r i : ℝ)) := by
    ext i
    have hz := congrFun (generatedNinth_section_root_certificate r) i
    change 2 * generatedNinthSectionRootCoordinates r i =
      ∑ j : Fin 24, co1XiNumerator j i * u j at hz
    change (∑ j : Fin 24, (co1XiNumerator j i : ℝ) * (u j : ℝ)) =
      2 * (generatedNinthSectionRootCoordinates r i : ℝ)
    exact_mod_cast hz.symm
  change co1XiEquiv.symm (golayRealPermute generatedNinthSectionPermutation.val
    (golayRealSign generatedNinthSectionSign.val (generatedNinthLowRootMatrix r))) = _
  rw [co1XiEquiv_symm_apply, co1XiMatrix_square_eq_transpose, hm, xi_real_numerator,
    Matrix.transpose_smul, Matrix.smul_mulVec, hi, smul_smul]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
