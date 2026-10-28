/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFirstTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityABCProduct

/-! The actual signed pair axes are closed under the original triality.
This is the pair-family destination in the first transition column. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem pair_plus_matrix (p : Fin 276) :
    (2 : ℝ) • Matrix.vecMulVec (griessShortVector (Sum.inl (1, p)))
      (griessShortVector (Sum.inl (1, p))) =
      conwayAxisMatrix p + (8 : ℝ) • trialityPairMatrix p := by
  funext i j
  have hs := griessPairOuter_sub p i j
  have hm := congrFun (congrFun (localAxis_matrix_outer p) i) j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.add_apply] at hm ⊢
  linarith

/-- Each of the four actual signed pair axes is the distinguished axis plus
an explicit pair of original dictionary basis vectors. -/
theorem generatedAxis_pair_dictionary (p : Fin 276) (s : Fin 2) (c : ZMod 2) :
    conwayShortAxis (Sum.inl (s, p)) c = conwayAxis p +
      (if s = 0 then 0 else (8 : ℝ)) • trialityABCBasis 0 p +
      (if c = 0 then (if s = 0 then 0 else (8 : ℝ))
        else (if s = 0 then (8 : ℝ) else 0)) • trialityABCBasis 1 p +
      (if c = 0 then 0 else (8 : ℝ)) • trialityABCBasis 2 p := by
  apply Function.LeftInverse.injective griessConwayDecode_encode
  change griessConwayEncodeLinear _ = griessConwayEncodeLinear _
  simp only [map_add, map_smul]
  have hcoe (x : GriessSpace) : griessConwayEncodeLinear x = griessConwayEncode x := rfl
  simp only [hcoe,
    conwayShortAxis_encode, conwayAxis_encode, griessConwayEncode_ABC_zero_sparse,
    griessConwayEncode_ABC_one_short, griessConwayEncode_ABC_two_short,
    conwayShortAxisRaw]
  fin_cases s <;> fin_cases c
  all_goals
    norm_num [qSign, conwayShortBasis]
    first
    | exact (localAxis_matrix_outer p).symm
    | exact pair_plus_matrix p
    | constructor
      · first | exact (localAxis_matrix_outer p).symm | exact pair_plus_matrix p
      · funext r
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
        ring

/-- Triality fixes the distinguished sign and cycles the other three signed
pair axes, with the original coordinate pair unchanged. -/
theorem generatedAxis_triality_pair_exact (p : Fin 276) (s : Fin 2) (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inl (s, p)) c) =
      conwayShortAxis (Sum.inl ((if c = 0 then 0 else 1), p))
        (if s = 0 then c else 1 - c) := by
  have h0 : trialityCycle 0 = 1 := by decide
  have h1 : trialityCycle 1 = 2 := by decide
  have h2 : trialityCycle 2 = 0 := by decide
  fin_cases s <;> fin_cases c
  all_goals
    simp only [generatedAxis_pair_dictionary, map_add, map_smul,
      conwayAxis_triality, sExtra_ABC_basis]
    simp only [h0, h1, h2]
    norm_num
    try abel

/-- The actual pair-family triality image belongs to the first local orbit. -/
theorem generatedAxis_triality_pair_mem_signed (p : Fin 276) (s : Fin 2) (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inl (s, p)) c) ∈ generatedSignedShortAxes := by
  rw [generatedAxis_triality_pair_exact]
  exact ⟨⟨Sum.inl ((if c = 0 then 0 else 1), p), (if s = 0 then c else 1 - c)⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
