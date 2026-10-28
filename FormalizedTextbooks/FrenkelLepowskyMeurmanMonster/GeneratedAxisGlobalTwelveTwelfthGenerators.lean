/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeAxisFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSectionPackedWordActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskInverse

/-! Six actual whole-axis fixers of the Twelfth representative for its binary Ω forest.

The closed Twelfth count attains each of the three original matrix-fixer words by a genuine
element of the full local stabilizer of `generatedTwelfthAxis`. The forest generators are these
three fixers and their inverses. Their binary actions are the checked column masks of the
original packed section words; no generator matrix is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Each original matrix-fixer word is the projection of an actual whole-axis fixer. -/
theorem generatedAxisGlobalTwelveTwelfth_fixer_exists (g : Fin 3) :
    ∃ k : generatedTwelfthLocalAxisStabilizer,
      projH k.val = QuotientGroup.mk (generatedTwelfthMatrixFixer g).val := by
  obtain ⟨k, hk⟩ :=
    generatedTwelfth_three_root_projection_mem generatedTwelfth_three_candidate_axis_fixation g
  exact ⟨k, hk⟩

/-- A chosen actual whole-axis fixer over each original matrix-fixer word. -/
def generatedAxisGlobalTwelveTwelfthFixer (g : Fin 3) : generatedTwelfthLocalAxisStabilizer :=
  Classical.choose (generatedAxisGlobalTwelveTwelfth_fixer_exists g)

/-- The chosen fixers have exactly the original word projections. -/
theorem generatedAxisGlobalTwelveTwelfthFixer_projection (g : Fin 3) :
    projH (generatedAxisGlobalTwelveTwelfthFixer g).val =
      QuotientGroup.mk (generatedTwelfthMatrixFixer g).val :=
  Classical.choose_spec (generatedAxisGlobalTwelveTwelfth_fixer_exists g)

/-- The six forest generators: the three fixers, then their inverses. -/
def generatedAxisGlobalTwelveTwelfthGenerator (e : Fin 6) : generatedTwelfthLocalAxisStabilizer :=
  if h : e.val < 3 then generatedAxisGlobalTwelveTwelfthFixer ⟨e.val, h⟩
  else (generatedAxisGlobalTwelveTwelfthFixer ⟨e.val - 3, by omega⟩)⁻¹

/-- Exact column masks of the three original matrix-fixer words. -/
def generatedAxisGlobalTwelveTwelfthForwardColumns : Fin 3 → Fin 24 → ℕ :=
  ![![2144838, 5222949, 3604484, 2210348, 5621387, 2429553, 203382, 3228745, 8043313, 3980089,
      8311344, 2048, 2752512, 1325056, 745472, 1519616, 526336, 4464640, 2236416, 4718592,
      4698112, 5746688, 7798784, 9790638],
    ![5900055, 1578775, 919552, 4886467, 4620047, 15388748, 10121288, 10336073, 12171311,
      13128779, 3711744, 4065280, 4171872, 4106336, 7258436, 524288, 4096000, 7084135, 2826339,
      4077568, 3190788, 4831232, 2734080, 2978062],
    ![6357556, 7078532, 505856, 7680564, 11708988, 13297053, 13860141, 4020095, 10595097,
      10008489, 14754221, 1507328, 458960, 2457607, 5944256, 3879123, 14336, 4196355, 5734407,
      34816, 8304640, 4194308, 4063232, 13466749]]

/-- Proposed inverse column masks of the same three words. -/
def generatedAxisGlobalTwelveTwelfthInverseColumns : Fin 3 → Fin 24 → ℕ :=
  ![![7779082, 3193710, 4786180, 7451392, 1044236, 5531469, 6516522, 7348373, 7949834, 8049729,
      5318560, 2048, 3874816, 333824, 325632, 2721792, 7733248, 7776256, 921600, 67584,
      3145728, 7843840, 591872, 11833362],
    ![4140960, 6098883, 2557956, 5932823, 1576513, 8900823, 8997047, 16711423, 14430611,
      13766135, 2331172, 4063232, 3780704, 3258464, 1259812, 4130816, 12288, 1048675, 3047527,
      32768, 4831236, 4829184, 2732032, 9553571],
    ![2935068, 7850268, 919552, 3359174, 14473291, 8865101, 8973635, 2764044, 11371852,
      5879050, 4635492, 7800832, 8259690, 524394, 5225026, 8325120, 1808393, 7182336, 526349,
      6430733, 8257540, 3780612, 3016704, 1395120]]

set_option maxHeartbeats 4000000 in
-- Replay all 72 unit columns through the complete original packed section words.
/-- Every displayed forward column is the original packed word action on a coordinate unit. -/
theorem generatedAxisGlobalTwelveTwelfth_word_columns : ∀ g : Fin 3, ∀ j : Fin 24,
    generatedTwelfthSectionPackedMaskWord (generatedTwelfthMatrixFixerWord g) (2 ^ j.val) =
      generatedAxisGlobalTwelveTwelfthForwardColumns g j := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all 72 single-bit column selections of the displayed forward columns.
/-- Column selection on a coordinate unit returns that displayed column. -/
theorem generatedAxisGlobalTwelveTwelfth_forward_unit : ∀ g : Fin 3, ∀ j : Fin 24,
    generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthForwardColumns g)
      (2 ^ j.val) = generatedAxisGlobalTwelveTwelfthForwardColumns g j := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all 72 compositions of the forward words with the proposed inverse columns.
/-- The proposed inverse columns are carried to the coordinate units by the forward columns. -/
theorem generatedAxisGlobalTwelveTwelfth_inverse_columns : ∀ g : Fin 3, ∀ j : Fin 24,
    generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveTwelfthForwardColumns g)
      (generatedAxisGlobalTwelveTwelfthInverseColumns g j) = 2 ^ j.val := by
  decide +kernel

/-- The full binary action of each original matrix-fixer word is its column matrix. -/
theorem generatedAxisGlobalTwelveTwelfth_word_binary (g : Fin 3) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthMatrixFixer g).val v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveTwelfthForwardColumns g) *ᵥ
        v := by
  have h : ((leechBinaryAction (generatedTwelfthMatrixFixer g).val :
        (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :
        (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2)) =
      Matrix.mulVecLin
        (generatedAxisGlobalMaskColumnMatrix
          (generatedAxisGlobalTwelveTwelfthForwardColumns g)) := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    rw [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
      ← generatedAxisGlobalMaskDecode_two_pow]
    have hw := generatedTwelfth_section_word_packed_actual (generatedTwelfthMatrixFixerWord g)
      (2 ^ j.val)
    change leechBinaryAction (generatedTwelfthMatrixFixer g).val _ = _ at hw
    rw [hw, generatedAxisGlobalTwelveTwelfth_word_columns,
      ← generatedAxisGlobalMaskColumnAction_decode, generatedAxisGlobalTwelveTwelfth_forward_unit]
  exact LinearMap.congr_fun h v

/-- The inverse binary action of each original matrix-fixer word is its inverse column matrix. -/
theorem generatedAxisGlobalTwelveTwelfth_word_inverse_binary (g : Fin 3) (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedTwelfthMatrixFixer g).val⁻¹ v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveTwelfthInverseColumns g) *ᵥ
        v := by
  rw [map_inv]
  change (leechBinaryAction (generatedTwelfthMatrixFixer g).val).symm v = _
  apply generatedAxisGlobalMaskColumnMatrix_inverse_apply _
    (generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveTwelfthForwardColumns g))
    _ (generatedAxisGlobalTwelveTwelfth_word_binary g)
  intro j
  rw [← generatedAxisGlobalMaskColumnAction_decode,
    generatedAxisGlobalTwelveTwelfth_inverse_columns, generatedAxisGlobalMaskDecode_two_pow]

/-- Column masks of the inverse action of each forest generator (the descent parents). -/
def generatedAxisGlobalTwelveTwelfthParentColumns (e : Fin 6) : Fin 24 → ℕ :=
  if h : e.val < 3 then generatedAxisGlobalTwelveTwelfthInverseColumns ⟨e.val, h⟩
  else generatedAxisGlobalTwelveTwelfthForwardColumns ⟨e.val - 3, by omega⟩

/-- Column masks of the forward action of each forest generator. -/
def generatedAxisGlobalTwelveTwelfthChildColumns (e : Fin 6) : Fin 24 → ℕ :=
  if h : e.val < 3 then generatedAxisGlobalTwelveTwelfthForwardColumns ⟨e.val, h⟩
  else generatedAxisGlobalTwelveTwelfthInverseColumns ⟨e.val - 3, by omega⟩

/-- Every forest generator acts on the actual binary coordinates by its child columns. -/
theorem generatedAxisGlobalTwelveTwelfthGenerator_child (e : Fin 6) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthGenerator e).val) v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveTwelfthChildColumns e) *ᵥ
        v := by
  by_cases h : e.val < 3
  · simp only [generatedAxisGlobalTwelveTwelfthGenerator,
      generatedAxisGlobalTwelveTwelfthChildColumns, h, ↓reduceDIte]
    rw [generatedAxisGlobalTwelveTwelfthFixer_projection]
    exact generatedAxisGlobalTwelveTwelfth_word_binary _ v
  · simp only [generatedAxisGlobalTwelveTwelfthGenerator,
      generatedAxisGlobalTwelveTwelfthChildColumns, h, ↓reduceDIte]
    rw [Subgroup.coe_inv, map_inv, generatedAxisGlobalTwelveTwelfthFixer_projection,
      ← QuotientGroup.mk_inv]
    exact generatedAxisGlobalTwelveTwelfth_word_inverse_binary _ v

/-- Every forest generator inverse acts on the actual binary coordinates by its parent columns. -/
theorem generatedAxisGlobalTwelveTwelfthGenerator_parent (e : Fin 6) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (projH (generatedAxisGlobalTwelveTwelfthGenerator e).val⁻¹) v =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveTwelfthParentColumns e) *ᵥ
        v := by
  by_cases h : e.val < 3
  · simp only [generatedAxisGlobalTwelveTwelfthGenerator,
      generatedAxisGlobalTwelveTwelfthParentColumns, h, ↓reduceDIte]
    rw [map_inv, generatedAxisGlobalTwelveTwelfthFixer_projection, ← QuotientGroup.mk_inv]
    exact generatedAxisGlobalTwelveTwelfth_word_inverse_binary _ v
  · simp only [generatedAxisGlobalTwelveTwelfthGenerator,
      generatedAxisGlobalTwelveTwelfthParentColumns, h, ↓reduceDIte]
    rw [Subgroup.coe_inv, inv_inv, generatedAxisGlobalTwelveTwelfthFixer_projection]
    exact generatedAxisGlobalTwelveTwelfth_word_binary _ v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
