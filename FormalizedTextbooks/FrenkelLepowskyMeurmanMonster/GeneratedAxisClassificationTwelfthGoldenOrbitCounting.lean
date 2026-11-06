/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitReachability

/-! Exact reachable distinct original matrix states give an honest full spatial stabilizer bound. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine full source E8 section group acts by its original ambient matrix conjugation. -/
local instance generatedTwelfthGoldenMatrixAction :
    MulAction generatedAxisE8FrameSystemSectionGroup (Matrix (Fin 24) (Fin 24) ℝ) where
  smul g M := conwayMatrixAction g.val M
  one_smul M := by change conwayMatrixAction 1 M = M; rw [map_one]; rfl
  mul_smul g h M := by
    change conwayMatrixAction (g.val * h.val) M = _
    rw [map_mul]
    rfl

/-- Exact reconstructed distinct integer codes retain distinct entire original axis matrices. -/
theorem generatedTwelfthGoldenOrbit_axis_injective
    (hNodes : ∀ n : Fin 24192, generatedTwelfthGoldenOrbitNodeProperty n)
    (hCodes : Function.Injective generatedTwelfthGoldenMatrixCode) :
    Function.Injective generatedTwelfthGoldenOrbitAxisMatrix := by
  intro n m h
  unfold generatedTwelfthGoldenOrbitAxisMatrix at h
  have hs := (smul_right_injective _ (by norm_num : (1 / 16 : ℝ) ≠ 0)) h
  have hh := add_right_cancel hs
  have hm := generatedTwelfthSectionMatrix_injective hh
  have hi : generatedTwelfthGoldenMatrixState n = generatedTwelfthGoldenMatrixState m := by
    ext i j
    have hij := congrFun (congrFun hm i) j
    simp only [Matrix.map_apply] at hij
    change (generatedTwelfthGoldenMatrixState n i j : ℝ) =
      (generatedTwelfthGoldenMatrixState m i j : ℝ) at hij
    exact_mod_cast hij
  apply hCodes
  rw [← (hNodes n).1, ← (hNodes m).1, hi]

/-- The entire original spatial stabilizer injects into the genuine E8 matrix stabilizer. -/
def generatedTwelfthGoldenOrbitSpatialEmbedding : generatedTwelfthSpatialStabilizer →*
    MulAction.stabilizer generatedAxisE8FrameSystemSectionGroup
      (griessConwayEncode generatedTwelfthAxis).1 where
  toFun g := ⟨⟨g.val, generatedTwelfth_matrix_fix_fifth_section g.val g.property⟩, g.property⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; rfl

/-- This original inclusion retains every actual full matrix fixer distinctly. -/
theorem generatedTwelfthGoldenOrbitSpatialEmbedding_injective :
    Function.Injective generatedTwelfthGoldenOrbitSpatialEmbedding := by
  intro g h he
  apply Subtype.ext
  exact congrArg (fun a => a.val.val) he

/-- Fully checked finite nodes and distinct codes bound the entire actual Co0 spatial stabilizer. -/
theorem generatedTwelfthGoldenOrbit_spatial_upper_of_nodes
    (hNodes : ∀ n : Fin 24192, generatedTwelfthGoldenOrbitNodeProperty n)
    (hCodes : Function.Injective generatedTwelfthGoldenMatrixCode)
    (hZero : ∀ n : Fin 24192, generatedTwelfthGoldenMatrixRank n = 0 → n = 18197)
    (hXi : ∀ n : Fin 24192, generatedTwelfthGoldenMatrixLetter n = 17 → n = 22875) :
    Nat.card generatedTwelfthSpatialStabilizer ≤ 7372800 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let actor : generatedAxisE8FrameSystemSectionGroup →
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (griessConwayEncode generatedTwelfthAxis).1 :=
    fun g => ⟨g • (griessConwayEncode generatedTwelfthAxis).1, ⟨g, rfl⟩⟩
  have hactor : Function.Surjective actor := by
    rintro ⟨M, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (griessConwayEncode generatedTwelfthAxis).1) := Finite.of_surjective actor hactor
  let reach : Fin 24192 → MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (griessConwayEncode generatedTwelfthAxis).1 := fun n =>
    ⟨generatedTwelfthGoldenOrbitAxisMatrix n,
      generatedTwelfthGoldenOrbit_reachable hNodes hZero hXi n⟩
  have hreach : Function.Injective reach := by
    intro n m he
    exact generatedTwelfthGoldenOrbit_axis_injective hNodes hCodes (congrArg Subtype.val he)
  have hsize := Nat.card_le_card_of_injective reach hreach
  simp only [Nat.card_fin] at hsize
  let _ := Fintype.ofFinite generatedAxisE8FrameSystemSectionGroup
  let _ := Fintype.ofFinite (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
    (griessConwayEncode generatedTwelfthAxis).1)
  let _ := Fintype.ofFinite (MulAction.stabilizer generatedAxisE8FrameSystemSectionGroup
    (griessConwayEncode generatedTwelfthAxis).1)
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    generatedAxisE8FrameSystemSectionGroup (griessConwayEncode generatedTwelfthAxis).1
  simp only [← Nat.card_eq_fintype_card] at horbit
  rw [generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at horbit
  have hstab := Nat.card_le_card_of_injective generatedTwelfthGoldenOrbitSpatialEmbedding
    generatedTwelfthGoldenOrbitSpatialEmbedding_injective
  have h1 := Nat.mul_le_mul_right
    (Nat.card (MulAction.stabilizer generatedAxisE8FrameSystemSectionGroup
      (griessConwayEncode generatedTwelfthAxis).1)) hsize
  rw [horbit] at h1
  have h2 := Nat.mul_le_mul_left 24192 hstab
  have h3 := h2.trans h1
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
