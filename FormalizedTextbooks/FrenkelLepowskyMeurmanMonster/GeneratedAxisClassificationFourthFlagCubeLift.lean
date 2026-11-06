/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagCube
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads

/-! The full fourth-axis lift supplies an actual sixteen-coordinate Golay-sign lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The complement of the standard first-eight octad is a genuine Golay codeword. -/
def generatedFourthFlagCubeSignCode : golayCode :=
  ⟨(fun _ => 1) + golayStandardOctad, by
    apply golayCode.add_mem
    · rw [← golay_all_one]
      exact ⟨Pi.single 11 1, rfl⟩
    · exact golayStandardOctad_mem⟩

/-- The actual codeword is zero on the first eight coordinates and one elsewhere. -/
theorem generatedFourth_flag_cube_sign_code (i : Fin 24) :
    generatedFourthFlagCubeSignCode.val i = if i.val < 8 then 0 else 1 := by
  change (1 : ZMod 2) + golayStandardOctad i = _
  by_cases hi : i.val < 8 <;> simp [golayStandardOctad, hi, CharTwo.add_self_eq_zero]

/-- The physical cube is the genuine Leech sign isometry of this actual Golay word. -/
theorem generatedFourth_flag_cube_isometry :
    generatedFourthFlagNormalizedLift.val.2 ^ 3 =
      golaySignIsometry generatedFourthFlagCubeSignCode := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [generatedFourth_flag_cube_apply]
  funext i
  change (if i.val < 8 then x i else -x i) =
    qSign (generatedFourthFlagCubeSignCode.val i) * x i
  rw [generatedFourth_flag_cube_sign_code]
  by_cases hi : i.val < 8 <;> simp [hi, qSign]

/-- Cubing the whole corrected lift gives an actual full-axis-fixing lift of the Golay sign. -/
theorem generatedFourth_flag_cube_sign_axis_lift :
    ∃ f : localFiberSubgroup,
      f.val.2 = golaySignIsometry generatedFourthFlagCubeSignCode ∧
      rhoLocal (localFiberIntoH f) generatedFourthAxis = generatedFourthAxis := by
  refine ⟨generatedFourthFlagCorrectedLift ^ 3, ?_, ?_⟩
  · change generatedFourthFlagCorrectedLift.val.2 ^ 3 = _
    rw [generatedFourth_flag_corrected_lift_spatial, generatedFourth_flag_cube_isometry]
  · have h := (generatedFourthFlagAxisLift ^ 3).property
    change rhoLocal (localFiberIntoH (generatedFourthFlagCorrectedLift ^ 3))
      generatedFourthAxis = generatedFourthAxis
    rw [map_pow]
    exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
