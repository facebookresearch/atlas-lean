/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitStep
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthE8Section
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrixRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitGenerators

/-! The reachable golden matrix states are exactly affine states of the original axis matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The full original axis matrix at one genuine finite golden-matrix address. -/
def generatedTwelfthGoldenOrbitAxisMatrix (n : Fin 24192) : Matrix (Fin 24) (Fin 24) ℝ :=
  (1 / 16 : ℝ) •
    (generatedTwelfthSectionMatrix
      ((generatedTwelfthGoldenMatrixState n).map (Int.castRingHom ℝ)) + (5 : ℕ) • 1)

/-- The finite base state is precisely the entire original actual axis matrix. -/
theorem generatedTwelfthGoldenOrbit_axis_base :
    generatedTwelfthGoldenOrbitAxisMatrix 18197 = (griessConwayEncode generatedTwelfthAxis).1 := by
  unfold generatedTwelfthGoldenOrbitAxisMatrix
  rw [← generatedTwelfthGoldenOrbit_base_actual, generatedTwelfth_golden_matrix_actual]
  module

/-- Every exact golden-matrix integer edge is the complete original axis matrix action. -/
theorem generatedTwelfthGoldenOrbit_axis_integer_step (g : Fin 18) (m n : Fin 24192)
    (h : generatedTwelfthSectionGeneratorTwice g * generatedTwelfthGoldenMatrixState m *
      (generatedTwelfthSectionGeneratorTwice g).transpose =
        (4 : ℕ) • generatedTwelfthGoldenMatrixState n) :
    conwayMatrixAction (generatedFifthSectionGenerator g)
      (generatedTwelfthGoldenOrbitAxisMatrix m) =
      generatedTwelfthGoldenOrbitAxisMatrix n := by
  unfold generatedTwelfthGoldenOrbitAxisMatrix
  rw [map_smul, map_add, map_nsmul, conwayMatrixAction_one,
    generatedTwelfthGoldenOrbit_integer_step g _ _ h]

/-- The original physical section is also the genuine source octad used by the existing E8 group. -/
theorem generatedTwelfth_section_fifth_actual :
    generatedTwelfthCoordinateSection =
      Matrix.diagonal (fun i =>
        if golayOctadWord generatedFifthFlagOctad i = 0 then (0 : ℝ) else 1) := by
  ext i j
  simp only [generatedTwelfthCoordinateSection, generatedTwelfthSectionInteger,
    Matrix.map_apply, Matrix.diagonal_apply, generatedFifth_flag_word_coordinate]
  by_cases hij : i = j
  · subst j
    cases Nat.testBit 0x0f000f i.val <;> simp [golayBooleanCast]
  · simp [hij]

/-- Every original full matrix fixer belongs to the actual source E8 section group. -/
theorem generatedTwelfth_matrix_fix_fifth_section (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1) :
    g ∈ generatedAxisE8FrameSystemSectionGroup := by
  rw [generatedAxisE8SectionStabilizer_mem]
  apply (generatedAxisE8_matrix_action_iff_section_stabilizer _ g).mp
  have h := generatedTwelfth_matrix_fix_section g hg
  rwa [generatedTwelfth_section_fifth_actual] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
