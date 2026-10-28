/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source A5 candidate group elements and their actual finite matrix images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Validation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationMatrixWordPrograms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordSubgroupMembership
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555TypeAParabolicOrderA5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawInstructionEquality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The base source A5 candidate programme instruction is exactly the empty word. -/
theorem y322Orthogonal3A5Program_zero : y322Orthogonal3A5Program 0 = .one := by
  apply y322Instruction_eq_of_raw_eq
  rw [y322Orthogonal3A5Program, y322RawWordProgram_raw]
  rfl

/-- Every nonbase A5 source word instruction is exactly an earlier prefix and source generator. -/
theorem y322Orthogonal3A5Program_step (i : Fin 720) (hi : i.val ≠ 0) :
    ∃ ref : Fin i.val, ref.val = (y322Orthogonal3A5Parent i).val ∧
      y322Orthogonal3A5Program i = .appendGenerator ref (y322Orthogonal3A5Generator i) := by
  have hp : (y322Orthogonal3A5Parent i).val < i.val := by
    have h := y322Orthogonal3A5Raw_allowed i
    simpa only [y322Orthogonal3A5Raw, ite_eq_right hi, Y322RawWordInstruction.Allowed] using h
  refine ⟨⟨(y322Orthogonal3A5Parent i).val, hp⟩, rfl, ?_⟩
  apply y322Instruction_eq_of_raw_eq
  rw [y322Orthogonal3A5Program, y322RawWordProgram_raw]
  simp only [y322Orthogonal3A5Raw, ite_eq_right hi, y322InstructionRaw]

/-- All finite A5 prefix recurrences are the exact image recurrences of actual source words. -/
theorem y322Orthogonal3A5Program_matrix_checked (i : Fin 720) :
    y322MatrixWordProgramChecked y322Orthogonal3A5Program y322Orthogonal3A5Matrix i := by
  have hc := y322Orthogonal3A5_checked i
  simp only [y322Orthogonal3A5CheckAt, dite_eq_left i.isLt] at hc
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [y322MatrixWordProgramChecked, y322Orthogonal3A5Program_zero]
    simpa using hc.1
  · obtain ⟨ref, href, hprogram⟩ := y322Orthogonal3A5Program_step i hi
    have he : y322ProgramPrior i ref = y322Orthogonal3A5Parent i := Fin.ext href
    rw [y322MatrixWordProgramChecked, hprogram]
    change y322Orthogonal3A5Matrix i =
      y322Orthogonal3A5Matrix (y322ProgramPrior i ref) *
        y322Orthogonal3Reflection (y322Orthogonal3A5Generator i)
    rw [he]
    simpa only [ite_eq_right hi] using hc.1

/-- Every literal source generator in the A5 candidate programme lies in the actual A5 subgroup. -/
theorem y322Orthogonal3A5Program_subgroup_checked (i : Fin 720) :
    y322WordProgramSubgroupChecked y322A5Parabolic y322Orthogonal3A5Program i := by
  have hc := y322Orthogonal3A5_checked i
  simp only [y322Orthogonal3A5CheckAt, dite_eq_left i.isLt] at hc
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    rw [y322WordProgramSubgroupChecked, y322Orthogonal3A5Program_zero]
    trivial
  · obtain ⟨ref, _, hprogram⟩ := y322Orthogonal3A5Program_step i hi
    rw [y322WordProgramSubgroupChecked, hprogram]
    exact y322A5Parabolic_generator_mem _ hc.2.1

/-- An actual original C322 element specified by a finite positive A5 source word. -/
noncomputable def y322Orthogonal3A5SourceCandidate (i : Fin 720) : Y322Presentation :=
  y322LocalProgramValue y322Orthogonal3A5Program i

/-- Every source candidate belongs to the genuine five-generator A5 subgroup. -/
theorem y322Orthogonal3A5SourceCandidate_mem (i : Fin 720) :
    y322Orthogonal3A5SourceCandidate i ∈ y322A5Parabolic :=
  y322WordProgram_checked_mem _ _ y322Orthogonal3A5Program_subgroup_checked i

/-- Each source candidate has exactly its checked actual finite matrix image. -/
theorem y322Orthogonal3A5SourceCandidate_matrix (i : Fin 720) :
    (y322Orthogonal3Hom (y322Orthogonal3A5SourceCandidate i)).val =
      y322Orthogonal3A5Matrix i :=
  y322MatrixWordProgram_checked_image _ _ y322Orthogonal3A5Program_matrix_checked i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
