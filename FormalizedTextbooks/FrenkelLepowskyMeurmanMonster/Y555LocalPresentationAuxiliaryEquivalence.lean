/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Acyclic word definitions give an actual isomorphism with the original local presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationAuxiliary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The quotient value of an auxiliary right-hand side is its literal instruction value. -/
theorem y322AuxiliaryInstructionWord_quotient {size : ℕ} (program : Y322WordProgram size)
    (i : Fin size) :
    PresentedGroup.mk (y322AuxiliaryRelations program)
        (y322AuxiliaryInstructionWord i (program i)) =
      y322InstructionValue (fun v =>
        (PresentedGroup.of (.inl v) : Y322AuxiliaryPresentation program))
        (fun a => PresentedGroup.of (.inr (y322ProgramPrior i a))) (program i) := by
  cases program i <;>
    simp [y322AuxiliaryInstructionWord, y322InstructionValue, PresentedGroup.of]

/-- Each auxiliary generator equals exactly its earlier-generator defining instruction. -/
theorem y322Auxiliary_generator_definition {size : ℕ} (program : Y322WordProgram size)
    (i : Fin size) :
    (PresentedGroup.of (.inr i) : Y322AuxiliaryPresentation program) =
      y322InstructionValue (fun v =>
        (PresentedGroup.of (.inl v) : Y322AuxiliaryPresentation program))
        (fun a => PresentedGroup.of (.inr (y322ProgramPrior i a))) (program i) := by
  have h := PresentedGroup.one_of_mem (rels := y322AuxiliaryRelations program)
    (show y322AuxiliaryDefinition program i ∈ y322AuxiliaryRelations program from
      Or.inr ⟨i, rfl⟩)
  simp only [y322AuxiliaryDefinition, map_mul, map_inv] at h
  have he := eq_of_mul_inv_eq_one h
  change (PresentedGroup.of (.inr i) : Y322AuxiliaryPresentation program) = _ at he
  rw [y322AuxiliaryInstructionWord_quotient] at he
  exact he

/-- Acyclic induction identifies every auxiliary name with its actual source-generator word. -/
theorem y322Auxiliary_program_value {size : ℕ} (program : Y322WordProgram size)
    (i : Fin size) :
    y322WordProgramValue program (fun v =>
      (PresentedGroup.of (.inl v) : Y322AuxiliaryPresentation program)) i =
        PresentedGroup.of (.inr i) := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    rw [y322WordProgramValue_eq, y322Auxiliary_generator_definition]
    cases program i with
    | one => rfl
    | generator v => rfl
    | multiply a b =>
      simp only [y322InstructionValue,
        ih (y322ProgramPrior i a) a.isLt, ih (y322ProgramPrior i b) b.isLt]
    | inverse a =>
      simp only [y322InstructionValue, ih (y322ProgramPrior i a) a.isLt]
    | appendGenerator a v =>
      simp only [y322InstructionValue, ih (y322ProgramPrior i a) a.isLt]

/-- Including and interpreting the original source generators is the identity. -/
theorem y322AuxiliaryToLocal_comp {size : ℕ} (program : Y322WordProgram size) :
    (y322AuxiliaryToLocal program).comp (y322LocalIntoAuxiliary program) =
      MonoidHom.id Y322Presentation := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y322LocalIntoAuxiliary_generator,
    y322AuxiliaryToLocal_generator, y322AuxiliaryValue, MonoidHom.id_apply]

/-- Interpreting and including every acyclic auxiliary word is also the identity. -/
theorem y322LocalIntoAuxiliary_comp {size : ℕ} (program : Y322WordProgram size) :
    (y322LocalIntoAuxiliary program).comp (y322AuxiliaryToLocal program) =
      MonoidHom.id (Y322AuxiliaryPresentation program) := by
  apply PresentedGroup.ext
  intro v
  cases v with
  | inl v =>
    simp only [MonoidHom.comp_apply, y322AuxiliaryToLocal_generator,
      y322AuxiliaryValue, y322LocalIntoAuxiliary_generator, MonoidHom.id_apply]
  | inr i =>
    simp only [MonoidHom.comp_apply, y322AuxiliaryToLocal_generator,
      y322AuxiliaryValue, MonoidHom.id_apply]
    change y322LocalIntoAuxiliary program
      (y322WordProgramValue program (fun v => (PresentedGroup.of v : Y322Presentation)) i) = _
    rw [y322WordProgramValue_map]
    simpa only [y322LocalIntoAuxiliary_generator] using y322Auxiliary_program_value program i

/-- The explicit auxiliary presentation is actually isomorphic to the original local group. -/
noncomputable def y322AuxiliaryEquiv {size : ℕ} (program : Y322WordProgram size) :
    Y322AuxiliaryPresentation program ≃* Y322Presentation where
  toFun := y322AuxiliaryToLocal program
  invFun := y322LocalIntoAuxiliary program
  left_inv a := by
    have h := DFunLike.congr_fun (y322LocalIntoAuxiliary_comp program) a
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  right_inv a := by
    have h := DFunLike.congr_fun (y322AuxiliaryToLocal_comp program) a
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  map_mul' := (y322AuxiliaryToLocal program).map_mul

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
