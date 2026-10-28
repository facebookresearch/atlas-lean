/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Acyclic auxiliary-word definitions in the exact independent local presentation.
These definitions map into the actual local group and introduce no relation assumption. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source generators together with finite acyclic word-program names. -/
abbrev Y322AuxiliaryAlphabet (size : ℕ) := Fin 8 ⊕ Fin size

/-- The literal right-hand side of an auxiliary word definition. -/
def y322AuxiliaryInstructionWord {size : ℕ} (i : Fin size) :
    Y322WordInstruction i.val → FreeGroup (Y322AuxiliaryAlphabet size)
  | .one => 1
  | .generator v => FreeGroup.of (.inl v)
  | .multiply a b =>
      FreeGroup.of (.inr (y322ProgramPrior i a)) *
        FreeGroup.of (.inr (y322ProgramPrior i b))
  | .inverse a => (FreeGroup.of (.inr (y322ProgramPrior i a)))⁻¹
  | .appendGenerator a v =>
      FreeGroup.of (.inr (y322ProgramPrior i a)) * FreeGroup.of (.inl v)

/-- Each auxiliary letter is defined to equal its exact earlier-generator word. -/
def y322AuxiliaryDefinition {size : ℕ} (program : Y322WordProgram size) (i : Fin size) :
    FreeGroup (Y322AuxiliaryAlphabet size) :=
  FreeGroup.of (.inr i) * (y322AuxiliaryInstructionWord i (program i))⁻¹

/-- Original source relators together with every acyclic auxiliary definition. -/
def y322AuxiliaryRelations {size : ℕ} (program : Y322WordProgram size) :
    Set (FreeGroup (Y322AuxiliaryAlphabet size)) :=
  {w | (∃ r ∈ y322Relations, w = FreeGroup.map Sum.inl r) ∨
    ∃ i, w = y322AuxiliaryDefinition program i}

/-- The exact source presentation with its finite explicitly defined word names. -/
abbrev Y322AuxiliaryPresentation {size : ℕ} (program : Y322WordProgram size) :=
  PresentedGroup (y322AuxiliaryRelations program)

/-- Every auxiliary name denotes its actual word value in the original local group. -/
noncomputable def y322AuxiliaryValue {size : ℕ} (program : Y322WordProgram size) :
    Y322AuxiliaryAlphabet size → Y322Presentation
  | .inl v => PresentedGroup.of v
  | .inr i => y322LocalProgramValue program i

/-- An auxiliary definition's right-hand side evaluates as precisely its word instruction. -/
theorem y322AuxiliaryInstructionWord_value {size : ℕ} (program : Y322WordProgram size)
    (i : Fin size) :
    FreeGroup.lift (y322AuxiliaryValue program)
        (y322AuxiliaryInstructionWord i (program i)) =
      y322InstructionValue (fun v => (PresentedGroup.of v : Y322Presentation))
        (fun a => y322LocalProgramValue program (y322ProgramPrior i a)) (program i) := by
  cases program i <;>
    simp [y322AuxiliaryInstructionWord, y322InstructionValue, y322AuxiliaryValue]

/-- Each auxiliary definition is true in the actual independent local group. -/
theorem y322AuxiliaryDefinition_valid {size : ℕ} (program : Y322WordProgram size)
    (i : Fin size) :
    FreeGroup.lift (y322AuxiliaryValue program) (y322AuxiliaryDefinition program i) = 1 := by
  rw [y322AuxiliaryDefinition, map_mul, map_inv, FreeGroup.lift_apply_of]
  change y322LocalProgramValue program i *
    (FreeGroup.lift (y322AuxiliaryValue program)
      (y322AuxiliaryInstructionWord i (program i)))⁻¹ = 1
  rw [y322AuxiliaryInstructionWord_value, ← y322LocalProgramValue_eq, mul_inv_cancel]

/-- All relations of the auxiliary presentation hold in the actual original local group. -/
theorem y322AuxiliaryRelations_valid {size : ℕ} (program : Y322WordProgram size)
    (w : FreeGroup (Y322AuxiliaryAlphabet size)) (hw : w ∈ y322AuxiliaryRelations program) :
    FreeGroup.lift (y322AuxiliaryValue program) w = 1 := by
  rcases hw with ⟨r, hr, rfl⟩ | ⟨i, rfl⟩
  · have hm : (FreeGroup.lift (y322AuxiliaryValue program)).comp
        (FreeGroup.map Sum.inl) = PresentedGroup.mk y322Relations := by
      apply FreeGroup.ext_hom
      intro v
      simp [y322AuxiliaryValue, PresentedGroup.of]
    change ((FreeGroup.lift (y322AuxiliaryValue program)).comp (FreeGroup.map Sum.inl)) r = 1
    rw [hm]
    exact PresentedGroup.one_of_mem hr
  · exact y322AuxiliaryDefinition_valid program i

/-- Canonical interpretation of every auxiliary word in the actual source local group. -/
noncomputable def y322AuxiliaryToLocal {size : ℕ} (program : Y322WordProgram size) :
    Y322AuxiliaryPresentation program →* Y322Presentation :=
  PresentedGroup.toGroup (y322AuxiliaryRelations_valid program)

/-- The canonical interpretation assigns exactly the declared actual source word value. -/
@[simp] theorem y322AuxiliaryToLocal_generator {size : ℕ} (program : Y322WordProgram size)
    (v : Y322AuxiliaryAlphabet size) :
    y322AuxiliaryToLocal program (PresentedGroup.of v) = y322AuxiliaryValue program v :=
  PresentedGroup.toGroup.of (y322AuxiliaryRelations_valid program)

/-- Original source relators also hold at the original letters of the auxiliary presentation. -/
theorem y322LocalIntoAuxiliary_valid {size : ℕ} (program : Y322WordProgram size)
    (r : FreeGroup (Fin 8)) (hr : r ∈ y322Relations) :
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (Sum.inl v) : Y322AuxiliaryPresentation program)) r = 1 := by
  have hm : (PresentedGroup.mk (y322AuxiliaryRelations program)).comp
      (FreeGroup.map Sum.inl) = FreeGroup.lift (fun v =>
        (PresentedGroup.of (Sum.inl v) : Y322AuxiliaryPresentation program)) := by
    apply FreeGroup.ext_hom
    intro v
    simp [PresentedGroup.of]
  rw [← hm, MonoidHom.comp_apply]
  exact PresentedGroup.one_of_mem (Or.inl ⟨r, hr, rfl⟩)

/-- Inclusion of the original generators into the explicitly defined auxiliary presentation. -/
noncomputable def y322LocalIntoAuxiliary {size : ℕ} (program : Y322WordProgram size) :
    Y322Presentation →* Y322AuxiliaryPresentation program :=
  PresentedGroup.toGroup (y322LocalIntoAuxiliary_valid program)

/-- The source inclusion preserves the literal original generator names. -/
@[simp] theorem y322LocalIntoAuxiliary_generator {size : ℕ} (program : Y322WordProgram size)
    (v : Fin 8) :
    y322LocalIntoAuxiliary program (PresentedGroup.of v) = PresentedGroup.of (Sum.inl v) :=
  PresentedGroup.toGroup.of (y322LocalIntoAuxiliary_valid program)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
