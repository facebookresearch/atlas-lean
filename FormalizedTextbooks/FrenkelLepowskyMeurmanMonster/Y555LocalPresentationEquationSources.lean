/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit defining equations for the compressed original C322 presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationPrograms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCertificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The signed letters of one acyclic auxiliary instruction, with no word expansion. -/
def y322AuxiliaryInstructionLetters {size : ℕ} (i : Fin size) :
    Y322WordInstruction i.val → List (Y322AuxiliaryAlphabet size × Bool)
  | .one => []
  | .generator v => [(.inl v, true)]
  | .multiply a b =>
      [(.inr (y322ProgramPrior i a), true), (.inr (y322ProgramPrior i b), true)]
  | .inverse a => [(.inr (y322ProgramPrior i a), false)]
  | .appendGenerator a v => [(.inr (y322ProgramPrior i a), true), (.inl v, true)]

/-- The literal instruction letters denote exactly the existing auxiliary defining word. -/
theorem y322AuxiliaryInstructionLetters_mk {size : ℕ} (i : Fin size)
    (instruction : Y322WordInstruction i.val) :
    FreeGroup.mk (y322AuxiliaryInstructionLetters i instruction) =
      y322AuxiliaryInstructionWord i instruction := by
  conv_lhs => rw [← FreeGroup.lift_of_apply
    (FreeGroup.mk (y322AuxiliaryInstructionLetters i instruction))]
  cases instruction <;> simp [y322AuxiliaryInstructionLetters, y322AuxiliaryInstructionWord]

/-- Source equations are original relators or actual acyclic word definitions. -/
abbrev Y322EquationSource (size : ℕ) := Y322RelatorIndex ⊕ Fin size

/-- Literal equations of the compressed presentation, using only original defining relations. -/
def y322EquationSource {size : ℕ} (program : Y322WordProgram size) :
    Y322EquationSource size → Y322WordEquation (Y322AuxiliaryAlphabet size)
  | .inl r =>
      ⟨(y322IndexedRelator r).toWord.map (fun letter => (.inl letter.1, letter.2)), []⟩
  | .inr i => ⟨[(.inr i, true)], y322AuxiliaryInstructionLetters i (program i)⟩

/-- Every compressed source equation holds in the actual original C322 group. -/
theorem y322EquationSource_valid {size : ℕ} (program : Y322WordProgram size)
    (s : Y322EquationSource size) :
    (y322EquationSource program s).Valid (y322AuxiliaryValue program) := by
  cases s with
  | inl r =>
    change FreeGroup.lift (y322AuxiliaryValue program)
      (FreeGroup.mk ((y322IndexedRelator r).toWord.map
        (fun letter => (Sum.inl letter.1, letter.2)))) =
      FreeGroup.lift (y322AuxiliaryValue program) (FreeGroup.mk [])
    have hm : (FreeGroup.lift (y322AuxiliaryValue program)).comp
        (FreeGroup.map Sum.inl) = PresentedGroup.mk y322Relations := by
      apply FreeGroup.ext_hom
      intro v
      simp [y322AuxiliaryValue, PresentedGroup.of]
    rw [← FreeGroup.map.mk, FreeGroup.mk_toWord]
    change ((FreeGroup.lift (y322AuxiliaryValue program)).comp (FreeGroup.map Sum.inl))
        (y322IndexedRelator r) = _
    rw [hm, y322IndexedRelator_valid]
    simp
  | inr i =>
    change FreeGroup.lift (y322AuxiliaryValue program) (FreeGroup.mk [(.inr i, true)]) =
      FreeGroup.lift (y322AuxiliaryValue program)
        (FreeGroup.mk (y322AuxiliaryInstructionLetters i (program i)))
    rw [y322AuxiliaryInstructionLetters_mk, y322AuxiliaryInstructionWord_value]
    simpa [y322AuxiliaryValue] using y322LocalProgramValue_eq program i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
