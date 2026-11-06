/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Elementary Coxeter certificates for acyclic source-generator word programs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Centrality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Positive generator word for an instruction, using the earlier supplied positive words. -/
def y322InstructionPositiveWord {earlier : ℕ} (prior : Fin earlier → List (Fin 8)) :
    Y322WordInstruction earlier → List (Fin 8)
  | .one => []
  | .generator v => [v]
  | .multiply a b => prior a ++ prior b
  | .inverse a => (prior a).reverse
  | .appendGenerator a v => prior a ++ [v]

/-- Positive instruction words denote their exact group operations in the actual local quotient. -/
theorem y322InstructionPositiveWord_value {earlier : ℕ}
    (prior : Fin earlier → List (Fin 8)) (instruction : Y322WordInstruction earlier) :
    y322PositiveWord (y322InstructionPositiveWord prior instruction) =
      y322InstructionValue (fun v => (PresentedGroup.of v : Y322Presentation))
        (fun a => y322PositiveWord (prior a)) instruction := by
  cases instruction with
  | one => rfl
  | generator v => simp [y322InstructionPositiveWord, y322PositiveWord, y322InstructionValue]
  | multiply a b => exact y322PositiveWord_append (prior a) (prior b)
  | inverse a => exact y322PositiveWord_reverse (prior a)
  | appendGenerator a v =>
    simp [y322InstructionPositiveWord, y322InstructionValue,
      y322PositiveWord]

/-- Finite Coxeter certificates identify source words with their supplied positive words. -/
theorem y322WordProgramValue_of_coxeter_certificates {size : ℕ}
    (program : Y322WordProgram size) (words : Fin size → List (Fin 8))
    (moves : Fin size → List Y322CoxeterMove)
    (h : ∀ i, y322CoxeterRun (moves i)
      (y322InstructionPositiveWord (fun a => words (y322ProgramPrior i a)) (program i)) =
        some (words i)) (i : Fin size) :
    y322LocalProgramValue program i = y322PositiveWord (words i) := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    rw [y322LocalProgramValue_eq]
    have hp : (fun a => y322LocalProgramValue program (y322ProgramPrior i a)) =
        (fun a => y322PositiveWord (words (y322ProgramPrior i a))) := by
      funext a
      exact ih (y322ProgramPrior i a) a.isLt
    rw [hp, ← y322InstructionPositiveWord_value]
    exact y322CoxeterRun_valid (moves i) _ (words i) (h i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
