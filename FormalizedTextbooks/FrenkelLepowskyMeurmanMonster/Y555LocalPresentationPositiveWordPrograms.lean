/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Positive literal words retain their actual original-source program values. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCoxeterRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every positive source program instruction has its exact literal word spelling. -/
def y322PositiveWordProgramChecked {size : ℕ} (program : Y322WordProgram size)
    (word : Fin size → List (Fin 8)) (i : Fin size) : Prop :=
  match program i with
  | .one => word i = []
  | .generator v => word i = [v]
  | .multiply a b => word i = word (y322ProgramPrior i a) ++ word (y322ProgramPrior i b)
  | .inverse _ => False
  | .appendGenerator a v => word i = word (y322ProgramPrior i a) ++ [v]

/-- Checked literal positive spellings evaluate to their actual original C322 source words. -/
theorem y322PositiveWordProgram_checked_value {size : ℕ} (program : Y322WordProgram size)
    (word : Fin size → List (Fin 8)) (checked : ∀ i, y322PositiveWordProgramChecked program word i)
    (i : Fin size) : y322LocalProgramValue program i = y322PositiveWord (word i) := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    have hc := checked i
    rw [y322LocalProgramValue_eq]
    cases hi : program i with
    | one =>
      simp only [y322PositiveWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, hc, y322PositiveWord, List.map_nil, List.prod_nil]
    | generator v =>
      simp only [y322PositiveWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, hc, y322PositiveWord, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
    | multiply a b =>
      simp only [y322PositiveWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, hc, y322PositiveWord_append,
        ih (y322ProgramPrior i a) a.isLt, ih (y322ProgramPrior i b) b.isLt]
    | inverse a => simp only [y322PositiveWordProgramChecked, hi] at hc
    | appendGenerator a v =>
      simp only [y322PositiveWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, hc, y322PositiveWord_append,
        ih (y322ProgramPrior i a) a.isLt]
      simp [y322PositiveWord]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
