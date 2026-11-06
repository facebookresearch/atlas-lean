/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Positive actual-source word programs and finite matrix image certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Hom
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A positive source instruction agrees with its declared characteristic-three image. -/
def y322MatrixWordProgramChecked {size : ℕ} (program : Y322WordProgram size)
    (matrix : Fin size → Matrix (Fin 7) (Fin 7) (ZMod 3)) (i : Fin size) : Prop :=
  match program i with
  | .one => matrix i = 1
  | .generator v => matrix i = y322Orthogonal3Reflection v
  | .multiply a b => matrix i = matrix (y322ProgramPrior i a) * matrix (y322ProgramPrior i b)
  | .inverse _ => False
  | .appendGenerator a v =>
    matrix i = matrix (y322ProgramPrior i a) * y322Orthogonal3Reflection v

/-- Checked source matrix recurrences are images of the actual original words. -/
theorem y322MatrixWordProgram_checked_image {size : ℕ} (program : Y322WordProgram size)
    (matrix : Fin size → Matrix (Fin 7) (Fin 7) (ZMod 3))
    (checked : ∀ i, y322MatrixWordProgramChecked program matrix i) (i : Fin size) :
    (y322Orthogonal3Hom (y322LocalProgramValue program i)).val = matrix i := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    have hc := checked i
    rw [y322LocalProgramValue_eq]
    cases hi : program i with
    | one =>
      simp only [y322MatrixWordProgramChecked, hi] at hc
      simpa only [y322InstructionValue, map_one, Units.val_one] using hc.symm
    | generator v =>
      simp only [y322MatrixWordProgramChecked, hi] at hc
      simpa only [y322InstructionValue, y322Orthogonal3Hom_generator,
        y322Orthogonal3Generator_matrix] using hc.symm
    | multiply a b =>
      simp only [y322MatrixWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, map_mul, Units.val_mul,
        ih (y322ProgramPrior i a) a.isLt, ih (y322ProgramPrior i b) b.isLt]
      exact hc.symm
    | inverse a =>
      simp only [y322MatrixWordProgramChecked, hi] at hc
    | appendGenerator a v =>
      simp only [y322MatrixWordProgramChecked, hi] at hc
      simp only [y322InstructionValue, map_mul, Units.val_mul,
        y322Orthogonal3Hom_generator, y322Orthogonal3Generator_matrix,
        ih (y322ProgramPrior i a) a.isLt]
      exact hc.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
