/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual subgroup membership of source word programs from their generator labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationWordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each generator of a source instruction lies in the specified actual subgroup. -/
def y322WordProgramSubgroupChecked {size : ℕ} (K : Subgroup Y322Presentation)
    (program : Y322WordProgram size) (i : Fin size) : Prop :=
  match program i with
  | .generator v => PresentedGroup.of v ∈ K
  | .appendGenerator _ v => PresentedGroup.of v ∈ K
  | _ => True

/-- Actual subgroup closure propagates through all acyclic original-source word instructions. -/
theorem y322WordProgram_checked_mem {size : ℕ} (K : Subgroup Y322Presentation)
    (program : Y322WordProgram size) (checked : ∀ i, y322WordProgramSubgroupChecked K program i)
    (i : Fin size) : y322LocalProgramValue program i ∈ K := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    have hc := checked i
    rw [y322LocalProgramValue_eq]
    cases hi : program i with
    | one => exact K.one_mem
    | generator v =>
      simpa only [y322InstructionValue, y322WordProgramSubgroupChecked, hi] using hc
    | multiply a b =>
      exact K.mul_mem (ih (y322ProgramPrior i a) a.isLt) (ih (y322ProgramPrior i b) b.isLt)
    | inverse a => exact K.inv_mem (ih (y322ProgramPrior i a) a.isLt)
    | appendGenerator a v =>
      apply K.mul_mem (ih (y322ProgramPrior i a) a.isLt)
      simpa only [y322WordProgramSubgroupChecked, hi] using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
