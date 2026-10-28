/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact recurrence statement for independently supplied finite vector candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3TPaths

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The candidate agrees with the original empty-path seed or its actual reflection step. -/
def y422Orthogonal3VectorRecurrence (i : Fin 9033) : Prop :=
  if hi : i = 0 then y422Orthogonal3VectorCache i = y422Orthogonal3FixedVector
  else y422Orthogonal3VectorCache i = y422Orthogonal3Reflection (y422TPathData i).2 *ᵥ
    y422Orthogonal3VectorCache
      ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩

/-- Candidate recurrence checks reduce to exact finite coordinate arithmetic. -/
instance y422Orthogonal3VectorRecurrenceDecidable (i : Fin 9033) :
    Decidable (y422Orthogonal3VectorRecurrence i) := by
  unfold y422Orthogonal3VectorRecurrence
  infer_instance

/-- Checked recurrences identify every candidate with the actual original source-word action. -/
theorem y422Orthogonal3VectorCache_eq_actual
    (hchecked : ∀ i, y422Orthogonal3VectorRecurrence i) (i : Fin 9033) :
    y422Orthogonal3TPathVector i = y422Orthogonal3VectorCache i := by
  have hmain : ∀ n, ∀ j : Fin 9033, j.val = n →
      y422Orthogonal3TPathVector j = y422Orthogonal3VectorCache j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      by_cases hz : j = 0
      · subst j
        rw [y422Orthogonal3TPathVector_zero]
        symm
        simpa [y422Orthogonal3VectorRecurrence] using hchecked 0
      · let parent : Fin 9033 :=
          ⟨(y422TPathData j).1, (y422TPathData_prior j hz).trans j.isLt⟩
        have hp : parent.val < n := by
          change (y422TPathData j).1 < n
          rw [← hj]
          exact y422TPathData_prior j hz
        have he := ih parent.val hp parent rfl
        rw [y422Orthogonal3TPathVector_step j hz, he]
        symm
        simpa [y422Orthogonal3VectorRecurrence, hz, parent] using hchecked j
  exact hmain i.val i rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
