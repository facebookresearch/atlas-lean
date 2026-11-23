/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Logics.CTLStar.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
import CSLibExt.Foundations.Semantics.LTS.OmegaExecution

/-!
# Run/execution correspondence with nontrivial labels

Labels record the source state in a Boolean toggle. Forgetting or
selecting labels must use this same canonical transition relation.
-/

@[expose] public section

namespace Cslib.CTLStar.Tests

/-- A canonical Boolean toggle with its source state as the label. -/
def labeledToggleLTS : LTS Bool Bool where
  Tr := fun s label t => label = s ∧ t = !s

/-- States and labels both alternate, with labels equal to source states. -/
theorem labeled_toggle_execution :
    labeledToggleLTS.OmegaExecution ⟨toggleRun⟩ ⟨toggleRun⟩ := by
  intro i
  exact ⟨rfl, rfl⟩

/-- The explicit canonical execution gives a state run without choice. -/
example : labeledToggleLTS.OmegaRun toggleRun :=
  LTS.omegaRun_of_omegaExecution labeled_toggle_execution

/-- Re-selecting labels from the state run recovers the required labels,
not an unrelated constant or relabeling. -/
theorem labeled_toggle_roundtrip :
    ∃ labels : ωSequence Bool,
      labeledToggleLTS.OmegaExecution ⟨toggleRun⟩ labels ∧
        labels = ⟨toggleRun⟩ := by
  obtain ⟨labels, hex⟩ := LTS.omegaExecution_of_omegaRun
    (LTS.omegaRun_of_omegaExecution labeled_toggle_execution)
  refine ⟨labels, hex, ?_⟩
  ext i
  exact (hex i).1

/-- State suffixes and canonical drops agree even without run validity. -/
example (run : ℕ → Bool) (k : ℕ) :
    (⟨Semantics.shiftSeq run k⟩ : ωSequence Bool) =
      (⟨run⟩ : ωSequence Bool).drop k :=
  LTS.shiftSeq_eq_drop run k

end Cslib.CTLStar.Tests
