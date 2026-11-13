/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The three conversion proofs below are adapted from
fairinternal/formal-math, CSLibExt/Foundations/Semantics/LTS/CslibBridge.lean,
commit cbe67c4f99b625a43c98959d53f88f7b137d7119 (PR 10058).
Original formalization by Adam Kiezun.
-/
module

public import CSLibExt.Foundations.Semantics.LTS.OmegaRun
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# State runs and canonical labeled executions

Both presentations use the same `Cslib.LTS` and its `Tr` relation.
Selecting labels from an abstract state run uses `Classical.choice`;
forgetting labels uses the supplied witnesses, with no new selection.
Canonical omega-sequence coercions also carry standard classical axioms
in their dependency closure. No constructive algorithm, alternative LTS
record, or historical compatibility aliases are introduced.
-/

@[expose] public section

namespace Cslib.LTS

variable {State Label : Type*} {lts : LTS State Label}

/-- Select a witnessing label at each step of an infinite state run. -/
theorem omegaExecution_of_omegaRun {ss : ℕ → State}
    (h : lts.OmegaRun ss) :
    ∃ μs : ωSequence Label, lts.OmegaExecution ⟨ss⟩ μs := by
  refine ⟨⟨fun i => Classical.choose (h i)⟩, ?_⟩
  intro i
  exact Classical.choose_spec (h i)

/-- Forget the labels of a canonical infinite execution. -/
theorem omegaRun_of_omegaExecution {oss : ωSequence State}
    {μs : ωSequence Label} (h : lts.OmegaExecution oss μs) :
    lts.OmegaRun (fun i => oss i) := by
  intro i
  exact ⟨μs i, h i⟩

/-- Function-sequence suffixes agree with canonical `ωSequence.drop`. -/
theorem shiftSeq_eq_drop (ss : ℕ → State) (k : ℕ) :
    (⟨Semantics.shiftSeq ss k⟩ : ωSequence State) =
      ωSequence.drop k ⟨ss⟩ := by
  ext i
  rfl

end Cslib.LTS
