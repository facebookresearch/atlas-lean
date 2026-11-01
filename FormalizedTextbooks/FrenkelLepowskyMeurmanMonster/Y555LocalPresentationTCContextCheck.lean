/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact replay predicate for the literal independent C322 contextual equation derivation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Replay an actual TC equation using solely literal source equations and earlier equations. -/
def y322TCContextCheckAt (index : ℕ) : Prop :=
  if h : index < 28530 then
    y322ContextEquationProgramChecked (y322FiniteEquationSource y322TransportProgram)
      y322TCContextProgram ⟨index, h⟩
  else True

/-- The literal source-equation and contextual substitution replay is decidable. -/
instance y322TCContextCheckAtDecidable (index : ℕ) : Decidable (y322TCContextCheckAt index) := by
  unfold y322TCContextCheckAt
  split
  · unfold y322ContextEquationProgramChecked
    split
    · unfold y322EquationsSameReduction
      infer_instance
    · infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
