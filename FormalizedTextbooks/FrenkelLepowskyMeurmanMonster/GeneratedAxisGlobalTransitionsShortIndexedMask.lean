/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortSparseMask
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadIndexed

/-! Direct indexed evaluation of the entire original preferred short-Q dictionary. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The same original preferred mask using exact constant-width octad catalogue extraction. -/
def generatedAxisGlobalShortIndexedMask : GriessShortIndex → ℕ
  | Sum.inr (Sum.inl (j, e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedAxisGlobalOctadIndexedCode j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (parkerThetaMask (generatedAxisGlobalOctadIndexedCode j).val)
        (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadIndexedCoordinate j)
          (trialityEvenMask e)))
  | r => generatedAxisGlobalShortSparseMask r

/-- Indexed extraction yields exactly the full original sparse mask, on every short coordinate. -/
theorem generatedAxisGlobalShortIndexedMask_eq (r : GriessShortIndex) :
    generatedAxisGlobalShortIndexedMask r = generatedAxisGlobalShortSparseMask r := by
  rcases r with p | (⟨j, e⟩ | p)
  · rfl
  · have hc : generatedAxisGlobalOctadIndexedCoordinate j =
        generatedAxisGlobalOctadCoordinatesData j := by
      funext k
      exact generatedAxisGlobalOctadIndexedCoordinate_actual j k
    simp only [generatedAxisGlobalShortIndexedMask, generatedAxisGlobalShortSparseMask,
      generatedAxisGlobalOctadIndexedCode_actual, hc]
  · rfl

/-- Every indexed word is the entire actual preferred lift, with its original central section. -/
theorem generatedAxisGlobalShortIndexedMask_Q_actual (r : GriessShortIndex) :
    generatedAxisGlobalShortQFinite r =
      generatedAxisGlobalQMask (generatedAxisGlobalShortIndexedMask r) := by
  rw [generatedAxisGlobalShortIndexedMask_eq]
  exact generatedAxisGlobalShortSparseMask_Q_actual r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
