/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite candidate columns for a coordinate stabilizer chain in the diagonal form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact quadratic value of the independent finite diagonal form. -/
def y322Orthogonal3DiagonalNorm (v : Fin 7 → ZMod 3) : ZMod 3 :=
  ∑ i : Fin 7, y322Orthogonal3DiagonalWeight i * v i * v i

/-- Candidate columns have zero later coordinates and the actual norm of their last basis column. -/
def y322Orthogonal3DiagonalCandidateProperty (i : Fin 7) (v : Fin 7 → ZMod 3) : Prop :=
  (∀ j : Fin 7, i.val < j.val → v j = 0) ∧
    y322Orthogonal3DiagonalNorm v = y322Orthogonal3DiagonalWeight i

/-- The actual finite-coordinate candidate condition is decidable. -/
instance y322Orthogonal3DiagonalCandidatePropertyDecidable (i : Fin 7) (v : Fin 7 → ZMod 3) :
    Decidable (y322Orthogonal3DiagonalCandidateProperty i v) := by
  unfold y322Orthogonal3DiagonalCandidateProperty
  infer_instance

/-- The independent finite norm level with its required zero later coordinates. -/
abbrev Y322Orthogonal3DiagonalCandidate (i : Fin 7) :=
  {v : Fin 7 → ZMod 3 // y322Orthogonal3DiagonalCandidateProperty i v}

/-- Exact candidate counts for successive dimensions of the independent diagonal form. -/
def y322Orthogonal3DiagonalCandidateCount : Fin 7 → ℕ := ![2, 4, 6, 30, 72, 252, 702]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Each independent finite candidate type has at most 2187 underlying field vectors.
/-- All seven finite coordinate candidate types have their exact checked cardinalities. -/
theorem y322Orthogonal3DiagonalCandidate_card (i : Fin 7) :
    Fintype.card (Y322Orthogonal3DiagonalCandidate i) =
      y322Orthogonal3DiagonalCandidateCount i := by
  fin_cases i <;> decide +kernel

/-- The product of the seven exact coordinate candidate bounds is 18341406720. -/
theorem y322Orthogonal3DiagonalCandidateCount_product :
    (∏ i : Fin 7, y322Orthogonal3DiagonalCandidateCount i) = 18341406720 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
