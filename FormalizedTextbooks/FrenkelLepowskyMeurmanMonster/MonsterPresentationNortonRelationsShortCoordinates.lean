/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Computable preferred short-Q labels from the genuine integral Leech basis. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative

/-- Eight times the inverse of the actual displayed integer Leech basis matrix. -/
def monsterNortonLeechInverseEight : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![1, -1, -1, -1, -1, -1, -1, 5, -1, -1, -1, 5, -1, 5, 5, 5, -1, 7, 5, 7, 7, 5, 7, -57],
  ![0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, -2, 0, -2, 0, 0, 0, -2, 0, 0, -2, -2, -2, 12],
  ![0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, -2, -2, -2, 0, 10],
  ![0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, -2, 0, -2, -2, -2, -2, 0, 0, 12],
  ![0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, -2, -2, -2, 0, -2, 12],
  ![0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0, 0, -2, 0, -2, 0, -2, -2, 0, 0, 0, -2, 10],
  ![0, 0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, -2, -2, 0, -2, 0, -2, 0, -2, -2, 12],
  ![0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, -2, -2, 0, 0, -2, -2, 0, -2, 0, 0, 10],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, -2, 0, -2, 0, -2, 0, -2, 0, -2, 0, 10],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, 0, 0, -2, -2, 0, 0, -2, -2, 0, 0, -2, 10],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, 0, 0, 0, 0, -2, -2, -2, 10],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -2, -2, -2, -2, -2, 10],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]]

set_option maxHeartbeats 16000000 in
-- All 576 integer entries verify this inverse using the genuine repository basis.
/-- The finite certificate proves the displayed rational inverse exactly. -/
theorem monsterNortonLeechInverseEight_certificate :
    monsterNortonLeechInverseEight * leechBasisMatrix = 8 • (1 : Matrix (Fin 24) (Fin 24) ℤ) := by
  decide +kernel

/-- Computable actual lattice coordinates, using exact division by eight. -/
def monsterNortonLeechCoordinates (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => (monsterNortonLeechInverseEight *ᵥ u) i / 8

/-- On genuine lattice vectors this computation equals the actual coordinate equivalence. -/
theorem monsterNortonLeechCoordinates_eq (u : leechIntegral) :
    monsterNortonLeechCoordinates u.val = leechExplicitCoordinates u := by
  have h := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℤ =>
    M *ᵥ leechExplicitCoordinates u) monsterNortonLeechInverseEight_certificate
  rw [← Matrix.mulVec_mulVec, leechExplicitCoordinates_vector] at h
  funext i
  have hi := congrFun h i
  simp only [monsterNortonLeechCoordinates]
  rw [hi]
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]

/-- The preferred short lift in Q is now expressed by finite integer and binary arithmetic. -/
def monsterNortonShortQ (r : GriessShortIndex) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (griessShortIntegral r))), 1⟩

/-- This computable preferred label is exactly the intrinsic actual short lift. -/
theorem monsterNortonShortQ_eq (r : GriessShortIndex) :
    monsterNortonShortQ r = griessShortQ r := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change leechHyperbolicInverse *ᵥ integerParity
      (monsterNortonLeechCoordinates (griessShortIntegral r)) =
        leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r))
    rw [leechHyperbolicCoordinates_explicit]
    exact congrArg (fun v => leechHyperbolicInverse *ᵥ integerParity v)
      (monsterNortonLeechCoordinates_eq (griessShortLatticeVector r))
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
