/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual short-coordinate transport of all 24 first-code X rows by the full Norton u word.
Output labels are the actual short-class inverse of certified norm32 lattice vectors,
so the proof never evaluates a noncomputable dictionary enumeration. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortFromVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Genuine integral-basis coordinates of the 24 reached short classes. -/
def monsterNortonUFirstCodeShortCoordinates : Fin 24 → Fin 24 → ℤ :=
  ![![4, -1, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0,
      -1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0],
    ![3, -1, -1, -1, -1, -1, 0, 1, -1, 0, 0, 0,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![3, -1, -1, -1, -1, 0, 0, 0, -1, -1, 0, 1,
      -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![3, -1, -1, -1, -1, -1, -1, 1, 0, -1, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0],
    ![3, -1, -1, -1, -1, -1, -1, 1, 0, 0, -1, 1,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0],
    ![4, -1, -1, -1, -1, -1, -1, 1, 0, 0, 0, 0,
      -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
    ![5, -2, -1, -1, -1, -1, 0, 0, -1, -1, -1, 1,
      -1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
    ![5, -1, -2, -2, -1, 0, -1, 1, -1, -1, -1, 1,
      0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0],
    ![2, 0, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0],
    ![2, 0, -1, -1, 0, 0, 0, 0, 0, -1, -1, 1,
      0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0],
    ![6, -1, -1, -1, -2, -1, -1, 0, -1, -1, -1, 0,
      -1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0],
    ![2, -1, -1, -1, -1, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, -1, -1, -1, 0, 0, 0, 0, -1, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![7, -2, -2, -1, -2, -1, -1, 1, -1, -1, -1, 1,
      -1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 1, -1],
    ![-3, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0,
      1, 0, 0, 0, 1, 0, 0, 0, -1, -2, 0, 1],
    ![-3, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0,
      1, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 1],
    ![-3, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0,
      0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 0, 1],
    ![7, -2, -1, -2, -2, -1, -1, 1, -1, -1, -1, 1,
      -1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 1, -1],
    ![-3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
      1, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 1],
    ![28, -6, -5, -6, -6, -5, -6, 2, -5, -5, -5, 2,
      -5, 2, 2, 2, -5, 2, 2, 2, 1, 2, 2, -3],
    ![-4, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0,
      0, 0, 0, 0, 1, -2, 0, 0, -1, 0, 0, 1]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Actual multiplication by the integer Leech basis checks the norm of every stated vector.
/-- Every displayed coordinate vector is an actual shortest lattice vector. -/
theorem monsterNortonUFirstCodeShort_norm (j : Fin 24) :
    leechSquareSum (leechBasisMatrix *ᵥ monsterNortonUFirstCodeShortCoordinates j) = 32 := by
  fin_cases j <;> decide +kernel

/-- The actual short dictionary labels of these certified lattice classes. -/
noncomputable def monsterNortonUFirstCodeShortOutput (j : Fin 24) : GriessShortIndex :=
  monsterNortonShortIndexOfCoordinates (monsterNortonUFirstCodeShortCoordinates j)
    (monsterNortonUFirstCodeShort_norm j)

/-- The full source word's central phase, before forgetting the preferred short section. -/
noncomputable def monsterNortonUFirstCodeShortPhase (j : Fin 24) : ZMod 2 :=
  toAdd (monsterNortonUQImage (monsterNortonShortQ (Sum.inr (Sum.inr (0,j))))).coeff

set_option maxRecDepth 10000 in
set_option maxHeartbeats 40000000 in
-- Each of 24 short rows checks all 24 bits through the actual seven-factor Norton Q action.
/-- The certified integer lattice coordinates have the full word's actual binary images. -/
theorem monsterNortonUFirstCodeShort_binary (j : Fin 24) : ∀ i : Fin 24,
    toAdd (monsterNortonUQImage (monsterNortonShortQ (Sum.inr (Sum.inr (0,j))))).base i =
      (leechHyperbolicInverse *ᵥ integerParity (monsterNortonUFirstCodeShortCoordinates j)) i := by
  fin_cases j <;> decide +kernel

/-- Full Q transport includes the exact central phase of each preferred short label. -/
theorem monsterNortonUFirstCodeShort_image (j : Fin 24) :
    spinConjugation monsterNortonUFiber.val.1 (monsterNortonShortQ (Sum.inr (Sum.inr (0,j)))) =
      qCentral (monsterNortonUFirstCodeShortPhase j) *
        monsterNortonShortQ (monsterNortonUFirstCodeShortOutput j) := by
  rw [monsterNortonUQImage_eq, monsterNortonUFirstCodeShortOutput,
    monsterNortonShortIndexOfCoordinates_Q]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    apply toAdd.injective
    funext i
    exact monsterNortonUFirstCodeShort_binary j i
  · apply toAdd.injective
    rw [qCentral_mul_coeff]
    change monsterNortonUFirstCodeShortPhase j = monsterNortonUFirstCodeShortPhase j + 0
    rw [add_zero]

/-- Every first-code X row has this genuine full-Norton short-coordinate action. -/
theorem monsterNortonUFirstCodeShort_operator (j : Fin 24) (X : GriessShortIndex → ℝ) :
    localShortOperator monsterNortonUFiber X (monsterNortonUFirstCodeShortOutput j) =
      qSign (monsterNortonUFirstCodeShortPhase j) * X (Sum.inr (Sum.inr (0,j))) := by
  exact monsterNortonShortOperator_of_Q_image _ _ _ _ (monsterNortonUFirstCodeShort_image j) X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
