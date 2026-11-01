/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Eight missing genuine octad-three inputs needed by the inverse half-word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPool

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The eight original signs absent from the common candidate input pool. -/
def monsterNortonOctadThreeSupplementInputSign : Fin 8 → Fin 64 :=
  ![6, 9, 19, 28, 32, 47, 53, 58]

/-- The actual output source code in the common verified octad dictionary. -/
def monsterNortonOctadThreeSupplementOutputChoice : Fin 8 → Fin 50 :=
  ![33, 4, 4, 33, 33, 4, 4, 33]

/-- The actual preferred original output sign. -/
def monsterNortonOctadThreeSupplementOutputSign : Fin 8 → Fin 64 :=
  ![1, 16, 6, 12, 61, 31, 9, 48]

/-- The complete original positive input Q mask. -/
def monsterNortonOctadThreeSupplementInputMask : Fin 8 → ℕ :=
  ![4405251, 210947, 5713923, 1519619, 8337411, 4143107, 7024643, 2830339]

/-- The original integral lattice coordinate parity. -/
def monsterNortonOctadThreeSupplementInputParity : Fin 8 → ℕ :=
  ![63871, 63856, 63787, 63780, 63769, 63766, 63821, 63810]

/-- The signed shortest-vector representative scalar. -/
def monsterNortonOctadThreeSupplementPhysicalSign : Fin 8 → ℤ :=
  ![1, 1, 1, 1, -1, -1, 1, 1]

/-- The full original preferred input label, using the verified source code three. -/
noncomputable def monsterNortonOctadThreeSupplementInput (i : Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inl (monsterNortonOctadIndex (monsterNortonPairHalfUPoolOctadCode 0)
    (monsterNortonPairHalfUPoolOctad_weight 0), monsterNortonOctadThreeSupplementInputSign i))

/-- The full original preferred output label, retaining its original source sign. -/
noncomputable def monsterNortonOctadThreeSupplementOutput (i : Fin 8) : GriessShortIndex :=
  Sum.inr (Sum.inl
    (monsterNortonOctadIndex
      (monsterNortonPairHalfUPoolOctadCode (monsterNortonOctadThreeSupplementOutputChoice i))
      (monsterNortonPairHalfUPoolOctad_weight (monsterNortonOctadThreeSupplementOutputChoice i)),
      monsterNortonOctadThreeSupplementOutputSign i))

/-- Exact integer physical input coordinates. -/
def monsterNortonOctadThreeSupplementInputIntegral (i : Fin 8) : Fin 24 → ℤ :=
  monsterNortonOctadIntegral (monsterNortonPairHalfUPoolOctadCode 0)
    (monsterNortonPairHalfUPoolOctadPositions 0) (monsterNortonOctadThreeSupplementInputSign i)

/-- Exact integer physical output coordinates. -/
def monsterNortonOctadThreeSupplementOutputIntegral (i : Fin 8) : Fin 24 → ℤ :=
  monsterNortonOctadIntegral
    (monsterNortonPairHalfUPoolOctadCode (monsterNortonOctadThreeSupplementOutputChoice i))
    (monsterNortonPairHalfUPoolOctadPositions (monsterNortonOctadThreeSupplementOutputChoice i))
    (monsterNortonOctadThreeSupplementOutputSign i)

/-- The input integer table is the entire actual preferred shortest vector. -/
theorem monsterNortonOctadThreeSupplementInputIntegral_actual (i : Fin 8) :
    griessShortIntegral (monsterNortonOctadThreeSupplementInput i) =
      monsterNortonOctadThreeSupplementInputIntegral i :=
  monsterNortonOctadIntegral_eq _ _ _ (monsterNortonPairHalfUPoolOctad_coordinate 0) _

/-- The output integer table is the entire actual preferred shortest vector. -/
theorem monsterNortonOctadThreeSupplementOutputIntegral_actual (i : Fin 8) :
    griessShortIntegral (monsterNortonOctadThreeSupplementOutput i) =
      monsterNortonOctadThreeSupplementOutputIntegral i :=
  monsterNortonOctadIntegral_eq _ _ _
    (monsterNortonPairHalfUPoolOctad_coordinate (monsterNortonOctadThreeSupplementOutputChoice i)) _

set_option maxHeartbeats 8000000 in
-- Check all original integer coordinate equations for the eight additional inputs.
/-- Actual U transports every supplemental physical vector to its signed output. -/
theorem monsterNortonOctadThreeSupplementPhysical_certificate (i : Fin 8) (j : Fin 24) :
    (monsterNortonUNumerator1 *ᵥ monsterNortonOctadThreeSupplementInputIntegral i) j =
      4 * monsterNortonOctadThreeSupplementPhysicalSign i *
        monsterNortonOctadThreeSupplementOutputIntegral i j := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
