/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual sparse eighth state, including its matrix and every short component. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthInputIndices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthU

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A C dictionary vector is the sum of the two original signed-pair units. -/
theorem monsterNortonPairShort_C (p : Fin 276) :
    trialityABCBasis 2 p =
      monsterNortonPureShort (Sum.inl (0, p)) +
        monsterNortonPureShort (Sum.inl (1, p)) := by
  rw [monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  simp only [ite_true, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  module

set_option maxRecDepth 10000 in
/-- Each actual C image is the sum of the two checked entire U short-unit images. -/
theorem monsterNortonLine01PairEighth_C (k : Fin 8) :
    y555NortonActualU.val (trialityABCBasis 2 (monsterNortonLine01AdjacentPair k)) =
      monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
        ⟨k.val, by omega⟩) +
      monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
        ⟨8 + k.val, by omega⟩) := by
  rw [monsterNortonPairShort_C, map_add]
  have hs (s : Fin 2) : y555NortonActualU.val
      (monsterNortonPureShort (Sum.inl (s, monsterNortonLine01AdjacentPair k))) =
      monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
        ⟨8 * s.val + k.val, by omega⟩) := by
    rw [← monsterNortonLine01PairEighthInput_pair s k]
    exact monsterNortonLine01PairEighthU_unit _
  have h0 : (⟨8 * (0 : Fin 2).val + k.val, by omega⟩ : Fin 240) =
      ⟨k.val, by omega⟩ := Fin.ext (by simp)
  have h1 : (⟨8 * (1 : Fin 2).val + k.val, by omega⟩ : Fin 240) =
      ⟨8 + k.val, by omega⟩ := Fin.ext (by simp)
  rw [hs 0, hs 1, h0, h1]

/-- All actual eighth-state short summands, with their original phase-complete coefficients. -/
noncomputable def monsterNortonLine01PairEighthShortPacket : GriessSpace :=
  (∑ k : Fin 8, (-1 / 16 : ℝ) •
    (monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput ⟨k.val, by omega⟩) +
      monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
        ⟨8 + k.val, by omega⟩))) +
  ∑ a : Fin 14, ∑ j : Fin 16,
    ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
      monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
        ⟨16 + 16 * a.val + j.val, by omega⟩)

set_option maxRecDepth 10000 in
/-- Literal U sends the entire seventh vector to the full matrix and 240-short-unit packet. -/
theorem monsterNortonLine01PairEighth_sparse :
    y555NortonActualU.val monsterNortonLine01PairAfterSeventh =
      (∑ k : Fin 8, ((monsterNortonLine01PairSeventhMatrixNumerator k : ℝ) / 16) •
        griessConwayDecode
          (conwayMatrixAction monsterNortonUFiber.val.2
            (trialityPairMatrix (monsterNortonLine01AdjacentPair k)), (0, 0))) +
      monsterNortonLine01PairEighthShortPacket := by
  rw [monsterNortonLine01PairSeventh_expansion_compact]
  simp only [map_add, map_sum, map_smul, monsterNortonU_pair_matrix,
    monsterNortonLine01PairEighth_C]
  rw [add_assoc]
  have ho : (∑ a : Fin 14, ∑ j : Fin 16,
      ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
        y555NortonActualU.val (monsterNortonPureShort (Sum.inr (Sum.inl
          (monsterNortonLine01PairBlockOctad a,
            monsterNortonLine01PairSeventhOctadSupport a j))))) =
      ∑ a : Fin 14, ∑ j : Fin 16,
        ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
          monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput
            ⟨16 + 16 * a.val + j.val, by omega⟩) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    rw [← monsterNortonLine01PairEighthInput_octad a j,
      monsterNortonLine01PairEighthU_unit]
  rw [ho]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
