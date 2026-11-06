/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual octad rows reached by the first sixteen X rows under Norton u. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortUCodeZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Source octad codes reached by the sixteen original X rows. -/
def monsterNortonUOctadCode : Fin 16 → Fin 4096 :=
  ![1106, 339, 349, 3420, 1256, 489, 487, 3558, 1204, 437, 443, 3514, 3342, 2063, 2049, 1024]

/-- Increasing physical positions of the eight coordinates in each reached octad. -/
def monsterNortonUOctadPositions : Fin 16 → Fin 8 → Fin 24 :=
  ![![1, 2, 3, 5, 9, 12, 19, 22],
    ![2, 3, 6, 7, 8, 9, 12, 13],
    ![2, 3, 4, 5, 10, 11, 12, 13],
    ![0, 2, 3, 5, 9, 13, 16, 20],
    ![1, 2, 3, 7, 10, 13, 19, 20],
    ![2, 3, 5, 6, 8, 10, 20, 22],
    ![2, 3, 4, 7, 9, 11, 20, 22],
    ![0, 2, 3, 7, 10, 12, 16, 22],
    ![1, 2, 3, 6, 11, 13, 16, 22],
    ![2, 3, 5, 7, 8, 11, 16, 19],
    ![2, 3, 4, 6, 9, 10, 16, 19],
    ![0, 2, 3, 6, 11, 12, 19, 20],
    ![0, 2, 3, 4, 8, 13, 19, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 8, 9, 10, 11],
    ![1, 2, 3, 4, 8, 12, 16, 20]]

/-- The even local sign labels in the original triality convention. -/
def monsterNortonUOctadSigns : Fin 16 → Fin 64 :=
  ![39, 19, 7, 57, 56, 19, 7, 38, 7, 19, 7, 25, 30, 30, 30, 0]

set_option maxHeartbeats 8000000 in
-- Check all sixteen code masks against the actual published Golay generator table.
/-- Every reached code really is an octad in the original model. -/
theorem monsterNortonUOctad_weight : ∀ j : Fin 16,
    golayMaskWeight (golayEncodedMask (monsterNortonUOctadCode j).val) = 8 := by
  decide +kernel

private theorem positions_mem : ∀ (j : Fin 16) (i : Fin 24),
    i ∈ golayMaskSupport (golayEncodedMask (monsterNortonUOctadCode j).val) ↔
      i ∈ List.ofFn (monsterNortonUOctadPositions j) := by
  decide +kernel

private theorem positions_sorted : ∀ j : Fin 16,
    List.SortedLT (List.ofFn (monsterNortonUOctadPositions j)) := by
  decide +kernel

private theorem positions_sort (j : Fin 16) :
    (golayMaskSupport (golayEncodedMask (monsterNortonUOctadCode j).val)).sort =
      List.ofFn (monsterNortonUOctadPositions j) := by
  apply (golayMaskSupport _).sortedLT_sort.eq_of_mem_iff (positions_sorted j)
  intro i
  simp only [Finset.mem_sort]
  exact positions_mem j i

private theorem positions_idx : ∀ (j : Fin 16) (k : Fin 8),
    (List.ofFn (monsterNortonUOctadPositions j)).idxOf (monsterNortonUOctadPositions j k) =
      k.val := by
  decide +kernel

/-- The finite position tables are exactly the original ordered octad coordinates. -/
theorem monsterNortonUOctad_coordinate (j : Fin 16) (k : Fin 8) :
    golayOctadCoordinate
      (monsterNortonOctadIndex (monsterNortonUOctadCode j) (monsterNortonUOctad_weight j)) k =
        monsterNortonUOctadPositions j k := by
  apply monsterNortonOctadIndex_coordinate
  · intro l
    have h := (positions_mem j (monsterNortonUOctadPositions j l)).mpr (List.mem_ofFn.mpr ⟨l,rfl⟩)
    exact (Finset.mem_filter.mp h).2
  · intro l
    rw [positions_sort]
    exact positions_idx j l

/-- Actual preferred octad labels, retaining their original even-sign coordinates. -/
noncomputable def monsterNortonUOctadOutput (j : Fin 16) : GriessShortIndex :=
  Sum.inr (Sum.inl
    (monsterNortonOctadIndex (monsterNortonUOctadCode j) (monsterNortonUOctad_weight j),
      monsterNortonUOctadSigns j))

set_option maxHeartbeats 16000000 in
-- The 384 parity coordinates use the checked integer inverse of the original Leech basis.
/-- The reached shortest-vector coordinates have exactly these original octad class parities. -/
theorem monsterNortonUOctad_parity : ∀ j : Fin 16,
    integerParity (monsterNortonUFirstCodeShortCoordinates (Fin.castAdd 8 j)) =
      integerParity (monsterNortonLeechCoordinates (monsterNortonOctadIntegral
        (monsterNortonUOctadCode j) (monsterNortonUOctadPositions j)
          (monsterNortonUOctadSigns j))) := by
  decide +kernel

private theorem shortQ_injective : Function.Injective monsterNortonShortQ := by
  intro r s hq
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base) hq
  have hbase (t : GriessShortIndex) : toAdd (griessShortQ t).base =
      leechHyperbolicCoordinates (griessShortClass t) := rfl
  rw [hbase, hbase] at hb
  exact hb

/-- The intrinsic class output is exactly the original triality octad label. -/
theorem monsterNortonUOctad_output_eq (j : Fin 16) :
    monsterNortonUFirstCodeShortOutput (Fin.castAdd 8 j) = monsterNortonUOctadOutput j := by
  have hq : monsterNortonShortQ (monsterNortonUFirstCodeShortOutput (Fin.castAdd 8 j)) =
      monsterNortonShortQ (monsterNortonUOctadOutput j) := by
    rw [monsterNortonUFirstCodeShortOutput, monsterNortonShortIndexOfCoordinates_Q,
      monsterNortonUOctadOutput,
      monsterNortonOctadShortQ_eq _ _ _ (monsterNortonUOctad_coordinate j)]
    rw [monsterNortonUOctad_parity]
  exact shortQ_injective hq

/-- The full actual U short-basis action now uses the original triality-compatible octad labels. -/
theorem monsterNortonUOctad_short_basis (j : Fin 16) :
    localGriessRepresentation monsterNortonUFiber
      (griessConwayDecode (0, (Pi.single (Sum.inr (Sum.inr (0,Fin.castAdd 8 j))) 1, 0))) =
    griessConwayDecode (0, (qSign (monsterNortonUFirstCodeShortPhase (Fin.castAdd 8 j)) •
      Pi.single (monsterNortonUOctadOutput j) (1 : ℝ), 0)) := by
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [← monsterNortonUOctad_output_eq]
  exact monsterNortonUFirstCodeShort_image (Fin.castAdd 8 j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
