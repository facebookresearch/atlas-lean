/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual first seed square proves the six consecutive selected Norton line pairs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Square
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineSeeds

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every consecutive actual source-line ratio inherits the proved first-line square. -/
theorem monsterNortonLine_consecutive_square (i : Fin 13) (hi : i.val + 1 < 13) :
    (y555NortonLine monsterSourceTriality i *
      (y555NortonLine monsterSourceTriality ⟨i.val + 1, hi⟩)⁻¹) ^ 2 = 1 :=
  (monsterNortonLinePair_shift_pow_iff i 1 hi 2).mpr monsterNortonLineZeroOne_square

/-- First chosen vertex of each of the six consecutive source-line pairs. -/
def monsterNortonConsecutiveLineFirst : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 0), (2, 0), (0, 2), (2, 1), (1, 2), (1, 1)]

/-- Second chosen vertex of each of the six consecutive source-line pairs. -/
def monsterNortonConsecutiveLineSecond : Fin 6 → Fin 3 × Fin 3 :=
  ![(1, 0), (0, 2), (2, 1), (1, 2), (1, 1), (0, 1)]

/-- These actual selected labels are distinct consecutive exponents and distinct vertices. -/
theorem monsterNortonConsecutiveLine_labels (q : Fin 6) :
    let a := monsterNortonConsecutiveLineFirst q
    let b := monsterNortonConsecutiveLineSecond q
    (y555NortonLineLabels a.1 a.2).val + 1 = (y555NortonLineLabels b.1 b.2).val ∧ a ≠ b := by
  revert q
  decide +kernel

/-- Each of the six selected consecutive pairs satisfies its actual Norton Coxeter square. -/
theorem monsterNortonCandidate_consecutive_line_square (q : Fin 6) :
    let a := monsterNortonConsecutiveLineFirst q
    let b := monsterNortonConsecutiveLineSecond q
    (y555NortonActualCandidate (monsterNortonLineVertex a.1 a.2) *
      y555NortonActualCandidate (monsterNortonLineVertex b.1 b.2)) ^
      (if y555Adjacent (monsterNortonLineVertex a.1 a.2)
        (monsterNortonLineVertex b.1 b.2) then 3 else 2) = 1 := by
  dsimp only
  let a := monsterNortonConsecutiveLineFirst q
  let b := monsterNortonConsecutiveLineSecond q
  obtain ⟨he, hn⟩ := monsterNortonConsecutiveLine_labels q
  obtain ⟨_, ha⟩ := monsterNortonLine_selected_labels a.1 a.2 b.1 b.2 hn
  rw [ite_eq_right ha]
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [monsterNortonParameter_line, monsterNortonParameter_line]
  have hlt : (y555NortonLineLabels a.1 a.2).val + 1 < 13 := by
    rw [he]
    exact (y555NortonLineLabels b.1 b.2).isLt
  have hl : (⟨(y555NortonLineLabels a.1 a.2).val + 1, hlt⟩ : Fin 13) =
      y555NortonLineLabels b.1 b.2 := Fin.ext he
  simpa only [hl] using monsterNortonLine_consecutive_square (y555NortonLineLabels a.1 a.2) hlt

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
