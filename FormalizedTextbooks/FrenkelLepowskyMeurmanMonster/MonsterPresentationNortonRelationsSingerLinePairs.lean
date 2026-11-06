/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Nineteen selected actual line-pair Coxeter relations from the proved Singer distance orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSeeds

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Every actual first-line distance in the proved Singer orbit has square one. -/
theorem monsterNortonSinger_line_seed_square (d : Fin 13)
    (hd : d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 9 ∨ d = 10 ∨ d = 12) :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality d)⁻¹) ^ 2 = 1 := by
  rcases hd with h | h | h | h | h | h <;> subst d
  · exact monsterNortonLineZeroOne_square
  · exact monsterNortonLineZeroThree_square
  · exact monsterNortonLineZeroFour_square
  · exact monsterNortonLineZeroNine_square
  · exact (monsterNortonLine_distance_complement 3 (by decide) 2).mp
      monsterNortonLineZeroThree_square
  · exact (monsterNortonLine_distance_complement 1 (by decide) 2).mp
      monsterNortonLineZeroOne_square

/-- The source line labels on the left of the nineteen proved selected pairs. -/
def monsterNortonSingerPairLeft : Fin 19 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 0), (0, 0), (0, 0), (1, 0), (1, 0), (1, 0), (2, 0), (2, 0), (2, 0), (0, 2), (0,
    2), (0, 2), (2, 1), (2, 1), (1, 2), (1, 2), (1, 1), (1, 1)]

/-- The source line labels on the right of those nineteen proved selected pairs. -/
def monsterNortonSingerPairRight : Fin 19 → Fin 3 × Fin 3 :=
  ![(1, 0), (2, 0), (0, 2), (2, 2), (0, 2), (2, 1), (2, 2), (0, 2), (1, 2), (1, 1), (2, 1), (1,
    1), (0, 1), (1, 2), (0, 1), (1, 1), (2, 2), (0, 1), (2, 2)]

private theorem selected_pair_certificate (q : Fin 19) :
    let a := monsterNortonSingerPairLeft q
    let b := monsterNortonSingerPairRight q
    (y555NortonLineLabels a.1 a.2).val < (y555NortonLineLabels b.1 b.2).val ∧
      ((y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 1 ∨
       (y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 3 ∨
       (y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 4 ∨
       (y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 9 ∨
       (y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 10 ∨
       (y555NortonLineLabels b.1 b.2).val - (y555NortonLineLabels a.1 a.2).val = 12) := by
  revert q
  decide +kernel

/-- These nineteen selected actual Norton line pairs satisfy their genuine Coxeter square. -/
theorem monsterNortonCandidate_Singer_line_square (q : Fin 19) :
    (y555NortonActualCandidate (monsterNortonLineVertex
      (monsterNortonSingerPairLeft q).1 (monsterNortonSingerPairLeft q).2) *
      y555NortonActualCandidate (monsterNortonLineVertex
        (monsterNortonSingerPairRight q).1 (monsterNortonSingerPairRight q).2)) ^ 2 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [monsterNortonParameter_line, monsterNortonParameter_line]
  let i := y555NortonLineLabels (monsterNortonSingerPairLeft q).1
    (monsterNortonSingerPairLeft q).2
  let j := y555NortonLineLabels (monsterNortonSingerPairRight q).1
    (monsterNortonSingerPairRight q).2
  obtain ⟨hlt, hd⟩ := selected_pair_certificate q
  change i.val < j.val at hlt
  let d : Fin 13 := ⟨j.val - i.val, by omega⟩
  have hseed : d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 9 ∨ d = 10 ∨ d = 12 := by
    change d.val = 1 ∨ d.val = 3 ∨ d.val = 4 ∨ d.val = 9 ∨
      d.val = 10 ∨ d.val = 12 at hd
    rcases hd with h | h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))
  have hadd : i.val + d.val < 13 := by dsimp [d]; omega
  have hj : (⟨i.val + d.val, hadd⟩ : Fin 13) = j := Fin.ext (by dsimp [d]; omega)
  have hp := (monsterNortonLinePair_shift_pow_iff i d hadd 2).mpr
    (monsterNortonSinger_line_seed_square d hseed)
  simpa only [hj] using hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
