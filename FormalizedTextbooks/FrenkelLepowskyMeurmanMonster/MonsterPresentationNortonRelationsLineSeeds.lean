/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Six actual first-line distances suffice for every selected Norton line-pair relation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLinePeriod

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero actual line distance follows from six first-line seed powers. -/
theorem monsterNortonLine_distance_of_six_seeds (k : ℕ)
    (hs : ∀ d : Fin 6, (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality ⟨d.val + 1, by omega⟩)⁻¹) ^ k = 1)
    (d : Fin 13) (hd : d ≠ 0) :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality d)⁻¹) ^ k = 1 := by
  have hd0 : d.val ≠ 0 := fun h => hd (Fin.ext h)
  by_cases h : d.val ≤ 6
  · let e : Fin 6 := ⟨d.val - 1, by omega⟩
    have he : (⟨e.val + 1, by omega⟩ : Fin 13) = d := Fin.ext (by dsimp [e]; omega)
    simpa only [he] using hs e
  · let e : Fin 6 := ⟨12 - d.val, by omega⟩
    have he : (⟨e.val + 1, by omega⟩ : Fin 13) =
        ⟨13 - d.val, by omega⟩ := Fin.ext (by dsimp [e]; omega)
    apply (monsterNortonLine_distance_complement d hd k).mpr
    simpa only [he] using hs e

/-- The six actual seed powers imply every distinct actual Norton line-ratio power. -/
theorem monsterNortonLine_pairs_of_six_seeds (k : ℕ)
    (hs : ∀ d : Fin 6, (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality ⟨d.val + 1, by omega⟩)⁻¹) ^ k = 1)
    (i j : Fin 13) (hij : i ≠ j) :
    (y555NortonLine monsterSourceTriality i *
      (y555NortonLine monsterSourceTriality j)⁻¹) ^ k = 1 := by
  have sorted (i j : Fin 13) (h : i.val < j.val) :
      (y555NortonLine monsterSourceTriality i *
        (y555NortonLine monsterSourceTriality j)⁻¹) ^ k = 1 := by
    let d : Fin 13 := ⟨j.val - i.val, by omega⟩
    have hd : d ≠ 0 := by intro he; have hx := congrArg Fin.val he; dsimp [d] at hx; omega
    have hadd : i.val + d.val < 13 := by dsimp [d]; omega
    have hj : (⟨i.val + d.val, hadd⟩ : Fin 13) = j := Fin.ext (by dsimp [d]; omega)
    have hs' := (monsterNortonLinePair_shift_pow_iff i d hadd k).mpr
      (monsterNortonLine_distance_of_six_seeds k hs d hd)
    simpa only [hj] using hs'
  by_cases h : i.val < j.val
  · exact sorted i j h
  · have hji : j.val < i.val := by
      have hn : i.val ≠ j.val := fun he => hij (Fin.ext he)
      omega
    have he : (y555NortonLine monsterSourceTriality j *
        (y555NortonLine monsterSourceTriality i)⁻¹)⁻¹ =
        y555NortonLine monsterSourceTriality i *
          (y555NortonLine monsterSourceTriality j)⁻¹ := by group
    rw [← he, inv_pow, sorted j i hji, inv_one]

/-- All chosen line vertices have distinct source labels and are mutually nonadjacent. -/
theorem monsterNortonLine_selected_labels (a b c d : Fin 3)
    (hne : (a, b) ≠ (c, d)) :
    y555NortonLineLabels a b ≠ y555NortonLineLabels c d ∧
      ¬ y555Adjacent (monsterNortonLineVertex a b) (monsterNortonLineVertex c d) := by
  revert a b c d
  decide +kernel

/-- Six concrete actual-group seed squares imply all thirty-six chosen line Coxeter relations. -/
theorem monsterNortonCandidate_line_line_of_six_seeds
    (hs : ∀ d : Fin 6, (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality ⟨d.val + 1, by omega⟩)⁻¹) ^ 2 = 1)
    (a b c d : Fin 3) (hne : (a, b) ≠ (c, d)) :
    (y555NortonActualCandidate (monsterNortonLineVertex a b) *
      y555NortonActualCandidate (monsterNortonLineVertex c d)) ^
        (if y555Adjacent (monsterNortonLineVertex a b) (monsterNortonLineVertex c d)
          then 3 else 2) = 1 := by
  obtain ⟨hl, ha⟩ := monsterNortonLine_selected_labels a b c d hne
  rw [ite_eq_right ha]
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [monsterNortonParameter_line, monsterNortonParameter_line]
  exact monsterNortonLine_pairs_of_six_seeds 2 hs _ _ hl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
