/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original C522 relations and proved redundant-F1 source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522AuxGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact lexicographic numbering of all forty-five distinct original C522 generator pairs. -/
def y522AuxOriginalPair : Fin 45 → Fin 10 × Fin 10 :=
  ![
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 6),
    (0, 7),
    (0, 8),
    (0, 9),
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (1, 6),
    (1, 7),
    (1, 8),
    (1, 9),
    (2, 3),
    (2, 4),
    (2, 5),
    (2, 6),
    (2, 7),
    (2, 8),
    (2, 9),
    (3, 4),
    (3, 5),
    (3, 6),
    (3, 7),
    (3, 8),
    (3, 9),
    (4, 5),
    (4, 6),
    (4, 7),
    (4, 8),
    (4, 9),
    (5, 6),
    (5, 7),
    (5, 8),
    (5, 9),
    (6, 7),
    (6, 8),
    (6, 9),
    (7, 8),
    (7, 9),
    (8, 9)]

/-- Every numbered original pair is a pair of distinct actual original vertices. -/
theorem y522AuxOriginalPair_distinct (i : Fin 45) :
    (y522AuxOriginalPair i).1 ≠ (y522AuxOriginalPair i).2 := by
  revert i
  decide +kernel

/-- The literal original C522 spider power in the actual redundant alphabet. -/
def y522AuxSpiderWord : List (Fin 11) :=
  (List.replicate 10 [0, 1, 2, 0, 5, 6, 0, 7, 8]).flatten

/-- The literal source spider power holds by the original independent Y555 relation. -/
theorem y522AuxSpiderWord_value : y522AuxPositiveWord y522AuxSpiderWord = 1 := by
  rw [y522AuxSpiderWord, y522AuxPositiveWord_replicate]
  have h := PresentedGroup.one_of_mem (rels := y555Relations)
    (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
  simpa [y555Spider, y522AuxPositiveWord, y522AuxGenerator, y522Vertex,
    PresentedGroup.of, map_pow, map_mul, mul_assoc] using h

/-- Exact original pairs and spider, two proved F1 definitions, commutations, and cubic. -/
def y522AuxRelatorWord (r : Fin 58) : List (Fin 11) :=
  if h : r.val < 45 then
    let pair := y522AuxOriginalPair ⟨r.val, h⟩
    let exponent := if y555Adjacent (y522Vertex pair.1) (y522Vertex pair.2) then 3 else 2
    (List.replicate exponent
      [y522AuxOriginalLetter pair.1, y522AuxOriginalLetter pair.2]).flatten
  else if r.val = 45 then y522AuxSpiderWord
  else if r.val = 46 then [10] ++ y522AuxF12Word.reverse
  else if r.val = 47 then [10] ++ y522AuxF13Word.reverse
  else if h : r.val < 57 then
    let g := y522AuxOriginalLetter (y522AuxNonE1 ⟨r.val - 48, by omega⟩)
    [10, g, 10, g]
  else [10, 4, 10, 4, 10, 4]

/-- Every replay relator is proved inside the original independent Y555 group. -/
theorem y522AuxRelatorWord_valid (r : Fin 58) :
    y522AuxPositiveWord (y522AuxRelatorWord r) = 1 := by
  unfold y522AuxRelatorWord
  split
  · dsimp only
    rw [y522AuxPositiveWord_replicate]
    simpa only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, y522AuxGenerator_original] using
      y555_coxeter_relation
        (y522Vertex (y522AuxOriginalPair ⟨r.val, ‹r.val < 45›⟩).1)
        (y522Vertex (y522AuxOriginalPair ⟨r.val, ‹r.val < 45›⟩).2)
        (fun h => y522AuxOriginalPair_distinct ⟨r.val, ‹r.val < 45›⟩
          (y522Vertex_injective h))
  · split
    · exact y522AuxSpiderWord_value
    · split
      · rw [y522AuxPositiveWord_append, y522AuxPositiveWord_reverse, y522AuxF12Word_value]
        simp only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, mul_one, y522AuxGenerator_ten, mul_inv_cancel]
      · split
        · rw [y522AuxPositiveWord_append, y522AuxPositiveWord_reverse, y522AuxF13Word_value]
          simp only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil, mul_one, y522AuxGenerator_ten, mul_inv_cancel]
        · split
          · dsimp only
            have h := y555Source_commuting_square _ _
              (y522AuxGenerator_ten_commute (⟨r.val - 48, by omega⟩ : Fin 9))
              (by simpa only [pow_two] using y522AuxGenerator_square 10)
              (by simpa only [pow_two] using (y522AuxGenerator_square
                (y522AuxOriginalLetter (y522AuxNonE1 ⟨r.val - 48, by omega⟩))))
            simpa only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
              List.prod_nil, mul_one, pow_two, mul_assoc] using h
          · have hg : y522AuxGenerator 4 =
                (PresentedGroup.of (some (0, 3)) : BimonsterPresentation) := rfl
            simpa only [y522AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
              List.prod_nil, y522AuxGenerator_ten, hg, pow_succ, pow_zero, one_mul,
              mul_one, mul_assoc] using y555LocalF1_e1_cube

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
