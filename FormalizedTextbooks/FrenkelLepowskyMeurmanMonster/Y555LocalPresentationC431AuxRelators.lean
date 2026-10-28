/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original Coxeter relators and proved redundant-symbol relations for the C431 replay. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Lexicographic numbering of all thirty-six distinct original C431 generator pairs. -/
def y431AuxOriginalPair : Fin 36 → Fin 9 × Fin 9 :=
  ![
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (0, 5),
    (0, 6),
    (0, 7),
    (0, 8),
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (1, 6),
    (1, 7),
    (1, 8),
    (2, 3),
    (2, 4),
    (2, 5),
    (2, 6),
    (2, 7),
    (2, 8),
    (3, 4),
    (3, 5),
    (3, 6),
    (3, 7),
    (3, 8),
    (4, 5),
    (4, 6),
    (4, 7),
    (4, 8),
    (5, 6),
    (5, 7),
    (5, 8),
    (6, 7),
    (6, 8),
    (7, 8)]

/-- Every numbered original pair consists of distinct actual source vertices. -/
theorem y431AuxOriginalPair_distinct (i : Fin 36) :
    (y431AuxOriginalPair i).1 ≠ (y431AuxOriginalPair i).2 := by
  revert i
  decide +kernel

/-- Exact positive words for original pairs, the F21 definition, and nine proved commutations. -/
def y431AuxRelatorWord (r : Fin 46) : List (Fin 10) :=
  if h : r.val < 36 then
    let pair := y431AuxOriginalPair ⟨r.val, h⟩
    let exponent := if y555Adjacent (y431Vertex pair.1) (y431Vertex pair.2) then 3 else 2
    (List.replicate exponent
      [y431AuxOriginalLetter pair.1, y431AuxOriginalLetter pair.2]).flatten
  else if r.val = 36 then [9] ++ y431E7Positive21.reverse.map y431AuxOriginalLetter
  else
    let g : Fin 9 := ⟨r.val - 37, by omega⟩
    [9, y431AuxOriginalLetter g, 9, y431AuxOriginalLetter g]

/-- Every replay relator holds in the original C431/R group by already proved source facts. -/
theorem y431AuxRelatorWord_valid (r : Fin 46) :
    y431AuxPositiveWord (y431AuxRelatorWord r) = 1 := by
  unfold y431AuxRelatorWord
  split
  · dsimp only
    rw [y431AuxPositiveWord_replicate]
    simpa only [y431AuxPositiveWord, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, y431AuxGenerator_original] using
      y431_generator_pair (y431AuxOriginalPair ⟨r.val, ‹r.val < 36›⟩).1
        (y431AuxOriginalPair ⟨r.val, ‹r.val < 36›⟩).2
        (y431AuxOriginalPair_distinct ⟨r.val, ‹r.val < 36›⟩)
  · split
    · rw [y431AuxPositiveWord_append, y431AuxPositiveWord_original,
        y431PositiveWord_reverse, y431E7Positive21_value]
      simp only [y431AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, y431AuxGenerator_nine, mul_inv_cancel]
    · dsimp only
      have hc := y431AuxGenerator_nine_commute (⟨r.val - 37, by omega⟩ : Fin 9)
      have h := hc.mul_pow 2
      simpa only [y431AuxPositiveWord, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one, pow_two, y431AuxGenerator_square, one_mul, mul_assoc] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
