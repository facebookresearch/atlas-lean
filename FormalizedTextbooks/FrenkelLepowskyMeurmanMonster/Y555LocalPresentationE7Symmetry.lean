/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The corrected second E7 word has a square certificate obtained by relabeling the first.
Only literal Coxeter moves are relabeled; no automorphism of the spider quotient is assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7Certificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Swap the two length-two arms of the actual C322 Coxeter diagram. -/
def y322E7BranchSwap : Fin 8 → Fin 8 := ![0, 1, 2, 3, 6, 7, 4, 5]

/-- Literal intermediate words after swapping the two shorter arms. -/
def y322E7SquareWord13 (i : Fin 39) : List (Fin 8) :=
  (y322E7SquareWord i).map y322E7BranchSwap

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The kernel replays each 64-move batch on the relabeled literal words.
/-- The same finite moves are valid at the relabeled actual C322 vertices. -/
theorem y322E7Square_replay13 (i : Fin 38) :
    y322CoxeterRun (y322E7SquareMoves i) (y322E7SquareWord13 i.castSucc) =
      some (y322E7SquareWord13 i.succ) := by
  fin_cases i <;> decide +kernel

/-- The two commuting arm roots can be restored to their source order. -/
theorem y322E7BranchSwap_base :
    y322PositiveWord ([0, 1, 6, 4, 2, 7, 3] : List (Fin 8)) =
      y322PositiveWord ([0, 1, 4, 6, 2, 7, 3] : List (Fin 8)) := by
  simp only [y322PositiveWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [← mul_assoc (PresentedGroup.of 6),
    y322Positive_generator_commute 6 4 (by decide), mul_assoc]

/-- The second corrected source word is also an involution in the independent local group. -/
theorem y322E7Word13_square :
    (PresentedGroup.mk y322Relations y322E7Word13) ^ 2 = 1 := by
  have hchain (i : Fin 39) :
      y322PositiveWord (y322E7SquareWord13 i) =
        y322PositiveWord (y322E7SquareWord13 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      exact (y322CoxeterRun_valid (y322E7SquareMoves i)
        (y322E7SquareWord13 i.castSucc) (y322E7SquareWord13 i.succ)
          (y322E7Square_replay13 i)).symm.trans ih
  have h := (hchain (Fin.last 38)).symm
  have hstart : y322E7SquareWord13 0 =
      (List.replicate 9 ([0, 1, 6, 4, 2, 7, 3] : List (Fin 8))).flatten ++
        (List.replicate 9 ([0, 1, 6, 4, 2, 7, 3] : List (Fin 8))).flatten := by
    decide +kernel
  have hend : y322E7SquareWord13 (Fin.last 38) = [] := by decide +kernel
  rw [hstart, hend, y322PositiveWord_append, y322PositiveWord_replicate,
    y322E7BranchSwap_base] at h
  simpa [y322E7Word13, y322PositiveWord, map_pow, map_mul, PresentedGroup.of,
    pow_two, mul_assoc] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
