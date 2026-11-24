/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sperner

@[expose] public section

open MathlibExt.Combinatorics.Sperner

namespace MathlibExtTest.Combinatorics.Sperner

/-- Non-vacuity, dimension one: the alternating colouring of `0, 1, 2, 3` starts at `0`, ends at
`1` and has three bichromatic segments. -/
example : Odd ((Finset.range 3).filter (fun i =>
    (if i % 2 = 0 then 0 else 1 : Fin 2) ≠ (if (i + 1) % 2 = 0 then 0 else 1 : Fin 2))).card :=
  odd_card_bichromatic (fun i => if i % 2 = 0 then 0 else 1) 3 (by decide) (by decide)

example : ((Finset.range 3).filter (fun i =>
    (if i % 2 = 0 then 0 else 1 : Fin 2) ≠ (if (i + 1) % 2 = 0 then 0 else 1 : Fin 2))).card = 3 := by
  decide

/-- A Sperner colouring of the grid triangle of side `2`: colour `2` on the left side above the
origin, colour `1` on the rest of the hypotenuse and bottom, `0` at the origin, and colour `2`
at the interior-free middle points as allowed. -/
def c₂ (i j : ℕ) : Fin 3 :=
  if i = 0 ∧ j = 0 then 0 else if i = 0 then 2 else if j = 0 then 1 else 2

/-- Non-vacuity, dimension two: `c₂` is a Sperner colouring of the triangle of side `2`. -/
theorem c₂_isSperner : IsSpernerColouring 2 c₂ where
  bottom := by decide
  left := by decide
  hypotenuse := by decide

/-- The lemma then produces a rainbow cell (here the up cell at the origin). -/
example : (∃ p ∈ upCells 2, IsRainbow (c₂ p.1 p.2) (c₂ (p.1 + 1) p.2) (c₂ p.1 (p.2 + 1))) ∨
    ∃ p ∈ downCells 2,
      IsRainbow (c₂ (p.1 + 1) p.2) (c₂ p.1 (p.2 + 1)) (c₂ (p.1 + 1) (p.2 + 1)) :=
  exists_rainbow c₂_isSperner

/-- The up cell at the origin is rainbow for `c₂`, so the conclusion is attained. -/
example : (0, 0) ∈ upCells 2 ∧ IsRainbow (c₂ 0 0) (c₂ 1 0) (c₂ 0 1) := by decide

/-- The parity statement on the same colouring. -/
example : Odd (((upCells 2).filter
      (fun p => IsRainbow (c₂ p.1 p.2) (c₂ (p.1 + 1) p.2) (c₂ p.1 (p.2 + 1)))).card +
    ((downCells 2).filter
      (fun p => IsRainbow (c₂ (p.1 + 1) p.2) (c₂ p.1 (p.2 + 1))
        (c₂ (p.1 + 1) (p.2 + 1)))).card) :=
  odd_card_rainbow c₂_isSperner

end MathlibExtTest.Combinatorics.Sperner
