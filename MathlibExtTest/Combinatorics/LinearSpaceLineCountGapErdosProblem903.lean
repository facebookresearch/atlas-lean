/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903` -/

namespace MathlibExtTest.LinearSpaceLineCountGapErdosProblem903

open Finset MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903Wanted

/-- The Fano plane: the projective plane of order `2` on the points `0, …, 6`. -/
private def fano : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

/-- The Fano plane with its line `{0, 1, 2}` replaced by the three pairs of points on it. -/
private def fanoSplit : Fin 9 → Finset (Fin 7) :=
  ![{0, 1}, {0, 2}, {1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

-- Test section: `IsTwoDesign`. The Fano plane is a 2-design with `2 ^ 2 + 2 + 1 = 7` blocks, so
-- the hypothesis `n < t` of the gap theorem cannot be dropped.
example : IsTwoDesign fano := by
  refine ⟨by decide, fun x y hxy => (Fintype.existsUnique_iff_card_one _).2 ?_⟩
  revert x y
  decide

-- Splitting a line of the Fano plane into its three pairs gives a 2-design with `7 + 2 = 9`
-- blocks, so the bound `t ≥ n + p` is attained for `p = 2`.
example : IsTwoDesign fanoSplit := by
  refine ⟨by decide, fun x y hxy => (Fintype.existsUnique_iff_card_one _).2 ?_⟩
  revert x y
  decide

-- Blocks have at least two points: a family with a singleton block is not a 2-design, even though
-- it covers no pair twice.
example : ¬ IsTwoDesign (fun _ : Fin 1 => ({0} : Finset (Fin 7))) := fun h => by
  have := h.1 0
  simp at this

-- Two blocks through the same pair of points are not allowed, so repeated blocks are excluded.
example : ¬ IsTwoDesign (fun _ : Fin 2 => ({0, 1} : Finset (Fin 2))) := fun h => by
  obtain ⟨i, -, hi⟩ := h.2 0 1 (by decide)
  have h0 := hi 0 (by decide)
  have h1 := hi 1 (by decide)
  exact absurd (h0.trans h1.symm) (by decide)

-- Test section: the gap theorem. No 2-design on `7` points has exactly `8` blocks.
example (A : Fin 8 → Finset (Fin 7)) : ¬ IsTwoDesign A := fun hA => by
  have := lineCountGapAboveProjectivePlane_holds 2 Nat.prime_two.isPrimePow 8 A hA (by norm_num)
  norm_num at this

-- For `p = 3`, a 2-design on `13` points with more than `13` blocks has at least `16` blocks.
example (t : ℕ) (A : Fin t → Finset (Fin 13)) (hA : IsTwoDesign A) (ht : 13 < t) : 16 ≤ t :=
  lineCountGapAboveProjectivePlane_holds 3 Nat.prime_three.isPrimePow t A hA ht

end MathlibExtTest.LinearSpaceLineCountGapErdosProblem903
