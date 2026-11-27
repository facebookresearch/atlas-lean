/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.HoeySloaneCycles

/-!
# Tests for `permutipleGraphEdges_union_cycles`

The theorem is proved in `MathlibExt.NumberTheory.Digits.HoeySloaneCycles`.
-/

namespace MathlibExtTest.NumberTheory.Digits.PermutiplePermutipleGraphEdgesUnionCycles

open MetaMathlibExt

-- The edge (2, 8) of the graph of 87912 is an edge of the (4, 10)-mother graph.
example : IsMotherGraphEdge 4 10 2 8 :=
  (permutipleGraphEdges_union_cycles 4 10 (by decide) (by decide) _ _
    isPermutiple_87912).1 (2, 8) (by rw [permutipleGraphEdges_87912]; decide)

-- The edge (2, 8) of the graph of 87912 lies on a simple cycle within the graph.
example :
    ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
      (∀ i, (v i, v (finRotate (m + 1) i)) ∈
        permutipleGraphEdges (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm) ∧
      ∃ i, (2, 8) = (v i, v (finRotate (m + 1) i)) :=
  (permutipleGraphEdges_union_cycles 4 10 (by decide) (by decide) _ _
    isPermutiple_87912).2 (2, 8) (by rw [permutipleGraphEdges_87912]; decide)

end MathlibExtTest.NumberTheory.Digits.PermutiplePermutipleGraphEdgesUnionCycles
