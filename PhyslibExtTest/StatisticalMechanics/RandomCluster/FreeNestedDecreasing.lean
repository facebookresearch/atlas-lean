/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeNestedDecreasing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FreeNestedDecreasing`

* `fkProb_free_nested_decreasing_le` for the identity embedding of the one-edge graph `⊤` on
  `Fin 2` into itself, at `p = 1/2`, `q = 2`, for the decreasing events `univ` and "the edge
  `s(0, 1)` is closed".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeNestedDecreasing

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The sure event.
example := fkProb_free_nested_decreasing_le (Gin := G2) (Gout := G2) (iota := id)
  Function.injective_id (fun _ _ => Iff.rfl) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
  one_le_two isLowerSet_univ

/-- "The edge `s(0, 1)` is closed" is decreasing. -/
theorem edgeClosed_isDecreasing :
    IsDecreasing {ω : ConfigSpace (Sym2 (Fin 2)) | ω s(0, 1) = false} := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact le_bot_iff.mp h

-- A single closed edge.
example := fkProb_free_nested_decreasing_le (Gin := G2) (Gout := G2) (iota := id)
  Function.injective_id (fun _ _ => Iff.rfl) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
  one_le_two edgeClosed_isDecreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FreeNestedDecreasing
