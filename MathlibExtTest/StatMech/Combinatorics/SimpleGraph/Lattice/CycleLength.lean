/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleLength
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleLength`

* `walk_split_dist` for the closed walk `0 → 1 → 0` in the complete graph on `Fin 2`:
  `2 · dist 0 1 ≤ 2`.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CycleLength

theorem hadj : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by simp

/-- The closed walk `0 → 1 → 0`. -/
def w : (⊤ : SimpleGraph (Fin 2)).Walk 0 0 := .cons hadj (.cons hadj.symm .nil)

example : 2 * (⊤ : SimpleGraph (Fin 2)).dist 0 1 ≤ w.length :=
  walk_split_dist w (by simp [w]) (by simp [w])

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CycleLength
