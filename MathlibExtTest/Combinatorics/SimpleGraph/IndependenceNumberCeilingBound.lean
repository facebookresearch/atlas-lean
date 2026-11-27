/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.IndependenceNumberCeilingBound

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.IndependenceNumberCeilingBound`
-/

open SimpleGraph WrittenOnTheWallII.GraphConjecture100

namespace MathlibExtTest.Combinatorics.SimpleGraphTests.IndependenceNumberCeilingBound

-- Source faithfulness: the Formal Conjectures statement
-- `WrittenOnTheWallII.GraphConjecture100.conjecture100`, verbatim.
example {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ :=
  conjecture100 G h

-- Sanity checks carried by the Formal Conjectures file.
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj] : 0 ≤ degreeL2Norm G :=
  degreeL2Norm_nonneg G

-- `indepNeighborsCard` is the independence number of the neighbourhood.
example {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (v : α) :
    indepNeighborsCard G v = (G.induce (G.neighborSet v)).indepNum := rfl

end MathlibExtTest.Combinatorics.SimpleGraphTests.IndependenceNumberCeilingBound
