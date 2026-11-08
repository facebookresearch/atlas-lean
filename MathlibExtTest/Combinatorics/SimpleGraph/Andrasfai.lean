/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Andrasfai
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.Andrasfai

open MetaMathlibExt

-- Combinatorics 26: Andrásfai graph

-- Sanity check: The Andrasfai graph for `k=0` has a single edge (the graph is just `K₂`).

/-- Decidability of adjacency in `andrasfaiGraph 0`. -/

instance : DecidableRel (andrasfaiGraph 0).Adj := by
  unfold andrasfaiGraph
  infer_instance

example : (andrasfaiGraph 0).edgeFinset.card = 1 := by
  decide

end MathlibExtTest.Combinatorics.SimpleGraph.Andrasfai

end
