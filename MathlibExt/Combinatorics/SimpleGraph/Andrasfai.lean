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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ZMod.Basic
/-!
# Andrasfai

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 26
-/

@[expose] public section

-- Combinatorics 26: Andrásfai graph
def andrasfaiConnectionSet (k : ℕ) : Finset (ZMod (3 * k + 2)) :=
  {x | x.val % 3 = 1}


def andrasfaiGraph (k : ℕ) : SimpleGraph (ZMod (3 * k + 2)) :=
  SimpleGraph.addCayley (andrasfaiConnectionSet k)


/-- Decidability of adjacency in `andrasfaiGraph 0`. -/
instance : DecidableRel (andrasfaiGraph 0).Adj := by
  unfold andrasfaiGraph
  infer_instance

example : (andrasfaiGraph 0).edgeFinset.card = 1 := by
  decide

end
