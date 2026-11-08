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

public import MathlibExt.Combinatorics.SimpleGraph.Petersen
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

open SimpleGraph Finset

namespace MathlibExtTest.Combinatorics.SimpleGraph.Petersen

open MetaMathlibExt

-- Combinatorics 10: Petersen graph

instance : DecidableRel petersenGraph.Adj := fun A B => by
  unfold petersenGraph johnsonGraph SimpleGraph.Adj
  infer_instance

-- Sanity check: The Petersen graph has 15 edges

example : petersenGraph.edgeFinset.card = 15 := by
    decide

end MathlibExtTest.Combinatorics.SimpleGraph.Petersen

end
