/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Tree.WeightedLeafDistance
import Mathlib.Tactic.NormNum

/-! # Weighted leaf-pair distances: the single-edge tree -/

open MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution

private def edge : UTree Bool := ⟨.leaf false, 7, .leaf true⟩

example : edge.labels = [false, true] := rfl

/-- The dissimilarity is symmetrized, not read in just one direction. The
geometric edge length does not enter the score. -/
example : edge.bmeLength (fun x _ => if x then 4 else 2) = 3 := by
  norm_num [UTree.bmeLength, UTree.pairs, RTree.pairs, RTree.leaves, pauplinCoeff, edge]
