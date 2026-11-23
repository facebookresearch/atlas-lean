/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSet

open MetaMathlibExt

-- A singleton consists entirely of an isolated point.
example (x : ℝ) : selfSimilarLayer {x} 0 = {x} := by
  rw [selfSimilarLayer_zero]
  apply Set.Subset.antisymm Set.sdiff_subset
  rintro y (rfl : y = x)
  refine ⟨rfl, ?_⟩
  rw [mem_derivedSet, accPt_principal_iff_clusterPt]
  simp [ClusterPt]

-- With 1 in layer 2, its index at exponent zero is -2. For module 3 this puts 1/3 in layer 5
-- whenever a layer containing it is given.
example {K : Set ℝ} (hK : IsQuasiArithmeticalCompactSet K 3 3)
    (h : 1 ∈ selfSimilarLayer K 2) {w : ℕ} (hw : (1 : ℝ) / 3 ∈ selfSimilarLayer K w) :
    w = 5 := by
  have heq := isQuasiArithmeticalCompactSet_layer_index (n := 1) (p := 0) (q := 1)
    hK (by simpa using h) (by simpa using hw)
  omega

-- The un-normalized gauge defaults to zero if the set has no points in any layer.
example (μ ρ n : ℕ) : stabilityGaugeIndex ∅ μ ρ n = 0 := by
  have hder : derivedSet (∅ : Set ℝ) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun x => by simp [mem_derivedSet, AccPt]
  have hlayer (i : ℕ) : selfSimilarLayer ∅ i = ∅ := by
    simp [selfSimilarLayer, Function.iterate_fixed hder]
  simp [stabilityGaugeIndex, hlayer]
