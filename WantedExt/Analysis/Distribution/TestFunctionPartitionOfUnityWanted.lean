/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.TestFunction

@[expose] public section

open TopologicalSpace
open scoped BigOperators Distributions

namespace MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnityWanted

/--
Finite test-function partition of unity: a compact set covered by finitely many open sets
carries nonnegative test functions supported in the cover members and summing to `1` on
the set.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Spaces D(R^d)" / entry "partitions of unity";
<https://en.wikipedia.org/wiki/Partition_of_unity>.
-/
public theorem_wanted testFunction_partitionOfUnity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : IsCompact K)
    {U : ι → Opens E} (hKU : K ⊆ ⋃ i, ↑(U i)) :
    ∃ φ : ι → 𝓓(⊤, ℝ),
      (∀ i x, 0 ≤ φ i x) ∧ (∀ i, tsupport (φ i) ⊆ ↑(U i)) ∧ ∀ x ∈ K, ∑ i, φ i x = 1

end MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnityWanted
