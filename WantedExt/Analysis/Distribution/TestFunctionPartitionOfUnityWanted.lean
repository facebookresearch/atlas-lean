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
**Smooth partitions of unity subordinate to a finite open cover.** Let $E$ be a
finite-dimensional real normed space, $K \subseteq E$ a compact set, and $(U_i)_{i \in \iota}$ a
finite family of open subsets of $E$ with $K \subseteq \bigcup_i U_i$. Then there are smooth
compactly supported functions $\varphi_i : E \to \mathbb{R}$, one for each $i \in \iota$, such
that $\varphi_i(x) \ge 0$ for all $i$ and all $x \in E$, the closed support of each $\varphi_i$
is contained in $U_i$, and $\sum_{i \in \iota} \varphi_i(x) = 1$ for every $x \in K$.

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
