/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth partitions of unity by test functions

Let `E` be a finite-dimensional real normed space and `K ⊆ E` a compact set covered by a finite
family of open sets `U i`. Then there are nonnegative test functions `φ i : 𝓓(⊤, ℝ)` (smooth and
compactly supported) with `tsupport (φ i) ⊆ U i` for every `i` and `∑ i, φ i x = 1` for every
`x ∈ K` (`testFunction_partitionOfUnity`).

## Proof outline

* Since `E` is locally compact, `K` has an open neighbourhood `V` with compact closure.
* Mathlib's smooth partitions of unity on the manifold `E`
  (`SmoothPartitionOfUnity.exists_isSubordinate`) give smooth nonnegative functions `f i` with
  `tsupport (f i) ⊆ U i ∩ V` that sum to `1` on the closed set `K`.
* Each `tsupport (f i)` is closed and lies in the compact set `closure V`, so it is compact, and
  `f i` is a test function.
-/

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
public theorem testFunction_partitionOfUnity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : IsCompact K)
    {U : ι → Opens E} (hKU : K ⊆ ⋃ i, ↑(U i)) :
    ∃ φ : ι → 𝓓(⊤, ℝ),
      (∀ i x, 0 ≤ φ i x) ∧ (∀ i, tsupport (φ i) ⊆ ↑(U i)) ∧ ∀ x ∈ K, ∑ i, φ i x = 1 := by
  -- Shrink the cover into an open neighbourhood `V` of `K` with compact closure.
  obtain ⟨V, hVo, hKV, hVc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ E)
    hK.isClosed (fun i => (U i : Set E) ∩ V) (fun i => (U i).isOpen.inter hVo) fun x hx => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hKU hx)
      exact Set.mem_iUnion.2 ⟨i, hi, hKV hx⟩
  refine ⟨fun i => ⟨f i, contMDiff_iff_contDiff.1 (f i).contMDiff, ?_, ?_⟩,
    fun i x => f.nonneg i x, fun i => (hf i).trans Set.inter_subset_left, fun x hx => ?_⟩
  · -- The closed support of `f i` lies in the compact set `closure V`.
    exact hVc.of_isClosed_subset (isClosed_tsupport _)
      ((hf i).trans (Set.inter_subset_right.trans subset_closure))
  · exact Set.subset_univ _
  · exact (finsum_eq_sum_of_fintype fun i => f i x).symm.trans (f.sum_eq_one hx)

end MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnityWanted
