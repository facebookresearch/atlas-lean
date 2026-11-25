/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.CompactOpen

/-!
# Complex continuous maps with the compact-open topology

For any topological space X, the complex-valued continuous maps C(X,ℂ)
form a topological ring for the compact-open topology and pointwise ring
operations. Addition and multiplication are jointly continuous, and
negation is continuous. Compact restrictions control joint multiplication.
-/

@[expose] public section
noncomputable section
open Filter Set Topology
namespace ContinuousMap
universe u

/-- For any topological space X, C(X,ℂ) with its compact-open topology and
pointwise operations is a topological ring: addition and multiplication are
jointly continuous, and negation is continuous. -/
instance (priority := 100) complexCompactOpenTopologicalRing
    (X : Type u) [TopologicalSpace X] : IsTopologicalRing C(X, ℂ) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg
  continuous_mul := by
    rw [continuous_iff_continuousAt]
    intro p
    change Tendsto (fun q : C(X, ℂ) × C(X, ℂ) => q.1 * q.2)
      (𝓝 p) (𝓝 (p.1 * p.2))
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro L hL
    let : CompactSpace L := isCompact_iff_compactSpace.mp hL
    let i : C(L, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : Continuous (fun f : C(X, ℂ) => f.comp i) := i.continuous_precomp
    have ht : Tendsto
        (fun q : C(X, ℂ) × C(X, ℂ) => q.1.comp i * q.2.comp i)
        (𝓝 p) (𝓝 (p.1.comp i * p.2.comp i)) :=
      ((hi.comp continuous_fst).mul (hi.comp continuous_snd)).tendsto p
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    simpa only [← ContinuousMap.mul_comp, ContinuousMap.coe_comp, ContinuousMap.coe_mk,
      Function.comp_apply, i] using
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp ht)

end ContinuousMap
