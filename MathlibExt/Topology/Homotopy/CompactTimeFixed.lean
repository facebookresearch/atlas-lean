/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Evaluation at an arbitrary compact-time selector near a fixed point

If a continuous map on a compact time parameter is constant over one spatial
point, its evaluation remains continuous at that point even when the chosen
time depends discontinuously on the source.  Compactness supplies a single
spatial neighborhood that works for every time.

The HomotopyRel specialization is the continuity gate needed by controlled
NDR pushout-product formulas.  This file defines no NDR structure.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Filter Set Topology

universe u₁ u₂ u₃ u₄

namespace ContinuousMap

variable {T : Type u₁} {X : Type u₂} {Y : Type u₃} {Z : Type u₄}
  [TopologicalSpace T] [CompactSpace T]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Let `F : T × X → Y` be continuous, with compact `T`, and suppose
`F (t, x₀) = y₀` for every `t`.  If `g` tends to `x₀` at `z₀`, then
`z ↦ F (τ z, g z)` tends to `y₀` for an arbitrary time selector `τ`;
no continuity of `τ` is required. -/
theorem continuousAt_comp_arbitrary_compact_time_of_forall_eq
    (F : C(T × X, Y)) (x₀ : X) (y₀ : Y)
    (hF : ∀ t : T, F (t, x₀) = y₀)
    (g : Z → X) (τ : Z → T) (z₀ : Z)
    (hg : ContinuousAt g z₀) (hg₀ : g z₀ = x₀) :
    ContinuousAt (fun z => F (τ z, g z)) z₀ := by
  have hvalue : F (τ z₀, g z₀) = y₀ := by
    rw [hg₀]
    exact hF (τ z₀)
  rw [continuousAt_def, hvalue]
  intro s hs
  obtain ⟨V, hVs, hVopen, hy₀V⟩ := mem_nhds_iff.mp hs
  let U : Set (T × X) := F ⁻¹' V
  have hUopen : IsOpen U := hVopen.preimage F.continuous
  have hU : U ∈ 𝓝ˢ (Set.univ : Set T) ×ˢ 𝓝 x₀ := by
    apply isCompact_univ.mem_nhdsSet_prod_of_forall
    intro t _
    rw [← nhds_prod_eq]
    apply hUopen.mem_nhds
    change F (t, x₀) ∈ V
    rw [hF t]
    exact hy₀V
  obtain ⟨W, hW, N, hN, hWN⟩ := Filter.mem_prod_iff.mp hU
  have hTW : (Set.univ : Set T) ⊆ W := subset_of_mem_nhdsSet hW
  have hNg : g ⁻¹' N ∈ 𝓝 z₀ := by
    apply hg
    simpa only [hg₀] using hN
  apply mem_of_superset hNg
  intro z hz
  apply hVs
  exact hWN ⟨hTW (Set.mem_univ (τ z)), hz⟩

end ContinuousMap

namespace ContinuousMap.HomotopyRel

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f₀ f₁ : C(X, Y)} {S : Set X}

/-- Near a point in the relative fixed set, a relative homotopy may be
evaluated at an arbitrary, possibly discontinuous, time selector without
losing continuity at that point. -/
theorem continuousAt_comp_arbitrary_time_of_mem
    (F : HomotopyRel f₀ f₁ S)
    (g : Z → X) (τ : Z → unitInterval) (z₀ : Z)
    (hg : ContinuousAt g z₀) (hz₀ : g z₀ ∈ S) :
    ContinuousAt (fun z => F (τ z, g z)) z₀ := by
  exact ContinuousMap.continuousAt_comp_arbitrary_compact_time_of_forall_eq
    F.toHomotopy.toContinuousMap (g z₀) (f₀ (g z₀))
    (fun t => F.eq_fst t hz₀) g τ z₀ hg rfl

end ContinuousMap.HomotopyRel

end
