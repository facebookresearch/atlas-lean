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

public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.CompactSupportCutoff
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Compactly supported functions are dense in C0

Let `X` be an arbitrary locally compact Hausdorff space. The functions in
`C₀(X,ℂ)` with compact support are dense for the original supremum norm.
The proof uses the compact-set cutoff factory
`exists_compact_one_on_of_regularSpace`: one complex-valued cutoff has compact
support, equals one on the compact set, and has pointwise norm at most one.

No countability, sigma-compactness or nonempty-domain hypothesis is required.
Empty compact sets and empty domains are included.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ZeroAtInfty

namespace ZeroAtInftyContinuousMap
universe uX
variable {X : Type uX} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- Compactly supported complex C0 functions are dense in the original supremum norm.

The domain is locally compact and Hausdorff; no countability or nonempty-set assumption is imposed.

```lean
theorem dense_hasCompactSupport : Dense {g : C₀(X, ℂ) | HasCompactSupport g}
``` -/
theorem dense_hasCompactSupport : Dense {g : C₀(X, ℂ) | HasCompactSupport g} := by
  rw [Metric.dense_iff]
  intro h ε hε
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  have hsmall : {x : X | ‖h x‖ < ε / 4} ∈ cocompact X := by
    rw [← Filter.eventually_iff]
    have hdist := (Metric.tendsto_nhds.1 (zero_at_infty h)) (ε / 4) hquarter
    exact hdist.mono fun x hx => by
      rwa [dist_zero_right] at hx
  obtain ⟨K, hK, houtside⟩ := Filter.mem_cocompact.1 hsmall
  obtain ⟨φ, hφsupport, hφone, _hφglobalNorm, hφnorm⟩ :=
    exists_compact_one_on_of_regularSpace hK
  let g : C₀(X, ℂ) := φ * h
  have hgsupport : HasCompactSupport (g : X → ℂ) := hφsupport.mul_right
  have hnorm : ‖g - h‖ ≤ ε / 2 := by
    rw [← norm_toBCF_eq_norm (f := g - h)]
    apply (BoundedContinuousFunction.norm_le (by linarith : 0 ≤ ε / 2)).2
    intro x
    change ‖g x - h x‖ ≤ ε / 2
    by_cases hx : x ∈ K
    · have hφx : φ x = 1 := hφone hx
      change ‖φ x * h x - h x‖ ≤ ε / 2
      rw [hφx, one_mul, sub_self, norm_zero]
      linarith
    · have hhx : ‖h x‖ < ε / 4 := houtside hx
      have hgx : ‖g x‖ ≤ ‖h x‖ := by
        change ‖φ x * h x‖ ≤ ‖h x‖
        calc
          ‖φ x * h x‖ = ‖φ x‖ * ‖h x‖ := norm_mul _ _
          _ ≤ 1 * ‖h x‖ := mul_le_mul_of_nonneg_right (hφnorm x) (norm_nonneg _)
          _ = ‖h x‖ := one_mul _
      calc
        ‖g x - h x‖ ≤ ‖g x‖ + ‖h x‖ := norm_sub_le _ _
        _ ≤ ε / 2 := by linarith
  refine ⟨g, ?_, hgsupport⟩
  change dist g h < ε
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hnorm (by linarith)

end ZeroAtInftyContinuousMap
