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

/-!
# Point cutoffs in the actual scalar C0 algebra

The chosen point cutoff comes from the single support-bearing compact-set
factory on regular locally compact spaces. Its original value and uniform
norm bound are retained together with compact support of that same function.
Continuity as the chosen point varies is not asserted.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap
universe u

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

Choose the cutoff from the support-bearing singleton construction. -/
noncomputable def pointCutoff
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x : X) : C₀(X, ℂ) :=
  Classical.choose (exists_compact_one_on_of_regularSpace (K := ({x} : Set X)) isCompact_singleton)

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

Compact support belongs to the same chosen pointCutoff, rather than a different existence
witness. -/
theorem pointCutoff_hasCompactSupport
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x : X) : HasCompactSupport (pointCutoff x) :=
  (Classical.choose_spec
    (exists_compact_one_on_of_regularSpace (K := ({x} : Set X)) isCompact_singleton)).1

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

The chosen cutoff has its value one at the specified point. -/
@[simp]
theorem pointCutoff_apply
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x : X) : pointCutoff x x = 1 := by
  have h := (Classical.choose_spec
    (exists_compact_one_on_of_regularSpace (K := ({x} : Set X)) isCompact_singleton)).2.1
  simpa only [pointCutoff, Pi.one_apply] using h (Set.mem_singleton x)

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

The chosen cutoff obeys the proved bound for the existing C0 norm. -/
theorem norm_pointCutoff_le
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x : X) : ‖pointCutoff x‖ ≤ 1 :=
  (Classical.choose_spec
    (exists_compact_one_on_of_regularSpace (K := ({x} : Set X)) isCompact_singleton)).2.2.1

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

Every pointwise bound is for that same support-bearing chosen cutoff. -/
theorem pointCutoff_norm_apply_le
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x y : X) : ‖pointCutoff x y‖ ≤ 1 :=
  (Classical.choose_spec
    (exists_compact_one_on_of_regularSpace (K := ({x} : Set X)) isCompact_singleton)).2.2.2 y

/-- Let `X` be a regular locally compact topological space and let `x ∈ X`. The cutoff is
complex-valued and continuous, with compact support.

The quantitative point-cutoff existence result keeps its RegularSpace-only scope. -/
theorem exists_point_cutoff
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
    (x : X) : ∃ φ : C₀(X, ℂ), φ x = 1 ∧ ‖φ‖ ≤ 1 :=
  ⟨pointCutoff x, pointCutoff_apply x, norm_pointCutoff_le x⟩

private theorem pointCutoff_lch
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (x : X) : pointCutoff x x = 1 ∧ ‖pointCutoff x‖ ≤ 1 :=
  ⟨pointCutoff_apply x, norm_pointCutoff_le x⟩

end ZeroAtInftyContinuousMap
