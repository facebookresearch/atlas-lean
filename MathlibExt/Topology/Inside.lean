/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The inside of a set

`Set.inside K` is the set of points off `K` whose connected component in `Kᶜ` is bounded, that is,
the union of the bounded connected components of the complement of `K`. This is the `inside` of
HOL Light's and Isabelle/HOL's Jordan curve developments. For a Jordan curve `K` in `ℂ` the Jordan
curve theorem identifies it with the interior of the curve, the bounded component of `ℂ \ K`.
Mathlib has neither this notion nor the Jordan curve theorem; statements about the interior of a
simple closed curve (Rouché's theorem, the argument principle, the residue theorem) can be phrased
with `Set.inside` without it.

## Main results

* `Set.isOpen_inside`: in a locally connected space, the inside of a closed set is open.
* `Set.closure_inside_subset`, `Set.frontier_inside_subset`, `Set.isClosed_union_inside`: the
  closure of the inside of a closed set `K` lies in `K ∪ K.inside`, so its frontier lies in `K`.
* `Set.isBounded_inside`: in a real normed space, the inside of a bounded set is bounded, because
  every point far enough out lies on an unbounded ray that avoids the set.
* `Set.isCompact_union_inside`: in a proper real normed space, `K ∪ K.inside` is compact for
  compact `K`.

Written for the rubric-guided revision of v1 ComplexVariables target 23 (`rouche_theorem` in
`v1/Atlas/ComplexVariables/code/Lecture14.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`), whose archived formalization restricted the curve to
a circle; with `Set.inside` the curve can be any simple closed curve. The archived formalization
and its original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`).
-/

set_option autoImplicit false

open Bornology

namespace Set

/-- The *inside* of a set `K`: the points not in `K` whose connected component in `Kᶜ` is
bounded. For a simple closed curve in `ℂ` it is the interior of the curve. -/
@[expose] public def inside {X : Type*} [TopologicalSpace X] [Bornology X] (K : Set X) : Set X :=
  {x | x ∉ K ∧ IsBounded (connectedComponentIn Kᶜ x)}

section Topology

variable {X : Type*} [TopologicalSpace X] [Bornology X] {K : Set X} {x : X}

public theorem mem_inside : x ∈ K.inside ↔ x ∉ K ∧ IsBounded (connectedComponentIn Kᶜ x) :=
  Iff.rfl

variable [LocallyConnectedSpace X]

/-- In a locally connected space, the inside of a closed set is open. -/
public theorem isOpen_inside (hK : IsClosed K) : IsOpen K.inside := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxK, hxb⟩
  have hC : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  refine Filter.mem_of_superset (hC.mem_nhds (mem_connectedComponentIn hxK)) fun y hy => ?_
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rwa [← connectedComponentIn_eq hy]

/-- In a locally connected space, the closure of the inside of a closed set `K` lies in
`K ∪ K.inside`. -/
public theorem closure_inside_subset (hK : IsClosed K) : closure K.inside ⊆ K ∪ K.inside := by
  intro w hw
  by_cases hwK : w ∈ K
  · exact Or.inl hwK
  right
  have hC : IsOpen (connectedComponentIn Kᶜ w) := hK.isOpen_compl.connectedComponentIn
  obtain ⟨x, hxC, hx⟩ := mem_closure_iff.1 hw _ hC (mem_connectedComponentIn hwK)
  refine ⟨hwK, ?_⟩
  rw [connectedComponentIn_eq hxC]
  exact hx.2

/-- In a locally connected space, the frontier of the inside of a closed set `K` lies in `K`. -/
public theorem frontier_inside_subset (hK : IsClosed K) : frontier K.inside ⊆ K := by
  rw [(isOpen_inside hK).frontier_eq]
  rintro w ⟨hw, hwi⟩
  exact (closure_inside_subset hK hw).resolve_right hwi

/-- In a locally connected space, `K ∪ K.inside` is closed for a closed set `K`. -/
public theorem isClosed_union_inside (hK : IsClosed K) : IsClosed (K ∪ K.inside) := by
  rw [← closure_subset_iff_isClosed, closure_union, hK.closure_eq]
  exact union_subset subset_union_left (closure_inside_subset hK)

end Topology

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- In a real normed space, the inside of a bounded set is bounded. -/
public theorem isBounded_inside (hK : IsBounded K) : IsBounded K.inside := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := max R 0)).subset ?_
  rintro x ⟨-, hxb⟩
  rw [mem_closedBall_zero_iff]
  by_contra! hx
  have hx0 : 0 < ‖x‖ := (le_max_right R 0).trans_lt hx
  have hxR : R < ‖x‖ := (le_max_left R 0).trans_lt hx
  -- the ray `{t • x | 1 ≤ t}` is connected, avoids `K`, contains `x` and is unbounded
  set ray := (fun t : ℝ => t • x) '' Ici 1
  have hnorm : ∀ t ∈ Ici (1 : ℝ), ‖t • x‖ = t * ‖x‖ := fun t ht => by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)]
  have hsub : ray ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩ htK
    have h1 := hR _ htK
    have h2 : 1 * ‖x‖ ≤ t * ‖x‖ := mul_le_mul_of_nonneg_right ht hx0.le
    rw [hnorm t ht] at h1
    linarith
  have hray : IsPreconnected ray :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => t • x).continuousOn
  have hxray : x ∈ ray := ⟨1, mem_Ici.2 le_rfl, one_smul ℝ x⟩
  obtain ⟨C, hC⟩ := (hxb.subset (hray.subset_connectedComponentIn hxray hsub)).exists_norm_le
  have ht : max ((C + 1) / ‖x‖) 1 ∈ Ici (1 : ℝ) := mem_Ici.2 (le_max_right _ _)
  have h1 := hC _ ⟨_, ht, rfl⟩
  rw [hnorm _ ht] at h1
  have h2 : (C + 1) / ‖x‖ * ‖x‖ ≤ max ((C + 1) / ‖x‖) 1 * ‖x‖ :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
  rw [div_mul_cancel₀ _ hx0.ne'] at h2
  linarith

/-- In a proper real normed space, `K ∪ K.inside` is compact for a compact set `K`. -/
public theorem isCompact_union_inside {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] {K : Set F} (hK : IsCompact K) : IsCompact (K ∪ K.inside) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_union_inside hK.isClosed)
    (hK.isBounded.union (isBounded_inside hK.isBounded))

end Normed

end Set
