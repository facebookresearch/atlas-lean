/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import MathlibExt.Topology.Inside

set_option autoImplicit false

open Bornology Metric Set

-- The inside of the unit circle in `ℂ` is open and bounded, and its frontier lies on the circle.
example : IsOpen (sphere (0 : ℂ) 1).inside ∧ IsBounded (sphere (0 : ℂ) 1).inside ∧
    frontier (sphere (0 : ℂ) 1).inside ⊆ sphere 0 1 :=
  ⟨isOpen_inside isClosed_sphere, isBounded_inside isBounded_sphere,
    frontier_inside_subset isClosed_sphere⟩

-- The centre of the unit circle is inside it: its component in the complement of the circle
-- stays in the open unit disc.
example : (0 : ℂ) ∈ (sphere (0 : ℂ) 1).inside := by
  refine mem_inside.2 ⟨by simp, (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_⟩
  have hsub : (sphere (0 : ℂ) 1)ᶜ ⊆ ball 0 1 ∪ (closedBall 0 1)ᶜ := by
    intro z hz
    rw [mem_compl_iff, mem_sphere_zero_iff_norm] at hz
    rcases lt_or_gt_of_ne hz with h | h
    · exact Or.inl (mem_ball_zero_iff.2 h)
    · exact Or.inr fun h' => (mem_closedBall_zero_iff.1 h').not_gt h
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_ball
    isClosed_closedBall.isOpen_compl (disjoint_compl_right_iff_subset.2 ball_subset_closedBall)
    ((connectedComponentIn_subset _ _).trans hsub)
    ⟨0, mem_connectedComponentIn (by simp), mem_ball_self one_pos⟩

-- In any finite-dimensional real normed space, a compact set together with its inside is
-- compact.
example (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K) : IsCompact (K ∪ K.inside) :=
  isCompact_union_inside hK

#print axioms Set.isBounded_inside
#print axioms Set.isCompact_union_inside
