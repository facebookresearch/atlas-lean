/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Cone.InnerDual
public import MathlibExt.Analysis.InnerProductSpace.ConvexProjection

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Moreau decomposition for closed convex cones

In a real Hilbert space, every point `x` is the sum of its nearest point
in a proper cone `C` and its nearest point in the negative polar
`C° = {y | ∀ x ∈ C, ⟪x, y⟫ ≤ 0}`, and the two summands are orthogonal.
This is the cone analogue of the orthogonal decomposition `E = W ⊕ Wᗮ`
for a closed subspace `W`, the projection proposition of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/`.

The nearest-point map and its generic properties come from
`MathlibExt.Analysis.InnerProductSpace.ConvexProjection`. Cone-specific
variational results use Mathlib's `PointedCone` with completeness of its
carrier, so they also apply when the ambient inner product space is
incomplete. The main decomposition and bipolar results take `ProperCone`
directly. The negative polar is the standard dual of the negated carrier,
packaged as a `ProperCone` using continuity of the inner product.

## Main declarations

* `convexProjection_eq_iff` : the cone-specific variational characterization.
* `polarCone K` : the negative polar as a canonical `ProperCone ℝ E`.
* `convexProjection_polarCone` : the cone projection's residual is the polar projection.
* `moreau_decomposition` : the two projections sum to `x` and are orthogonal.
* `polarCone_polarCone` : the negative bipolar of a proper cone is itself.

References: Jean-Jacques Moreau, "Fonctions convexes duales et points
proximaux", *C. R. Acad. Sci. Paris* 255 (1962), 2897-2899; Heinz H.
Bauschke and Patrick L. Combettes, *Convex Analysis and Monotone
Operator Theory in Hilbert Spaces*, 2nd edition, Springer, 2017.
-/

@[expose] public section

open Set
open scoped InnerProductSpace Pointwise
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

namespace MathlibExt.Analysis.Convex.MoreauDecomposition

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Variational characterization of the projection onto a cone with complete carrier:
`p` is the projection of `x` iff the residual pairs nonpositively with the
cone and is orthogonal to `p`. The ambient space need not be complete. -/
theorem convexProjection_eq_iff (C : PointedCone ℝ E) (hC : IsComplete (C : Set E))
    (x p : E) (hp : p ∈ C) :
    convexProjection (C : Set E) x = p ↔
      (∀ y ∈ C, ⟪x - p, y⟫_ℝ ≤ 0) ∧ ⟪x - p, p⟫_ℝ = 0 := by
  constructor
  · intro h
    have hvar : ∀ w ∈ C, ⟪x - p, w - p⟫_ℝ ≤ 0 := by
      rw [← h]
      exact convexProjection_variational C.nonempty hC C.convex x
    have hself : ⟪x - p, p⟫_ℝ = 0 := by
      have h0 := hvar 0 C.zero_mem
      have h2 := hvar ((2 : ℝ) • p) (C.smul_mem (by norm_num) hp)
      rw [zero_sub, inner_neg_right] at h0
      have h2' : ⟪x - p, p⟫_ℝ ≤ 0 := by
        have e : (2 : ℝ) • p - p = p := by rw [two_smul]; abel
        rwa [e] at h2
      linarith
    refine ⟨?_, hself⟩
    intro y hy
    have h3 := hvar (y + p) (C.add_mem hy hp)
    have e : y + p - p = y := add_sub_cancel_right y p
    rwa [e] at h3
  · rintro ⟨h1, h2⟩
    have hpmin : ‖x - p‖ = ⨅ w : C, ‖x - w‖ := by
      apply (norm_eq_iInf_iff_real_inner_le_zero C.convex hp).2
      intro w hw
      rw [inner_sub_right, h2, sub_zero]
      exact h1 w hw
    exact convexProjection_eq_of_isNearestPoint C.nonempty hC C.convex hp hpmin

/-- The residual of the cone projection pairs nonpositively with every point of the cone. -/
theorem convexProjection_inner_le_zero (C : PointedCone ℝ E)
    (hC : IsComplete (C : Set E)) (x y : E) (hy : y ∈ C) :
    ⟪x - convexProjection (C : Set E) x, y⟫_ℝ ≤ 0 :=
  ((convexProjection_eq_iff C hC x _
    (convexProjection_mem C.nonempty hC C.convex x)).1 rfl).1 y hy

/-- The residual of the cone projection is orthogonal to the projection. -/
theorem convexProjection_inner_self (C : PointedCone ℝ E) (hC : IsComplete (C : Set E))
    (x : E) :
    ⟪x - convexProjection (C : Set E) x, convexProjection (C : Set E) x⟫_ℝ = 0 :=
  ((convexProjection_eq_iff C hC x _
    (convexProjection_mem C.nonempty hC C.convex x)).1 rfl).2

/-- A point satisfying the cone variational characterization is the projection. -/
theorem convexProjection_eq_of_forall_inner_le_zero (C : PointedCone ℝ E)
    (hC : IsComplete (C : Set E)) {x p : E} (hp : p ∈ C)
    (h1 : ∀ y ∈ C, ⟪x - p, y⟫_ℝ ≤ 0) (h2 : ⟪x - p, p⟫_ℝ = 0) :
    convexProjection (C : Set E) x = p :=
  (convexProjection_eq_iff C hC x p hp).2 ⟨h1, h2⟩

/-- The negative polar is the standard dual cone of the negated set. Continuity
makes its carrier closed without requiring completeness of the ambient space. -/
def polarCone (K : Set E) : ProperCone ℝ E where
  toSubmodule := PointedCone.dual (innerₗ E) (-K)
  isClosed' := PointedCone.isClosed_dual fun x => (innerSL ℝ x).continuous

/-- Membership in the negative polar uses the nonpositive inner-product convention. -/
theorem mem_polarCone {K : Set E} {y : E} :
    y ∈ polarCone K ↔ ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 0 := by
  change (∀ ⦃z⦄, z ∈ -K → 0 ≤ ⟪z, y⟫_ℝ) ↔ _
  constructor
  · intro hy x hx
    have h := hy (Set.neg_mem_neg.mpr hx)
    rw [inner_neg_left] at h
    exact neg_nonneg.mp h
  · intro hy z hz
    have h := hy (-z) (Set.mem_neg.mp hz)
    rw [inner_neg_left] at h
    exact neg_nonpos.mp h

/-- The residual of a cone projection lies in its negative polar. -/
theorem sub_convexProjection_mem_polarCone (C : PointedCone ℝ E)
    (hC : IsComplete (C : Set E)) (x : E) :
    x - convexProjection (C : Set E) x ∈ polarCone (C : Set E) := by
  refine mem_polarCone.2 fun y hy => ?_
  rw [real_inner_comm]
  exact convexProjection_inner_le_zero C hC x y hy

section CompleteSpace

variable [CompleteSpace E]

/-- In a complete ambient space, the negative polar agrees with Mathlib's
inner dual of the negated carrier. -/
theorem polarCone_eq_innerDual_neg (K : Set E) :
    polarCone K = ProperCone.innerDual (-K) := rfl

/-- **Moreau decomposition, polar form**: the cone projection's residual is the
projection onto its negative polar. This accepts a Mathlib proper cone directly. -/
theorem convexProjection_polarCone (C : ProperCone ℝ E) (x : E) :
    convexProjection (polarCone (C : Set E)) x = x - convexProjection (C : Set E) x := by
  apply convexProjection_eq_of_forall_inner_le_zero (polarCone (C : Set E)).toPointedCone
    (polarCone (C : Set E)).isClosed.isComplete
    (sub_convexProjection_mem_polarCone C.toPointedCone C.isClosed.isComplete x)
  · intro z hz
    rw [sub_sub_self]
    exact (mem_polarCone.1 hz) _ (convexProjection_mem C.nonempty C.isClosed.isComplete C.convex x)
  · rw [sub_sub_self, real_inner_comm]
    exact convexProjection_inner_self C.toPointedCone C.isClosed.isComplete x

/-- **Moreau decomposition**: a point is the sum of its projections onto a
proper cone and its negative polar, and the projections are orthogonal. -/
theorem moreau_decomposition (C : ProperCone ℝ E) (x : E) :
    x = convexProjection (C : Set E) x + convexProjection (polarCone (C : Set E)) x ∧
      ⟪convexProjection (C : Set E) x, convexProjection (polarCone (C : Set E)) x⟫_ℝ = 0 := by
  rw [convexProjection_polarCone C x]
  refine ⟨by abel, ?_⟩
  rw [real_inner_comm]
  exact convexProjection_inner_self C.toPointedCone C.isClosed.isComplete x

private theorem neg_mem_polarCone_iff_innerDual {K : Set E} {y : E} :
    -y ∈ polarCone K ↔ y ∈ ProperCone.innerDual K := by
  rw [mem_polarCone, ProperCone.mem_innerDual]
  simp only [inner_neg_right, neg_nonpos]

/-- The negative bipolar of a proper cone is itself, by Mathlib's inner-dual bipolar theorem. -/
theorem polarCone_polarCone (C : ProperCone ℝ E) :
    polarCone (polarCone (C : Set E) : Set E) = C := by
  have h : polarCone (polarCone (C : Set E) : Set E) =
      ProperCone.innerDual (ProperCone.innerDual (C : Set E) : Set E) := by
    ext y
    constructor
    · intro hy
      refine ProperCone.mem_innerDual.2 fun z hz => ?_
      have h := (mem_polarCone.1 hy) (-z) (neg_mem_polarCone_iff_innerDual.2 hz)
      rw [inner_neg_left] at h
      exact neg_nonpos.mp h
    · intro hy
      refine mem_polarCone.2 fun z hz => ?_
      have hzz : -(-z) ∈ polarCone (C : Set E) := by
        rw [neg_neg]
        exact hz
      have hz' : -z ∈ ProperCone.innerDual (C : Set E) :=
        neg_mem_polarCone_iff_innerDual.1 hzz
      have h := (ProperCone.mem_innerDual.1 hy) hz'
      rw [inner_neg_left] at h
      exact neg_nonneg.mp h
  exact h.trans (ProperCone.innerDual_innerDual C)

end CompleteSpace

end

end MathlibExt.Analysis.Convex.MoreauDecomposition
