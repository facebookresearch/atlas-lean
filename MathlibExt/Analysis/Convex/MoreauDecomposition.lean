/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Cone.InnerDual
public import MathlibExt.Analysis.InnerProductSpace.ConvexProjection

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moreau decomposition for closed convex cones

In a real inner product space, every point `x` splits uniquely as the sum
of its nearest point in a closed convex cone `K` and its nearest point in
the polar cone `K° = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 0}`, and the two summands are
orthogonal. This is the cone analogue of the orthogonal decomposition
`E = W ⊕ Wᗮ` for a closed subspace `W`, which is the projection
proposition of `v1/Atlas/IntroductionToFunctionalAnalysis/code/`; the
subspace case is recovered by taking `K = W`, since then `K° = Wᗮ`.
The decomposition is the geometric content of Moreau's theorem on
proximal points of convex cones. The nearest-point map and its generic
properties come from `MathlibExt.Analysis.InnerProductSpace.ConvexProjection`;
this module supplies the cone-specific characterization and polar results.

## Main declarations

* `IsClosedConvexCone K` : the hypothesis bundle for a nonempty complete
  convex cone `K` in a real inner product space.
* `ConvexProjection.convexProjection K x` : the canonical nearest point of `x` in `K`,
  reused with the fields of `IsClosedConvexCone K`.
* `convexProjection_eq_iff` : the variational characterization of
  `convexProjection` for cones: `p` is the projection of `x` iff `p ∈ K`,
  `⟪x - p, y⟫ ≤ 0` for all `y ∈ K`, and `⟪x - p, p⟫ = 0`.
* `polarCone K` : the (negative) polar cone of `K`.
* `convexProjection_polarCone` : the residual `x - convexProjection K x`
  is the projection of `x` onto `polarCone K`.
* `moreau_decomposition` : `x` is the sum of its two projections, which
  are orthogonal.
* `polarCone_polarCone` : the polar of the polar of a proper cone is
  itself (via Farkas' lemma, `ProperCone.hyperplane_separation'`).

References: Jean-Jacques Moreau, "Fonctions convexes duales et points
proximaux", *C. R. Acad. Sci. Paris* 255 (1962), 2897-2899; Heinz H.
Bauschke and Patrick L. Combettes, *Convex Analysis and Monotone
Operator Theory in Hilbert Spaces*, 2nd edition, Springer, 2017, on
Moreau's decomposition for cones.
-/

@[expose] public section

open Set Filter Topology
open scoped InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

namespace MathlibExt.Analysis.Convex.MoreauDecomposition

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {K : Set E}

/-- A nonempty complete convex cone in a real inner product space: the
hypothesis bundle for Moreau decomposition. Completeness is imposed on
`K` itself, not on the ambient space. -/
structure IsClosedConvexCone (K : Set E) : Prop where
  nonempty : K.Nonempty
  isComplete : IsComplete K
  convex : Convex ℝ K
  smul_mem : ∀ {c : ℝ}, 0 ≤ c → ∀ {x : E}, x ∈ K → c • x ∈ K

/-- A closed convex cone contains `0`. -/
theorem IsClosedConvexCone.zero_mem (hK : IsClosedConvexCone K) : (0 : E) ∈ K := by
  obtain ⟨x₀, hx₀⟩ := hK.nonempty
  have h := hK.smul_mem (le_refl (0 : ℝ)) hx₀
  simpa using h

/-- A closed convex cone is closed under addition. -/
theorem IsClosedConvexCone.add_mem (hK : IsClosedConvexCone K) {x y : E} (hx : x ∈ K)
    (hy : y ∈ K) : x + y ∈ K := by
  have h := hK.convex hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h2 := hK.smul_mem (show (0 : ℝ) ≤ 2 by norm_num) h
  have e : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = x + y := by
    rw [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
      one_smul]
  rwa [e] at h2

/-- Variational characterization of the projection onto a closed convex
cone: `p` is the projection of `x` iff `p ∈ K`, the residual `x - p`
makes a nonpositive inner product with every point of `K`, and the
residual is orthogonal to `p` itself. -/
theorem convexProjection_eq_iff (hK : IsClosedConvexCone K) (x p : E) (hp : p ∈ K) :
    convexProjection K x = p ↔
      (∀ y ∈ K, ⟪x - p, y⟫_ℝ ≤ 0) ∧ ⟪x - p, p⟫_ℝ = 0 := by
  constructor
  · intro h
    have hvar : ∀ w ∈ K, ⟪x - p, w - p⟫_ℝ ≤ 0 := by
      rw [← h]
      exact convexProjection_variational hK.nonempty hK.isComplete hK.convex x
    have hself : ⟪x - p, p⟫_ℝ = 0 := by
      have h0 := hvar 0 hK.zero_mem
      have h2 := hvar ((2 : ℝ) • p) (hK.smul_mem (by norm_num) hp)
      rw [zero_sub, inner_neg_right] at h0
      have h2' : ⟪x - p, p⟫_ℝ ≤ 0 := by
        have e : (2 : ℝ) • p - p = p := by rw [two_smul]; abel
        rwa [e] at h2
      linarith
    refine ⟨?_, hself⟩
    intro y hy
    have h3 := hvar (y + p) (hK.add_mem hy hp)
    have e : y + p - p = y := add_sub_cancel_right y p
    rwa [e] at h3
  · rintro ⟨h1, h2⟩
    have hpmin : ‖x - p‖ = ⨅ w : K, ‖x - w‖ := by
      apply (norm_eq_iInf_iff_real_inner_le_zero hK.convex hp).2
      intro w hw
      have e : ⟪x - p, w - p⟫_ℝ = ⟪x - p, w⟫_ℝ - ⟪x - p, p⟫_ℝ := inner_sub_right _ _ _
      rw [e, h2, sub_zero]
      exact h1 w hw
    exact convexProjection_eq_of_isNearestPoint hK.nonempty hK.isComplete hK.convex hp hpmin

/-- The residual of the cone projection makes a nonpositive inner product
with every point of the cone. -/
theorem convexProjection_inner_le_zero (hK : IsClosedConvexCone K) (x : E) (y : E) (hy : y ∈ K) :
    ⟪x - convexProjection K x, y⟫_ℝ ≤ 0 :=
  ((convexProjection_eq_iff hK x _
    (convexProjection_mem hK.nonempty hK.isComplete hK.convex x)).1 rfl).1 y hy

/-- The residual of the cone projection is orthogonal to the projection. -/
theorem convexProjection_inner_self (hK : IsClosedConvexCone K) (x : E) :
    ⟪x - convexProjection K x, convexProjection K x⟫_ℝ = 0 :=
  ((convexProjection_eq_iff hK x _
    (convexProjection_mem hK.nonempty hK.isComplete hK.convex x)).1 rfl).2

/-- A point satisfying the variational characterization is the cone
projection. -/
theorem convexProjection_eq_of_forall_inner_le_zero (hK : IsClosedConvexCone K) {x p : E}
    (hp : p ∈ K) (h1 : ∀ y ∈ K, ⟪x - p, y⟫_ℝ ≤ 0) (h2 : ⟪x - p, p⟫_ℝ = 0) :
    convexProjection K x = p :=
  (convexProjection_eq_iff hK x p hp).2 ⟨h1, h2⟩

/-- The (negative) polar cone of a set in a real inner product space:
the vectors making a nonpositive inner product with every point of `K`.
This is the negation of Mathlib's `ProperCone.innerDual`, whose sign
convention is the opposite one. -/
def polarCone (K : Set E) : Set E := {y | ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 0}

/-- Membership in the polar cone, unfolded. -/
theorem mem_polarCone {y : E} : y ∈ polarCone K ↔ ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 0 := Iff.rfl

/-- `0` lies in every polar cone. -/
theorem zero_mem_polarCone : (0 : E) ∈ polarCone K :=
  mem_polarCone.2 fun _ _ => by simp only [inner_zero_right, le_refl]

/-- The polar cone is closed under nonnegative scaling. -/
theorem smul_mem_polarCone {c : ℝ} (hc : 0 ≤ c) {y : E} (hy : y ∈ polarCone K) :
    c • y ∈ polarCone K := by
  refine mem_polarCone.2 fun x hx => ?_
  rw [real_inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hc ((mem_polarCone.1 hy) x hx)

/-- The polar cone is convex. -/
theorem convex_polarCone : Convex ℝ (polarCone K) := by
  intro x hx y hy a b ha hb hab
  refine mem_polarCone.2 fun z hz => ?_
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha ((mem_polarCone.1 hx) z hz))
    (mul_nonpos_of_nonneg_of_nonpos hb ((mem_polarCone.1 hy) z hz))

/-- The polar cone is closed. -/
theorem isClosed_polarCone : IsClosed (polarCone K) := by
  have hset : polarCone K = ⋂ x : E, ⋂ _ : x ∈ K, {y | ⟪x, y⟫_ℝ ≤ 0} := by
    ext y
    simp only [polarCone, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- The residual of the cone projection lies in the polar cone. -/
theorem sub_convexProjection_mem_polarCone (hK : IsClosedConvexCone K) (x : E) :
    x - convexProjection K x ∈ polarCone K := by
  refine mem_polarCone.2 fun y hy => ?_
  rw [real_inner_comm]
  exact convexProjection_inner_le_zero hK x y hy

section CompleteSpace

variable [CompleteSpace E]

/-- The polar cone of any set is a closed convex cone (in a complete
space, closedness gives completeness). -/
theorem isClosedConvexCone_polarCone : IsClosedConvexCone (polarCone K) where
  nonempty := ⟨0, zero_mem_polarCone⟩
  isComplete := isClosed_polarCone.isComplete
  convex := convex_polarCone
  smul_mem := smul_mem_polarCone

/-- **Moreau decomposition, polar form**: the residual of the cone
projection is the projection onto the polar cone. -/
theorem convexProjection_polarCone (hK : IsClosedConvexCone K) (x : E) :
    convexProjection (polarCone K) x =
      x - convexProjection K x := by
  apply convexProjection_eq_of_forall_inner_le_zero isClosedConvexCone_polarCone
    (sub_convexProjection_mem_polarCone hK x)
  · intro z hz
    have e : x - (x - convexProjection K x) = convexProjection K x := sub_sub_self x _
    rw [e]
    exact (mem_polarCone.1 hz) _ (convexProjection_mem hK.nonempty hK.isComplete hK.convex x)
  · have e : x - (x - convexProjection K x) = convexProjection K x := sub_sub_self x _
    rw [e, real_inner_comm]
    exact convexProjection_inner_self hK x

/-- **Moreau decomposition**: every point is the sum of its projections
onto a closed convex cone and its polar cone, and the two projections
are orthogonal. -/
theorem moreau_decomposition (hK : IsClosedConvexCone K) (x : E) :
    x = convexProjection K x +
        convexProjection (polarCone K) x ∧
      ⟪convexProjection K x,
        convexProjection (polarCone K) x⟫_ℝ = 0 := by
  rw [convexProjection_polarCone hK x]
  refine ⟨by abel, ?_⟩
  rw [real_inner_comm]
  exact convexProjection_inner_self hK x

/-- The polar of the polar of a proper cone is itself. The forward
inclusion is Farkas' lemma: a point outside the cone is separated from
it by a vector of the cone's dual, whose negation lies in the polar
cone and pairs positively with the point. -/
theorem polarCone_polarCone (C : ProperCone ℝ E) :
    polarCone (polarCone (C : Set E)) = (C : Set E) := by
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyC
    obtain ⟨v, hv, hvy⟩ := C.hyperplane_separation' hyC
    have hz : -v ∈ polarCone (C : Set E) :=
      mem_polarCone.2 fun x hx => by
        rw [inner_neg_right]
        exact neg_nonpos.mpr (hv x hx)
    have h := (mem_polarCone.1 hy) (-v) hz
    rw [inner_neg_left, real_inner_comm y v] at h
    linarith
  · intro y hy
    refine mem_polarCone.2 fun z hz => ?_
    rw [real_inner_comm]
    exact (mem_polarCone.1 hz) y hy

end CompleteSpace

end

end MathlibExt.Analysis.Convex.MoreauDecomposition
