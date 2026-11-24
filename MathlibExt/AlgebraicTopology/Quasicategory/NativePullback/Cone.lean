/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Basic
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.JoinShape
import MathlibExt.AlgebraicTopology.Quasicategory.LimitCone

/-!
# The actual pullback cone point

The original diamond is the actual left cone on its cospan. Index
transport and the actual iterated over-slice isomorphism identify the
original boundary-lift pullback condition with terminality of the
original whole cone point. No homotopy-category square is substituted.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.NativePullback

variable {X : SSet.{u}}

/-- The original coherent square, expressed as the whole left cone. -/
def coneDiagram (q : squareShape.{u} ⟶ X) :
    (Δ[0] : SSet.{u}) ⋆ cospanShape.{u} ⟶ X :=
  shapeJoinIso.inv ≫ q

/-- The whole original cospan is the right restriction of the original cone. -/
theorem coneDiagram_fixed (q : squareShape.{u} ⟶ X) :
    joinInr Δ[0] cospanShape ≫ coneDiagram q = cospanInclusion ≫ q := by
  have hi : joinInr (Δ[0] : SSet.{u}) cospanShape ≫ shapeJoinIso.inv =
      cospanInclusion := by
    apply (cancel_mono shapeJoinIso.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      cospanInclusion_comp_shapeJoinIso_hom]
  rw [coneDiagram, ← Category.assoc, hi]

/-- The original boundary-lift square condition is the native limit condition
of its entire original left cone. -/
theorem isPullbackSquare_iff_isLimitCone (q : squareShape.{u} ⟶ X) :
    IsPullbackSquare q ↔ IsLimitCone (coneDiagram q) := by
  have hi : joinInr (Δ[0] : SSet.{u}) cospanShape ≫ shapeJoinIso.inv =
      (Iso.refl cospanShape).hom ≫ cospanInclusion := by
    apply (cancel_mono shapeJoinIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.refl_hom, Category.id_comp, cospanInclusion_comp_shapeJoinIso_hom]
  unfold IsPullbackSquare IsLimitCone
  apply forall_congr'
  intro m
  exact sliceOver.hasLiftingProperty_restrictionIndex_iff X q cospanInclusion
    (joinInr Δ[0] cospanShape) shapeJoinIso.symm (Iso.refl cospanShape) hi (boundary m).ι

/-- The pullback condition is terminality of the given original cone POINT
in the original cospan over-slice. -/
theorem isPullbackSquare_iff_isTerminalVertex (q : squareShape.{u} ⟶ X) :
    IsPullbackSquare q ↔ IsTerminalVertex
      (sliceOver.conePoint (cospanInclusion ≫ q) (coneDiagram q) (coneDiagram_fixed q)) :=
  (isPullbackSquare_iff_isLimitCone q).trans
    (isLimitCone_iff_isTerminalVertex _ _ (coneDiagram_fixed q))

end SSet.NativePullback
