/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.CGWH.Point
public import MathlibExt.Topology.Category.TopCat.PointQuotient

/-!
# Quotient projections for native point pushouts

The closed-pushout comparison transports the topological quotient projection
to the selected native CGWH pushout. Nonemptiness ensures that the collapsed
point has a representative in the original target.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits Topology

namespace CGWH

/-- Collapsing a nonempty closedly embedded subspace onto the terminal point
gives the actual quotient topology on the native projection. -/
theorem isQuotientMap_pointPushout_inl
    {W X : CGWH.{u, v}} (i : W ⟶ X) [Nonempty W]
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) :
    IsQuotientMap
      (ConcreteCategory.hom (pushout.inl i (point_isTerminal.from W))) := by
  let g : W ⟶ point.{u, v} := point_isTerminal.from W
  let e := pushoutClosedComparisonIso i g hi
  have hPoint : cgwhToTop.map g =
      TopCat.isTerminalPUnit.from (cgwhToTop.obj W) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    change (g w : PUnit.{v + 1}) = PUnit.unit
    exact @Subsingleton.elim PUnit.{v + 1} inferInstance _ _
  have hRaw : IsQuotientMap
      (pushout.inl (cgwhToTop.map i) (cgwhToTop.map g)).hom := by
    rw [hPoint]
    let _ : Nonempty (Arrow.mk (cgwhToTop.map i)).left := by
      change Nonempty W
      infer_instance
    exact TopCat.pointQuotientProjection_isQuotientMap
      (Arrow.mk (cgwhToTop.map i))
  have hComparison :
      pushout.inl (cgwhToTop.map i) (cgwhToTop.map g) ≫ e.hom =
        cgwhToTop.map (pushout.inl i g) :=
    pushoutClosedComparisonIso_hom_inl i g hi
  change IsQuotientMap (cgwhToTop.map (pushout.inl i g)).hom
  rw [← hComparison]
  exact (TopCat.homeoOfIso e).isQuotientMap.comp hRaw

end CGWH
