/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.SimplexClosedSource
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne
public import Mathlib.Tactic.FinCases

/-!
# The original realized interval with disjoint basepoint

The interval coefficient is the actual native realization of Δ[1] with
the original freely adjoined basepoint. Its endpoint and augmentation maps
retain the general-versus-finite zero-simplex comparison and the literal
cofaces/codegeneracy. Both endpoint retractions and the original-cardinal
source conclusion are proved without model or cylinder input data.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace PointedCGWH.IntervalCoefficient

set_option backward.isDefEq.respectTransparency false in
/-- The exact general realization, finite realization and original native point comparison. -/
@[no_expose]
def zeroSimplexIsoPoint : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} := by
  let e : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) :=
    CGWH.finiteRealizationIso (Δ[0] : SSet.{v})
  exact e ≪≫ SSet.toCGWHOfFinite_stdSimplex_zero_iso_point

/-- The actual native interval coefficient with the original disjoint basepoint. -/
abbrev interval : PointedCGWH.{u, v} :=
  (Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v}))

set_option backward.isDefEq.respectTransparency false in
/-- Each endpoint uses the original coface after the complete chosen point comparison. -/
@[no_expose]
def endpoint (i : Fin 2) : (𝟙_ PointedCGWH.{u, v}) ⟶ interval.{u, v} :=
  (Under.costar CGWH.point.{u, v}).map
    (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ i))

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation uses the original zero codegeneracy and complete point comparison. -/
@[no_expose]
def augmentation : interval.{u, v} ⟶ (𝟙_ PointedCGWH.{u, v}) :=
  (Under.costar CGWH.point.{u, v}).map
    (SSet.toCGWH.map (SSet.stdSimplex.σ (0 : Fin 1)) ≫ zeroSimplexIsoPoint.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem endpoint_eq_private (i : Fin 2) :
    endpoint.{u, v} i = (Under.costar CGWH.point.{u, v}).map
      (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ i)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole endpoint arrow retains the actual original coface and comparison maps. -/
theorem endpoint_eq (i : Fin 2) :
    endpoint.{u, v} i = (Under.costar CGWH.point.{u, v}).map
      (zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ i)) :=
  endpoint_eq_private i

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_eq_private :
    augmentation.{u, v} = (Under.costar CGWH.point.{u, v}).map
      (SSet.toCGWH.map (SSet.stdSimplex.σ (0 : Fin 1)) ≫ zeroSimplexIsoPoint.hom) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole augmentation arrow retains the actual original codegeneracy and comparison. -/
theorem augmentation_eq :
    augmentation.{u, v} = (Under.costar CGWH.point.{u, v}).map
      (SSet.toCGWH.map (SSet.stdSimplex.σ (0 : Fin 1)) ≫ zeroSimplexIsoPoint.hom) :=
  augmentation_eq_private

private theorem coface_codegen (i : Fin 2) :
    SSet.stdSimplex.{v}.δ i ≫ SSet.stdSimplex.{v}.σ (0 : Fin 1) =
      𝟙 (Δ[0] : SSet.{v}) := by
  fin_cases i
  · exact CosimplicialObject.δ_comp_σ_self (n := 0) (i := (0 : Fin 1)) SSet.stdSimplex
  · exact CosimplicialObject.δ_comp_σ_succ (n := 0) (i := (0 : Fin 1)) SSet.stdSimplex

set_option backward.isDefEq.respectTransparency false in
/-- Both original native endpoints are sections of the same original augmentation. -/
@[reassoc]
theorem endpoint_augmentation (i : Fin 2) :
    endpoint.{u, v} i ≫ augmentation.{u, v} = 𝟙 (𝟙_ PointedCGWH.{u, v}) := by
  rw [endpoint_eq, augmentation_eq, ← CategoryTheory.Functor.map_comp]
  change (Under.costar CGWH.point.{u, v}).map
    ((zeroSimplexIsoPoint.inv ≫ SSet.toCGWH.map (SSet.stdSimplex.δ i)) ≫
      (SSet.toCGWH.map (SSet.stdSimplex.σ (0 : Fin 1)) ≫ zeroSimplexIsoPoint.hom)) =
    𝟙 ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v})
  rw [Category.assoc, ← Category.assoc
    (SSet.toCGWH.map (SSet.stdSimplex.δ i))
    (SSet.toCGWH.map (SSet.stdSimplex.σ (0 : Fin 1))) zeroSimplexIsoPoint.hom]
  rw [← CategoryTheory.Functor.map_comp, coface_codegen,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- The actual interval source preserves every original closed-chain colimit at the same κ. -/
theorem source_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op interval.{u, v})) :=
  PointedCGWH.realizedSimplexSource_preservesClosedColimit 1 F hF

end PointedCGWH.IntervalCoefficient
