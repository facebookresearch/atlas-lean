/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Presentable.UnderSourcePresentation
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.SimplexClosedSource
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne
public import MathlibExt.Topology.Category.PointedCGWH.Zero

/-!
# Native pointed disk and one-sphere source preservation

The actual realized one-disk uses the original ordered endpoint. Its free
underlying source and free point source give its under-object preservation.
The original disk cofiber then supplies the native one-sphere through a
finite pushout and the original cofiber comparison. Every source conclusion
uses the same realized-generator cardinal and original closed-chain diagram.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject

namespace PointedCGWH

set_option backward.isDefEq.respectTransparency false in
private def realizedZeroSimplexIsoPoint :
    SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} := by
  let e : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) :=
    CGWH.finiteRealizationIso (Δ[0] : SSet.{v})
  exact e ≪≫ SSet.toCGWHOfFinite_stdSimplex_zero_iso_point

/-- The literal free native point source preserves every original closed-chain colimit. -/
theorem freePointSource_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op
      ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v}))) := by
  let e := (Under.costar CGWH.point.{u, v}).mapIso realizedZeroSimplexIsoPoint.{u, v}
  let h : Retract ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v})
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}))) :=
    { i := e.inv
      r := e.hom
      retract := e.inv_hom_id }
  have : PreservesColimit F (coyoneda.obj (Opposite.op
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}))))) :=
    realizedSimplexSource_preservesClosedColimit 0 F hF
  exact Limits.preservesColimit_of_retract (K := F) (h.op.map coyoneda)

set_option backward.isDefEq.respectTransparency false in
private def freePointIsoDiskBoundarySource :
    (Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v} ≅
      Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
  Under.isoMk (Iso.refl _) (by
    simp only [Under.costar_obj_hom, coprod.inl_desc, Iso.refl_hom,
      Category.comp_id, Under.mk_hom])

/-- The original literal ordered disk-boundary source preserves the same native closed chain. -/
theorem diskBoundarySource_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op
      (Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v})))) := by
  have : PreservesColimit F (coyoneda.obj (Opposite.op
      ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v}))) :=
    freePointSource_preservesClosedColimit F hF
  exact preservesColimit_of_natIso F
    (coyoneda.mapIso freePointIsoDiskBoundarySource.{u, v}.symm.op)

/-- The actual one-disk with its original selected endpoint preserves the original closed chain. -/
theorem diskOneSource_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op diskOne.{u, v})) := by
  have : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  exact Under.source_preservesColimit_of_costarSources
    realizedGeneratorCardinal.{v} F diskOne.{u, v}
    (freePointSource_preservesClosedColimit F hF)
    (realizedSimplexSource_preservesClosedColimit 1 F hF)

/-- The chosen terminal pointed object is also an initial source for this same cardinal diagram. -/
theorem terminalSource_preservesGeneratorColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v}) :
    PreservesColimit F (coyoneda.obj (Opposite.op (⊤_ PointedCGWH.{u, v}))) := by
  have : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  have hInitial : IsInitial (⊤_ PointedCGWH.{u, v}) :=
    HasZeroObject.zeroIsInitial.ofIso HasZeroObject.zeroIsoTerminal
  exact preservesColimit_coyoneda_of_finiteColimit realizedGeneratorCardinal.{v} F
    (asEmptyCocone (⊤_ PointedCGWH.{u, v})) hInitial (fun k => k.as.elim)

/-- The ordinary cofiber of the original ordered disk boundary preserves the same closed chain. -/
theorem diskCofiberSource_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op
      ((HomotopicalAlgebra.ordinaryCofiber (C := PointedCGWH.{u, v})).obj
        (Arrow.mk diskBoundary.{u, v})))) := by
  have : Fact realizedGeneratorCardinal.{v}.IsRegular :=
    ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  let S0 : PointedCGWH.{u, v} :=
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  let h := IsPushout.of_hasPushout diskBoundary.{u, v} (terminal.from S0)
  refine preservesColimit_coyoneda_of_finiteColimit
    realizedGeneratorCardinal.{v} F h.cocone h.isColimit ?_
  intro k
  cases k with
  | none => exact diskBoundarySource_preservesClosedColimit F hF
  | some k =>
    cases k with
    | left => exact diskOneSource_preservesClosedColimit F hF
    | right => exact terminalSource_preservesGeneratorColimit F

/-- The actual native boundary-quotient one-sphere preserves the original closed-chain colimit. -/
theorem sphereOneSource_preservesClosedColimit
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right)) :
    PreservesColimit F (coyoneda.obj (Opposite.op sphereOne.{u, v})) := by
  let e := diskCofiberIsoSphereOne.{u, v}
  let h : Retract sphereOne.{u, v}
      ((HomotopicalAlgebra.ordinaryCofiber (C := PointedCGWH.{u, v})).obj
        (Arrow.mk diskBoundary.{u, v})) :=
    { i := e.inv
      r := e.hom
      retract := e.inv_hom_id }
  have : PreservesColimit F (coyoneda.obj (Opposite.op
      ((HomotopicalAlgebra.ordinaryCofiber (C := PointedCGWH.{u, v})).obj
        (Arrow.mk diskBoundary.{u, v})))) :=
    diskCofiberSource_preservesClosedColimit F hF
  exact Limits.preservesColimit_of_retract (K := F) (h.op.map coyoneda)

end PointedCGWH
