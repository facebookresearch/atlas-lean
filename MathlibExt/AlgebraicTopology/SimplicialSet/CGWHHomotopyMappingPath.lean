/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.Topology.Category.CGWH.RealizedInterval

/-!
# Whole original homotopies as compact-open mapping-space paths

The actual realized edge of the simplicial internal Hom maps into the RAW
compact-open space through the existing forward comparison. Its endpoints
are proved to be the original native realized maps. Every point of its
whole prism is retained. An original two-simplex gives endpoint-fixed
composition of these paths, reusing the existing realized composition
theorem rather than a second interpolation or pointwise filling argument.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}} {f g h : X ⟶ Y}

private theorem realizationNativeMap_apply {U V : SSet.{u}} (k : U ⟶ V)
    (z : SSet.toCGWH.{u, u}.obj U) :
    SSet.toTop.map k z = SSet.toCGWH.{u, u}.map k z := by
  have hMap : ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.{u, u}.map k) =
      (SSet.toTop.map k).hom := by
    have hConstructor := ConcreteCategory.hom_ofHom (C := CGWH.{u, u})
      (X := SSet.toCGWH.{u, u}.obj U) (Y := SSet.toCGWH.{u, u}.obj V)
      (SSet.toTop.map k).hom
    dsimp only [SSet.toCGWH] at hConstructor ⊢
    exact hConstructor
  exact (congrArg (fun F : C(SSet.toCGWH.{u, u}.obj U,
    SSet.toCGWH.{u, u}.obj V) => F z) hMap).symm

private def mappingVertex (f : X ⟶ Y) :
    C(SSet.toCGWH.{u, u}.obj X, SSet.toCGWH.{u, u}.obj Y) :=
  realizationIhomToCompactOpen X Y (realizedVertex (ihomVertexEquiv X Y f))

private def mappedIhomHomotopyPath (K : Homotopy f g) :
    _root_.Path (mappingVertex f) (mappingVertex g) :=
  (TopCat.pathEquiv (realizedEdgePath K.edgeIhom)).map
    (realizationIhomToCompactOpen X Y).continuous

private theorem mappedIhomHomotopyPath_apply
    (K : Homotopy f g) (t : unitInterval) (a : SSet.toCGWH.{u, u}.obj X) :
    mappedIhomHomotopyPath K t a =
      ((realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map K.h)
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) := by
  have hy : yonedaEquiv.symm K.edgeIhom.edge = MonoidalClosed.curry K.h := by
    rw [Homotopy.edgeIhom_edge, Equiv.symm_apply_apply]
  have hp : TopCat.pathEquiv (realizedEdgePath K.edgeIhom) t =
      SSet.toCGWH.{u, u}.map (MonoidalClosed.curry K.h)
        (CGWH.nativeIntervalHomeomorph.{u, u}.symm t) := by
    change (realizedEdgePath K.edgeIhom).hom (TopCat.I.homeomorph.symm t) = _
    rw [realizedEdgePath_hom]
    change SSet.toTop.map (yonedaEquiv.symm K.edgeIhom.edge)
      (stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t)) = _
    rw [hy, CGWH.nativeIntervalHomeomorph_symm_apply.{u, u}]
    exact realizationNativeMap_apply (MonoidalClosed.curry K.h) _
  change realizationIhomToCompactOpen X Y
    (TopCat.pathEquiv (realizedEdgePath K.edgeIhom) t) a = _
  rw [hp]
  exact realizationIhomToCompactOpen_prism_apply K.h _ a

private theorem mappingVertex_eq (f : X ⟶ Y) :
    mappingVertex f = ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.map f) := by
  apply ContinuousMap.ext
  intro a
  have hs : mappedIhomHomotopyPath (Homotopy.reflH f) (0 : unitInterval) a =
      mappingVertex f a :=
    congrArg (fun c : C(SSet.toCGWH.{u, u}.obj X,
      SSet.toCGWH.{u, u}.obj Y) => c a)
        (mappedIhomHomotopyPath (Homotopy.reflH f)).source
  have hp : mappedIhomHomotopyPath (Homotopy.reflH f) (0 : unitInterval) a =
      ((realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map (Homotopy.reflH f).h)
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm 0)) :=
    mappedIhomHomotopyPath_apply (Homotopy.reflH f) (0 : unitInterval) a
  have hf :
      (realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map (Homotopy.reflH f).h =
      CartesianMonoidalCategory.fst (SSet.toCGWH.{u, u}.obj X)
        (SSet.toCGWH.{u, u}.obj (Δ[1] : SSet.{u})) ≫ SSet.toCGWH.map f := by
    rw [Homotopy.reflH_h, Functor.map_comp, ← Category.assoc,
      realizationTensorIsoCGWH_inv_fst]
  have he := ConcreteCategory.congr_hom hf
    (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm 0))
  have he' :
      ((realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map (Homotopy.reflH f).h)
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm 0)) =
        SSet.toCGWH.map f a :=
    he.trans (by rw [ConcreteCategory.comp_apply, CGWH.tensorMk_fst])
  exact hs.symm.trans (hp.trans he')

/-- The actual whole simplicial homotopy gives a path between the
ORIGINAL two native maps in their RAW compact-open mapping space. -/
public def nativeHomotopyMappingPath (K : Homotopy f g) :
    _root_.Path (ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.map f))
      (ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.map g)) :=
  (mappedIhomHomotopyPath K).cast (mappingVertex_eq f).symm (mappingVertex_eq g).symm

private theorem nativeHomotopyMappingPath_apply_computed
    (K : Homotopy f g) (t : unitInterval) (a : SSet.toCGWH.{u, u}.obj X) :
    nativeHomotopyMappingPath K t a =
      ((realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map K.h)
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) := by
  unfold nativeHomotopyMappingPath
  change mappedIhomHomotopyPath K t a = _
  exact mappedIhomHomotopyPath_apply K t a

/-- Every interval and active-source value is the SAME original realized
prism value, including both original endpoint maps. -/
public theorem nativeHomotopyMappingPath_apply
    (K : Homotopy f g) (t : unitInterval) (a : SSet.toCGWH.{u, u}.obj X) :
    nativeHomotopyMappingPath K t a =
      ((realizationTensorIsoCGWH.{u, u} X (Δ[1] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map K.h)
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)) :=
  nativeHomotopyMappingPath_apply_computed K t a

/-- An actual mapping-space two-simplex gives composition of the three
whole ORIGINAL compact-open paths with fixed original endpoints. -/
public theorem nativeHomotopyMappingPath_comp_homotopic
    (K₀₁ : Homotopy f g) (K₁₂ : Homotopy g h) (K₀₂ : Homotopy f h)
    (c : Edge.CompStruct K₀₁.edgeIhom K₁₂.edgeIhom K₀₂.edgeIhom) :
    (nativeHomotopyMappingPath K₀₂).Homotopic
      ((nativeHomotopyMappingPath K₀₁).trans (nativeHomotopyMappingPath K₁₂)) := by
  unfold nativeHomotopyMappingPath
  have hc := (realizedCompStructHomotopic c).map (realizationIhomToCompactOpen X Y)
  rw [_root_.Path.map_trans] at hc
  have hc' : (mappedIhomHomotopyPath K₀₂).Homotopic
      ((mappedIhomHomotopyPath K₀₁).trans (mappedIhomHomotopyPath K₁₂)) := hc
  have hcast := hc'.pathCast (mappingVertex_eq f).symm (mappingVertex_eq h).symm
  rw [_root_.Path.cast_trans _ _ (mappingVertex_eq f).symm (mappingVertex_eq g).symm
    (mappingVertex_eq h).symm] at hcast
  exact hcast

/-- The original constant simplicial homotopy is endpoint-fixed homotopic
to the constant path at its ORIGINAL native realized map. -/
public theorem nativeHomotopyMappingPath_reflH_homotopic (f : X ⟶ Y) :
    (nativeHomotopyMappingPath (Homotopy.reflH f)).Homotopic
      (_root_.Path.refl (ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.map f))) := by
  unfold nativeHomotopyMappingPath
  have hc := realizedEdgePath_id_homotopic (ihomVertexEquiv X Y f)
  rw [← Homotopy.edgeIhom_reflH] at hc
  have hm := hc.map (realizationIhomToCompactOpen X Y)
  have hr :
      (_root_.Path.refl (realizedVertex (ihomVertexEquiv X Y f))).map
          (realizationIhomToCompactOpen X Y).continuous = _root_.Path.refl (mappingVertex f) := by
    ext t
    rfl
  rw [hr] at hm
  have hm' : (mappedIhomHomotopyPath (Homotopy.reflH f)).Homotopic
      (_root_.Path.refl (mappingVertex f)) := hm
  have hcast := hm'.pathCast (mappingVertex_eq f).symm (mappingVertex_eq f).symm
  have he : (_root_.Path.refl (mappingVertex f)).cast (mappingVertex_eq f).symm
      (mappingVertex_eq f).symm =
      _root_.Path.refl (ConcreteCategory.hom (C := CGWH.{u, u}) (SSet.toCGWH.map f)) := by
    apply _root_.Path.ext
    funext t
    exact mappingVertex_eq f
  rw [he] at hcast
  exact hcast

end SSet

end
