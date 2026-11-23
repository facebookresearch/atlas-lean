/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.CGWH.ProductPoints
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Pair vertices in the native simplicial realization product

The inverse of the original CGWH realization-product isomorphism sends
the original pair of realized vertices to the realized pair simplex.
The probe universe remains independent of the simplicial carrier universe.
-/

noncomputable section

open CategoryTheory.Limits Opposite
open scoped Simplicial

universe w u

namespace CategoryTheory

/-- The original native realization-product inverse carries the original
pair point to the realized pair vertex. -/
public theorem realizationProdIsoCGWH_inv_prodPoint_realizedVertex
    {X Y : SSet.{u}}
    (x : X.obj (op (SimplexCategory.mk 0)))
    (y : Y.obj (op (SimplexCategory.mk 0))) :
    (SSet.realizationProdIsoCGWH.{w, u} X Y).inv
        (CGWH.prodPoint _ _
          (SSet.realizedVertex x) (SSet.realizedVertex y)) =
      SSet.realizedVertex
        (FunctorToTypes.prodMk x y : (X ⨯ Y).obj
          (op (SimplexCategory.mk 0))) := by
  let F := SSet.toCGWH.{w, u}
  let A : CGWH.{w, u} := F.obj X
  let B : CGWH.{w, u} := F.obj Y
  let P : CGWH.{w, u} := F.obj (X ⨯ Y)
  let delta := SSet.realizationToTopIso.{w, u}
  let nativeVertex (Z : SSet.{u}) (z : Z.obj (op (SimplexCategory.mk 0))) : F.obj Z :=
    (delta.app Z).inv (SSet.realizedVertex z)
  let v : (X ⨯ Y).obj (op (SimplexCategory.mk 0)) := FunctorToTypes.prodMk x y
  let ax : A := nativeVertex X x
  let nativeY : B := nativeVertex Y y
  let c : P := nativeVertex (X ⨯ Y) v
  let E : P ≅ A ⨯ B := SSet.realizationProdIsoCGWH.{w, u} X Y
  let piX : A ⨯ B ⟶ A := Limits.prod.fst
  let piY : A ⨯ B ⟶ B := Limits.prod.snd
  let fstTop : TopCat.of (A × B) ⟶ CGWH.cgwhToTop.obj A := TopCat.prodFst
  let sndTop : TopCat.of (A × B) ⟶ CGWH.cgwhToTop.obj B := TopCat.prodSnd
  have hForget {U V : CGWH.{w, u}} (k : U ⟶ V) (z : U) :
      (CGWH.cgwhToTop.map k) z = k z := rfl
  have hFst (z : A × B) : fstTop z = z.1 := rfl
  have hSnd (z : A × B) : sndTop z = z.2 := rfl
  change E.inv (CGWH.prodPoint A B ax nativeY) = c
  have hNativeMap {Z : SSet.{u}} (f : X ⨯ Y ⟶ Z)
      (z : Z.obj (op (SimplexCategory.mk 0)))
      (hz : f.app (op (SimplexCategory.mk 0)) v = z) :
      F.map f c = nativeVertex Z z := by
    apply (ConcreteCategory.bijective_of_isIso (delta.app Z).hom).1
    have hNatArrow : CGWH.cgwhToTop.map (F.map f) ≫ (delta.app Z).hom =
        (delta.app (X ⨯ Y)).hom ≫ SSet.toTop.map f := delta.hom.naturality f
    have h := ConcreteCategory.congr_hom hNatArrow c
    have hLeft : (CGWH.cgwhToTop.map (F.map f) ≫ (delta.app Z).hom) c =
        (delta.app Z).hom (F.map f c) :=
      (CategoryTheory.comp_apply (CGWH.cgwhToTop.map (F.map f)) (delta.app Z).hom c).trans
        (congrArg (fun a : F.obj Z => (delta.app Z).hom a) (hForget (F.map f) c))
    have hRight : ((delta.app (X ⨯ Y)).hom ≫ SSet.toTop.map f) c =
        (SSet.toTop.map f) ((delta.app (X ⨯ Y)).hom c) :=
      CategoryTheory.comp_apply (delta.app (X ⨯ Y)).hom (SSet.toTop.map f) c
    have hNat : (delta.app Z).hom (F.map f c) =
        (SSet.toTop.map f) ((delta.app (X ⨯ Y)).hom c) :=
      hLeft.symm.trans (h.trans hRight)
    have hSource : (delta.app (X ⨯ Y)).hom c = SSet.realizedVertex v :=
      Iso.inv_hom_id_apply (delta.app (X ⨯ Y)) (SSet.realizedVertex v)
    have hTarget : (delta.app Z).hom (nativeVertex Z z) = SSet.realizedVertex z :=
      Iso.inv_hom_id_apply (delta.app Z) (SSet.realizedVertex z)
    have hRaw : SSet.toTop.map f (SSet.realizedVertex v) = SSet.realizedVertex z :=
      (SSet.realizedVertex_naturality f v).symm.trans
        (congrArg (fun z : Z.obj (op (SimplexCategory.mk 0)) => SSet.realizedVertex z) hz)
    exact hNat.trans ((congrArg (SSet.toTop.map f) hSource).trans (hRaw.trans hTarget.symm))
  have hX : F.map (Limits.prod.fst : X ⨯ Y ⟶ X) c = ax :=
    hNativeMap _ x (FunctorToTypes.prodMk_fst x y)
  have hY : F.map (Limits.prod.snd : X ⨯ Y ⟶ Y) c = nativeY :=
    hNativeMap _ y (FunctorToTypes.prodMk_snd x y)
  have hCoordinates : CGWH.prodComparisonToTop A B (E.hom c) = (ax, nativeY) := by
    apply Prod.ext
    · have hArrow : CGWH.prodComparisonToTop A B ≫ fstTop =
          CGWH.cgwhToTop.map piX := CGWH.prodComparisonToTop_fst A B
      have h := ConcreteCategory.congr_hom hArrow (E.hom c)
      have hLeft : (CGWH.prodComparisonToTop A B ≫ fstTop) (E.hom c) =
          (CGWH.prodComparisonToTop A B (E.hom c)).1 :=
        (CategoryTheory.comp_apply (CGWH.prodComparisonToTop A B) fstTop (E.hom c)).trans
          (hFst (CGWH.prodComparisonToTop A B (E.hom c)))
      have h1 : (CGWH.prodComparisonToTop A B (E.hom c)).1 = piX (E.hom c) :=
        hLeft.symm.trans (h.trans (hForget piX (E.hom c)))
      have hE : E.hom ≫ piX = F.map (Limits.prod.fst : X ⨯ Y ⟶ X) :=
        SSet.realizationProdIsoCGWH_hom_fst X Y
      have h2 : piX (E.hom c) = F.map (Limits.prod.fst : X ⨯ Y ⟶ X) c :=
        (CategoryTheory.comp_apply E.hom piX c).symm.trans
          (ConcreteCategory.congr_hom hE c)
      exact h1.trans (h2.trans hX)
    · have hArrow : CGWH.prodComparisonToTop A B ≫ sndTop =
          CGWH.cgwhToTop.map piY := CGWH.prodComparisonToTop_snd A B
      have h := ConcreteCategory.congr_hom hArrow (E.hom c)
      have hLeft : (CGWH.prodComparisonToTop A B ≫ sndTop) (E.hom c) =
          (CGWH.prodComparisonToTop A B (E.hom c)).2 :=
        (CategoryTheory.comp_apply (CGWH.prodComparisonToTop A B) sndTop (E.hom c)).trans
          (hSnd (CGWH.prodComparisonToTop A B (E.hom c)))
      have h1 : (CGWH.prodComparisonToTop A B (E.hom c)).2 = piY (E.hom c) :=
        hLeft.symm.trans (h.trans (hForget piY (E.hom c)))
      have hE : E.hom ≫ piY = F.map (Limits.prod.snd : X ⨯ Y ⟶ Y) :=
        SSet.realizationProdIsoCGWH_hom_snd X Y
      have h2 : piY (E.hom c) = F.map (Limits.prod.snd : X ⨯ Y ⟶ Y) c :=
        (CategoryTheory.comp_apply E.hom piY c).symm.trans
          (ConcreteCategory.congr_hom hE c)
      exact h1.trans (h2.trans hY)
  have hPoint : E.hom c = CGWH.prodPoint A B ax nativeY :=
    (CGWH.prodComparisonToTop_bijective A B).1
      (hCoordinates.trans (CGWH.prodComparisonToTop_prodPoint A B ax nativeY).symm)
  apply (ConcreteCategory.bijective_of_isIso E.hom).1
  exact (Iso.inv_hom_id_apply E (CGWH.prodPoint A B ax nativeY)).trans hPoint.symm

end CategoryTheory

end
