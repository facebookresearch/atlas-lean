/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import MathlibExt.CategoryTheory.NerveProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationTensor
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# The original native classifying product and its points

This Iso composes the existing strict nerve-product Iso, the existing
native realization-product Iso and the selected tensor/product Iso.
Its projection and point laws retain the original two classifying maps.
Object, morphism and compact-probe universes are kept independently.
No ordinary-product inverse or expected classifying comparison is used.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace CategoryTheory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]

/-- Native classifying realization of the actual product category is
the selected native tensor product, through the existing two product Isos. -/
public abbrev classifyingSpaceCGWHProductIso :
    classifyingSpaceCGWH.{w, v, u}.obj (Cat.of (C × D)) ≅
      classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) ⊗
        classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D) :=
  (SSet.toCGWH.{w, max u v}.mapIso (nerveProdIso C D)) ≪≫
    (SSet.realizationProdIsoCGWH.{w, max u v} (nerve C) (nerve D)) ≪≫
      (CGWH.tensorSelectedProductIso
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))).symm

private theorem classifyingSpaceCGWHProductIso_hom_fst_computed :
    (classifyingSpaceCGWHProductIso.{w} C D).hom ≫
      CartesianMonoidalCategory.fst
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) =
      classifyingSpaceCGWH.{w, v, u}.map (Prod.fst C D).toCatHom := by
  let F : SSet.{max u v} ⥤ CGWH.{w, max u v} := SSet.toCGWH.{w, max u v}
  let NC : SSet.{max u v} := nerve C
  let ND : SSet.{max u v} := nerve D
  let NP : SSet.{max u v} := nerve (C × D)
  let eN : NP ≅ NC ⨯ ND := nerveProdIso C D
  let E₀ : F.obj NP ≅ F.obj (NC ⨯ ND) := F.mapIso eN
  let E₁ : F.obj (NC ⨯ ND) ≅ F.obj NC ⨯ F.obj ND :=
    SSet.realizationProdIsoCGWH.{w, max u v} NC ND
  let E₂ : F.obj NC ⊗ F.obj ND ≅ F.obj NC ⨯ F.obj ND :=
    CGWH.tensorSelectedProductIso (F.obj NC) (F.obj ND)
  let pC : NC ⨯ ND ⟶ NC := Limits.prod.fst
  let πC : F.obj NC ⨯ F.obj ND ⟶ F.obj NC := Limits.prod.fst
  let fC : NP ⟶ NC := nerveMap (Prod.fst C D)
  have h₀ : E₀.hom = F.map eN.hom := rfl
  have h₁ : E₁.hom ≫ πC = F.map pC :=
    SSet.realizationProdIsoCGWH_hom_fst NC ND
  have h₂ : E₂.inv ≫ CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) = πC :=
    CGWH.tensorSelectedProductIso_inv_fst (F.obj NC) (F.obj ND)
  have hN : eN.hom ≫ pC = fC := nerveProdIso_hom_comp_fst C D
  change (E₀.hom ≫ E₁.hom ≫ E₂.inv) ≫
      CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) = F.map fC
  calc
    (E₀.hom ≫ E₁.hom ≫ E₂.inv) ≫
        CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) =
      E₀.hom ≫ (E₁.hom ≫
        (E₂.inv ≫ CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND))) :=
      (Category.assoc E₀.hom (E₁.hom ≫ E₂.inv) _).trans
        (congrArg (fun k => E₀.hom ≫ k) (Category.assoc E₁.hom E₂.inv _))
    _ = E₀.hom ≫ (E₁.hom ≫ πC) :=
      congrArg (fun k => E₀.hom ≫ (E₁.hom ≫ k)) h₂
    _ = E₀.hom ≫ F.map pC := congrArg (fun k => E₀.hom ≫ k) h₁
    _ = F.map eN.hom ≫ F.map pC := congrArg (fun k => k ≫ F.map pC) h₀
    _ = F.map (eN.hom ≫ pC) := (F.map_comp eN.hom pC).symm
    _ = F.map fC := congrArg F.map hN

/-- The original first product-category projection is retained exactly. -/
@[reassoc]
public theorem classifyingSpaceCGWHProductIso_hom_fst :
    (classifyingSpaceCGWHProductIso.{w} C D).hom ≫
      CartesianMonoidalCategory.fst
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) =
      classifyingSpaceCGWH.{w, v, u}.map (Prod.fst C D).toCatHom :=
  classifyingSpaceCGWHProductIso_hom_fst_computed C D

private theorem classifyingSpaceCGWHProductIso_hom_snd_computed :
    (classifyingSpaceCGWHProductIso.{w} C D).hom ≫
      CartesianMonoidalCategory.snd
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) =
      classifyingSpaceCGWH.{w, v, u}.map (Prod.snd C D).toCatHom := by
  let F : SSet.{max u v} ⥤ CGWH.{w, max u v} := SSet.toCGWH.{w, max u v}
  let NC : SSet.{max u v} := nerve C
  let ND : SSet.{max u v} := nerve D
  let NP : SSet.{max u v} := nerve (C × D)
  let eN : NP ≅ NC ⨯ ND := nerveProdIso C D
  let E₀ : F.obj NP ≅ F.obj (NC ⨯ ND) := F.mapIso eN
  let E₁ : F.obj (NC ⨯ ND) ≅ F.obj NC ⨯ F.obj ND :=
    SSet.realizationProdIsoCGWH.{w, max u v} NC ND
  let E₂ : F.obj NC ⊗ F.obj ND ≅ F.obj NC ⨯ F.obj ND :=
    CGWH.tensorSelectedProductIso (F.obj NC) (F.obj ND)
  let pD : NC ⨯ ND ⟶ ND := Limits.prod.snd
  let πD : F.obj NC ⨯ F.obj ND ⟶ F.obj ND := Limits.prod.snd
  let fD : NP ⟶ ND := nerveMap (Prod.snd C D)
  have h₀ : E₀.hom = F.map eN.hom := rfl
  have h₁ : E₁.hom ≫ πD = F.map pD :=
    SSet.realizationProdIsoCGWH_hom_snd NC ND
  have h₂ : E₂.inv ≫ CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) = πD :=
    CGWH.tensorSelectedProductIso_inv_snd (F.obj NC) (F.obj ND)
  have hN : eN.hom ≫ pD = fD := nerveProdIso_hom_comp_snd C D
  change (E₀.hom ≫ E₁.hom ≫ E₂.inv) ≫
      CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) = F.map fD
  calc
    (E₀.hom ≫ E₁.hom ≫ E₂.inv) ≫
        CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) =
      E₀.hom ≫ (E₁.hom ≫
        (E₂.inv ≫ CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND))) :=
      (Category.assoc E₀.hom (E₁.hom ≫ E₂.inv) _).trans
        (congrArg (fun k => E₀.hom ≫ k) (Category.assoc E₁.hom E₂.inv _))
    _ = E₀.hom ≫ (E₁.hom ≫ πD) :=
      congrArg (fun k => E₀.hom ≫ (E₁.hom ≫ k)) h₂
    _ = E₀.hom ≫ F.map pD := congrArg (fun k => E₀.hom ≫ k) h₁
    _ = F.map eN.hom ≫ F.map pD := congrArg (fun k => k ≫ F.map pD) h₀
    _ = F.map (eN.hom ≫ pD) := (F.map_comp eN.hom pD).symm
    _ = F.map fD := congrArg F.map hN

/-- The original second product-category projection is retained exactly. -/
@[reassoc]
public theorem classifyingSpaceCGWHProductIso_hom_snd :
    (classifyingSpaceCGWHProductIso.{w} C D).hom ≫
      CartesianMonoidalCategory.snd
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) =
      classifyingSpaceCGWH.{w, v, u}.map (Prod.snd C D).toCatHom :=
  classifyingSpaceCGWHProductIso_hom_snd_computed C D

/-- The product point is the pair of the two ORIGINAL native classifying points. -/
public theorem classifyingSpaceCGWHProductIso_hom_point (c : C) (d : D) :
    (classifyingSpaceCGWHProductIso.{w} C D).hom
        (classifyingSpaceCGWHPoint.{w} (c, d)) =
      CGWH.tensorMk (classifyingSpaceCGWHPoint.{w} c) (classifyingSpaceCGWHPoint.{w} d) := by
  apply (CGWH.tensorEquivProd
    (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C))
    (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))).injective
  rw [CGWH.tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [CGWH.tensorEquivProd_apply_fst]
    exact (ConcreteCategory.congr_hom
      (classifyingSpaceCGWHProductIso_hom_fst.{w} C D)
        (classifyingSpaceCGWHPoint.{w} (c, d))).trans
      (classifyingSpaceCGWH_map_point (Prod.fst C D) (c, d))
  · rw [CGWH.tensorEquivProd_apply_snd]
    exact (ConcreteCategory.congr_hom
      (classifyingSpaceCGWHProductIso_hom_snd.{w} C D)
        (classifyingSpaceCGWHPoint.{w} (c, d))).trans
      (classifyingSpaceCGWH_map_point (Prod.snd C D) (c, d))

/-- Its inverse sends the original pair back to the original product-category point. -/
public theorem classifyingSpaceCGWHProductIso_inv_point (c : C) (d : D) :
    (classifyingSpaceCGWHProductIso.{w} C D).inv
        (CGWH.tensorMk (classifyingSpaceCGWHPoint.{w} c) (classifyingSpaceCGWHPoint.{w} d)) =
      classifyingSpaceCGWHPoint.{w} (c, d) := by
  apply (ConcreteCategory.bijective_of_isIso
    (classifyingSpaceCGWHProductIso.{w} C D).hom).1
  rw [Iso.inv_hom_id_apply]
  have hPoint :
      (classifyingSpaceCGWHProductIso.{w} C D).hom
          (classifyingSpaceCGWHPoint.{w} (c, d)) =
        CGWH.tensorMk (classifyingSpaceCGWHPoint.{w} c) (classifyingSpaceCGWHPoint.{w} d) :=
    classifyingSpaceCGWHProductIso_hom_point C D c d
  exact hPoint.symm

private theorem classifyingSpaceCGWHProductIso_inv_tensor_computed :
    (classifyingSpaceCGWHProductIso.{w} C D).inv =
      (SSet.realizationTensorIsoCGWH.{w, max u v} (nerve C) (nerve D)).inv ≫
        SSet.toCGWH.{w, max u v}.map
          (Limits.prod.lift
            (CartesianMonoidalCategory.fst (nerve C) (nerve D))
            (CartesianMonoidalCategory.snd (nerve C) (nerve D)) ≫
              (nerveProdIso C D).inv) := by
  let F : SSet.{max u v} ⥤ CGWH.{w, max u v} := SSet.toCGWH.{w, max u v}
  let NC : SSet.{max u v} := nerve C
  let ND : SSet.{max u v} := nerve D
  let NP : SSet.{max u v} := nerve (C × D)
  let eN : NP ≅ NC ⨯ ND := nerveProdIso C D
  let E : F.obj NP ≅ F.obj NC ⊗ F.obj ND :=
    classifyingSpaceCGWHProductIso.{w} C D
  let T : F.obj (NC ⊗ ND) ≅ F.obj NC ⊗ F.obj ND :=
    SSet.realizationTensorIsoCGWH.{w, max u v} NC ND
  let Q : NC ⊗ ND ⟶ NC ⨯ ND :=
    Limits.prod.lift (CartesianMonoidalCategory.fst NC ND)
      (CartesianMonoidalCategory.snd NC ND)
  let fC : NP ⟶ NC := nerveMap (Prod.fst C D)
  let fD : NP ⟶ ND := nerveMap (Prod.snd C D)
  let pC : NC ⨯ ND ⟶ NC := Limits.prod.fst
  let pD : NC ⨯ ND ⟶ ND := Limits.prod.snd
  let k : F.obj NC ⊗ F.obj ND ⟶ F.obj NP := T.inv ≫ F.map (Q ≫ eN.inv)
  have hNfst : eN.hom ≫ pC = fC := nerveProdIso_hom_comp_fst C D
  have hNsnd : eN.hom ≫ pD = fD := nerveProdIso_hom_comp_snd C D
  have hInvfst : eN.inv ≫ fC = pC :=
    (congrArg (fun f => eN.inv ≫ f) hNfst.symm).trans
      (eN.inv_hom_id_assoc pC)
  have hInvsnd : eN.inv ≫ fD = pD :=
    (congrArg (fun f => eN.inv ≫ f) hNsnd.symm).trans
      (eN.inv_hom_id_assoc pD)
  have hQfst : Q ≫ eN.inv ≫ fC = CartesianMonoidalCategory.fst NC ND :=
    (congrArg (fun f => Q ≫ f) hInvfst).trans (Limits.prod.lift_fst _ _)
  have hQsnd : Q ≫ eN.inv ≫ fD = CartesianMonoidalCategory.snd NC ND :=
    (congrArg (fun f => Q ≫ f) hInvsnd).trans (Limits.prod.lift_snd _ _)
  have hEfst : E.hom ≫ CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) = F.map fC :=
    classifyingSpaceCGWHProductIso_hom_fst C D
  have hEsnd : E.hom ≫ CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) = F.map fD :=
    classifyingSpaceCGWHProductIso_hom_snd C D
  have hkfst : k ≫ F.map fC = CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) := by
    calc
      k ≫ F.map fC = (T.inv ≫ F.map (Q ≫ eN.inv)) ≫ F.map fC := rfl
      _ = T.inv ≫ (F.map (Q ≫ eN.inv) ≫ F.map fC) := Category.assoc _ _ _
      _ = T.inv ≫ F.map ((Q ≫ eN.inv) ≫ fC) :=
        congrArg (fun f => T.inv ≫ f) (F.map_comp (Q ≫ eN.inv) fC).symm
      _ = T.inv ≫ F.map (Q ≫ eN.inv ≫ fC) :=
        congrArg (fun f => T.inv ≫ F.map f) (Category.assoc Q eN.inv fC)
      _ = T.inv ≫ F.map (CartesianMonoidalCategory.fst NC ND) :=
        congrArg (fun f => T.inv ≫ F.map f) hQfst
      _ = CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) :=
        SSet.realizationTensorIsoCGWH_inv_fst NC ND
  have hksnd : k ≫ F.map fD = CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) := by
    calc
      k ≫ F.map fD = (T.inv ≫ F.map (Q ≫ eN.inv)) ≫ F.map fD := rfl
      _ = T.inv ≫ (F.map (Q ≫ eN.inv) ≫ F.map fD) := Category.assoc _ _ _
      _ = T.inv ≫ F.map ((Q ≫ eN.inv) ≫ fD) :=
        congrArg (fun f => T.inv ≫ f) (F.map_comp (Q ≫ eN.inv) fD).symm
      _ = T.inv ≫ F.map (Q ≫ eN.inv ≫ fD) :=
        congrArg (fun f => T.inv ≫ F.map f) (Category.assoc Q eN.inv fD)
      _ = T.inv ≫ F.map (CartesianMonoidalCategory.snd NC ND) :=
        congrArg (fun f => T.inv ≫ F.map f) hQsnd
      _ = CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) :=
        SSet.realizationTensorIsoCGWH_inv_snd NC ND
  have hkE : k ≫ E.hom = 𝟙 (F.obj NC ⊗ F.obj ND) := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (k ≫ E.hom) ≫ CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) =
            k ≫ (E.hom ≫ CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND)) :=
          Category.assoc _ _ _
        _ = k ≫ F.map fC := congrArg (fun f => k ≫ f) hEfst
        _ = CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) := hkfst
        _ = (𝟙 (F.obj NC ⊗ F.obj ND)) ≫
            CartesianMonoidalCategory.fst (F.obj NC) (F.obj ND) :=
          (Category.id_comp _).symm
    · calc
        (k ≫ E.hom) ≫ CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) =
            k ≫ (E.hom ≫ CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND)) :=
          Category.assoc _ _ _
        _ = k ≫ F.map fD := congrArg (fun f => k ≫ f) hEsnd
        _ = CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) := hksnd
        _ = (𝟙 (F.obj NC ⊗ F.obj ND)) ≫
            CartesianMonoidalCategory.snd (F.obj NC) (F.obj ND) :=
          (Category.id_comp _).symm
  change E.inv = k
  exact (cancel_mono E.hom).mp ((Iso.inv_hom_id E).trans hkE.symm)

/-- The inverse of the ORIGINAL native classifying product Iso is the
actual realization tensor inverse followed by the SAME strict nerve pair.
The equality is derived from both original projection equations. -/
public theorem classifyingSpaceCGWHProductIso_inv_tensor :
    (classifyingSpaceCGWHProductIso.{w} C D).inv =
      (SSet.realizationTensorIsoCGWH.{w, max u v} (nerve C) (nerve D)).inv ≫
        SSet.toCGWH.{w, max u v}.map
          (Limits.prod.lift
            (CartesianMonoidalCategory.fst (nerve C) (nerve D))
            (CartesianMonoidalCategory.snd (nerve C) (nerve D)) ≫
              (nerveProdIso C D).inv) :=
  classifyingSpaceCGWHProductIso_inv_tensor_computed C D

end CategoryTheory

end
