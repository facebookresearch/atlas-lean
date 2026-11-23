/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWHProduct
public import MathlibExt.CategoryTheory.NerveProductLoop
public import MathlibExt.Topology.Category.CGWH.RealizedInterval
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# The whole native classifying product loop

The original product natural-transformation cylinder realizes to the
original active native classifying space paired with the SAME realized
inactive edge. The equality uses the actual realization tensor inverse
and the original classifying-product Iso; every active parameter is kept.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe w v u

namespace CategoryTheory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  {E : Type u} [Category.{v} E]

/-- The actual native realization of the whole original loop cylinder. -/
public def productLoopNativeMap (d : D) (k : d ⟶ d) (F : C × D ⥤ E) :
    classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) ⊗
      CGWH.nativeInterval.{w, max u v} ⟶
        classifyingSpaceCGWH.{w, v, u}.obj (Cat.of E) :=
  (SSet.realizationTensorIsoCGWH.{w, max u v}
    (nerve C) (Δ[1] : SSet.{max u v})).inv ≫
      SSet.toCGWH.{w, max u v}.map
        (NatTrans.nerveHomotopyMap
          (Functor.whiskerRight (productConstantLoop C D d k) F))

private theorem productLoopNativeMap_eq_computed (d : D) (k : d ⟶ d) (F : C × D ⥤ E) :
    productLoopNativeMap.{w} C D d k F =
      (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) ◁
        SSet.toCGWH.{w, max u v}.map (SSet.yonedaEquiv.symm (nerve.edgeMk k).edge)) ≫
          (classifyingSpaceCGWHProductIso.{w} C D).inv ≫
            classifyingSpaceCGWH.{w, v, u}.map F.toCatHom := by
  let G : SSet.{max u v} ⥤ CGWH.{w, max u v} := SSet.toCGWH.{w, max u v}
  let NC : SSet.{max u v} := nerve C
  let ND : SSet.{max u v} := nerve D
  let NE : SSet.{max u v} := nerve E
  let NI : SSet.{max u v} := Δ[1]
  let NP : SSet.{max u v} := nerve (C × D)
  let e : NI ⟶ ND := SSet.yonedaEquiv.symm (nerve.edgeMk k).edge
  let Q : NC ⊗ ND ⟶ NC ⨯ ND :=
    Limits.prod.lift (CartesianMonoidalCategory.fst NC ND)
      (CartesianMonoidalCategory.snd NC ND)
  let nInv : NC ⨯ ND ⟶ NP := (nerveProdIso C D).inv
  let nF : NP ⟶ NE := nerveMap F
  let H : NC ⊗ NI ⟶ NE := NatTrans.nerveHomotopyMap
    (Functor.whiskerRight (productConstantLoop C D d k) F)
  have hpair : Limits.prod.lift
      (CartesianMonoidalCategory.fst NC NI)
      (CartesianMonoidalCategory.snd NC NI ≫ e) = (NC ◁ e) ≫ Q := by
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst, Limits.prod.lift_fst,
        CartesianMonoidalCategory.whiskerLeft_fst]
    · rw [Category.assoc, Limits.prod.lift_snd, Limits.prod.lift_snd,
        CartesianMonoidalCategory.whiskerLeft_snd]
  have hH : H = ((NC ◁ e) ≫ (Q ≫ nInv)) ≫ nF := by
    have h := nerveHomotopyMap_productConstantLoop_postcomp C D d k F
    change H = Limits.prod.lift
      (CartesianMonoidalCategory.fst NC NI)
      (CartesianMonoidalCategory.snd NC NI ≫ e) ≫ nInv ≫ nF at h
    rw [hpair] at h
    simpa only [Category.assoc] using h
  let T₀ : G.obj (NC ⊗ NI) ≅ G.obj NC ⊗ G.obj NI :=
    SSet.realizationTensorIsoCGWH.{w, max u v} NC NI
  let T₁ : G.obj (NC ⊗ ND) ≅ G.obj NC ⊗ G.obj ND :=
    SSet.realizationTensorIsoCGWH.{w, max u v} NC ND
  let P : G.obj NP ≅ G.obj NC ⊗ G.obj ND :=
    classifyingSpaceCGWHProductIso.{w} C D
  let W : G.obj NC ⊗ G.obj NI ⟶ G.obj NC ⊗ G.obj ND :=
    G.obj NC ◁ G.map e
  let fOut : G.obj NP ⟶ G.obj NE := G.map nF
  have hInv : T₁.inv ≫ G.map (Q ≫ nInv) = P.inv :=
    (classifyingSpaceCGWHProductIso_inv_tensor.{w} C D).symm
  have hT : T₀.inv ≫ G.map (NC ◁ e) = W ≫ T₁.inv :=
    SSet.realizationTensorIsoCGWH_inv_whiskerLeft.{w, max u v} NC e
  change T₀.inv ≫ G.map H = W ≫ P.inv ≫ fOut
  calc
    T₀.inv ≫ G.map H = T₀.inv ≫ G.map (((NC ◁ e) ≫ (Q ≫ nInv)) ≫ nF) :=
      congrArg (fun h : NC ⊗ NI ⟶ NE => T₀.inv ≫ G.map h) hH
    _ = (T₀.inv ≫ G.map (NC ◁ e)) ≫ G.map (Q ≫ nInv) ≫ fOut := by
      simp only [fOut, Functor.map_comp, Category.assoc]
    _ = W ≫ (T₁.inv ≫ G.map (Q ≫ nInv)) ≫ fOut := by
      simpa only [Category.assoc] using
        congrArg (fun h : G.obj NC ⊗ G.obj NI ⟶ G.obj (NC ⊗ ND) =>
          h ≫ G.map (Q ≫ nInv) ≫ fOut) hT
    _ = W ≫ P.inv ≫ fOut :=
      congrArg (fun h : G.obj NC ⊗ G.obj ND ⟶ G.obj NP => W ≫ h ≫ fOut) hInv

/-- The whole original cylinder is the literal original native product
family evaluated along the SAME original inactive edge map. -/
public theorem productLoopNativeMap_eq (d : D) (k : d ⟶ d) (F : C × D ⥤ E) :
    productLoopNativeMap.{w} C D d k F =
      (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) ◁
        SSet.toCGWH.{w, max u v}.map (SSet.yonedaEquiv.symm (nerve.edgeMk k).edge)) ≫
          (classifyingSpaceCGWHProductIso.{w} C D).inv ≫
            classifyingSpaceCGWH.{w, v, u}.map F.toCatHom :=
  productLoopNativeMap_eq_computed.{w} C D d k F

/-- Every original active parameter has the exact original paired
realized-edge value, not only the value at the selected unit point. -/
public theorem productLoopNativeMap_apply
    (d : D) (k : d ⟶ d) (F : C × D ⥤ E)
    (a : classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C)) (t : unitInterval) :
    productLoopNativeMap.{w} C D d k F
        (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{w, max u v}.symm t)) =
      (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
        ((classifyingSpaceCGWHProductIso.{w} C D).inv
          (CGWH.tensorMk a (SSet.toCGWH.{w, max u v}.map
            (SSet.yonedaEquiv.symm (nerve.edgeMk k).edge)
              (CGWH.nativeIntervalHomeomorph.{w, max u v}.symm t)))) := by
  rw [productLoopNativeMap_eq]
  change (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
    ((classifyingSpaceCGWHProductIso.{w} C D).inv
      ((classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) ◁ SSet.toCGWH.{w, max u v}.map
        (SSet.yonedaEquiv.symm (nerve.edgeMk k).edge))
          (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{w, max u v}.symm t)))) = _
  rw [CGWH.tensorMk_whiskerLeft]
  rfl

end CategoryTheory

end
