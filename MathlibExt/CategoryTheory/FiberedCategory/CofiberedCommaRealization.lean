/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Realization of the cofibered comma/fiber adjunction

The actual comma retraction and strict-fiber inclusion realize to homotopy inverse maps.
Their forward and inverse characteristics give weakness of the original comma inclusion.
Object and morphism universes remain independent.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.IsCofibered

variable {C : Type (max u v)} [Category.{v} C]
  {D : Type u} [Category.{v} D] {p : C ⥤ D} [p.IsCofibered]

/-- The original comma retraction and fibre inclusion are actual realized homotopy inverses. -/
def commaFiberRealizedEquiv (d : D) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj (nerve (CostructuredArrow p d)))
      (SSet.toTop.obj (nerve (Functor.Fiber p d))) := by
  let L := costructuredToFiber (p := p) d
  let R := fiberToCostructuredArrow (p := p) d
  let h : L ⊣ R := costructuredToFiberAdjunction (p := p) d
  let NC : SSet.{max u v} := nerve (CostructuredArrow p d)
  let NF : SSet.{max u v} := nerve (Functor.Fiber p d)
  let f : NC ⟶ NF := nerveMap L
  let g : NF ⟶ NC := nerveMap R
  have hLR : f ≫ g = nerveMap (L ⋙ R) := nerveMap_comp L R
  have hRL : g ≫ f = nerveMap (R ⋙ L) := nerveMap_comp R L
  refine
    { toFun := (SSet.toTop.map f).hom
      invFun := (SSet.toTop.map g).hom
      left_inv := ?_
      right_inv := ?_ }
  · have hu0 : SSet.Homotopy (𝟙 NC) (nerveMap (L ⋙ R)) := by
      simpa only [nerveMap_id] using NatTrans.nerveHomotopy h.unit
    have hu : SSet.Homotopy (𝟙 NC) (f ≫ g) := hLR.symm ▸ hu0
    let ht := SSet.realizeHomotopy NC NC (𝟙 NC) (f ≫ g) hu
    have hComp : (SSet.toTop.map (f ≫ g)).hom =
        (SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 NC)).hom = ContinuousMap.id (SSet.toTop.obj NC) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.symm.cast hComp hId⟩
  · have he0 : SSet.Homotopy (nerveMap (R ⋙ L)) (𝟙 NF) := by
      simpa only [nerveMap_id] using NatTrans.nerveHomotopy h.counit
    have he : SSet.Homotopy (g ≫ f) (𝟙 NF) := hRL.symm ▸ he0
    let ht := SSet.realizeHomotopy NF NF (g ≫ f) (𝟙 NF) he
    have hComp : (SSet.toTop.map (g ≫ f)).hom =
        (SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 NF)).hom = ContinuousMap.id (SSet.toTop.obj NF) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.cast hComp hId⟩

/-- The exact forward map is the original actual comma retraction. -/
theorem commaFiberRealizedEquiv_toFun (d : D) :
    (commaFiberRealizedEquiv (p := p) d).toFun =
      (SSet.toTop.map (nerveMap (costructuredToFiber (p := p) d))).hom := rfl

/-- Its actual inverse is the original strict-fibre-to-comma inclusion. -/
theorem commaFiberRealizedEquiv_invFun (d : D) :
    (commaFiberRealizedEquiv (p := p) d).invFun =
      (SSet.toTop.map (nerveMap (fiberToCostructuredArrow (p := p) d))).hom := rfl

/-- The original comma inclusion is weak, as a consequence of its actual adjunction. -/
theorem fiberToCostructuredArrow_mem_realizationWeakEquivalences (d : D) :
    SSet.realizationWeakEquivalences (nerveMap (fiberToCostructuredArrow (p := p) d)) := by
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (nerveMap (fiberToCostructuredArrow (p := p) d)))
  exact TopCat.mem_of_eq_toFun (commaFiberRealizedEquiv (p := p) d).symm rfl

end CategoryTheory.Functor.IsCofibered

end
