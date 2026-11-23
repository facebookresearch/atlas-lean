/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.FiberedComma
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Realization of the original fibered left-comma adjunction

The strict fiber includes in the actual structured-arrow category.
The chosen Cartesian right adjoint and the actual inclusion realize to
homotopy inverse maps. Both their maps and the entire unit/counit homotopies
are retained, with a common native value universe and arbitrary Hom levels.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.IsPreFibered

variable {S : Type u} [Category.{v} S]
  {X : Type (max u v)} [Category.{v} X] {p : X ⥤ S} [p.IsPreFibered]

/-- The original fiber inclusion realizes with its actual chosen Cartesian right adjoint. -/
def fiberCommaRealizedEquiv (s : S) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj (nerve (Functor.Fiber p s)))
      (SSet.toTop.obj (nerve (StructuredArrow s p))) := by
  let L := Functor.fiberToStructuredArrow (p := p) s
  let R := structuredToFiber (p := p) s
  let h : L ⊣ R := fiberToStructuredArrowAdjunction (p := p) s
  let N₁ : SSet.{max u v} := nerve (Functor.Fiber p s)
  let N₂ : SSet.{max u v} := nerve (StructuredArrow s p)
  let f : N₁ ⟶ N₂ := nerveMap L
  let g : N₂ ⟶ N₁ := nerveMap R
  have hLR : f ≫ g = nerveMap (L ⋙ R) := nerveMap_comp L R
  have hRL : g ≫ f = nerveMap (R ⋙ L) := nerveMap_comp R L
  refine
    { toFun := (SSet.toTop.map f).hom
      invFun := (SSet.toTop.map g).hom
      left_inv := ?_
      right_inv := ?_ }
  · have hu0 : SSet.Homotopy (𝟙 N₁) (nerveMap (L ⋙ R)) := by
      simpa only [nerveMap_id] using NatTrans.nerveHomotopy h.unit
    have hu : SSet.Homotopy (𝟙 N₁) (f ≫ g) := hLR.symm ▸ hu0
    let ht := SSet.realizeHomotopy N₁ N₁ (𝟙 N₁) (f ≫ g) hu
    have hComp : (SSet.toTop.map (f ≫ g)).hom =
        (SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 N₁)).hom = ContinuousMap.id (SSet.toTop.obj N₁) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.symm.cast hComp hId⟩
  · have he0 : SSet.Homotopy (nerveMap (R ⋙ L)) (𝟙 N₂) := by
      simpa only [nerveMap_id] using NatTrans.nerveHomotopy h.counit
    have he : SSet.Homotopy (g ≫ f) (𝟙 N₂) := hRL.symm ▸ he0
    let ht := SSet.realizeHomotopy N₂ N₂ (g ≫ f) (𝟙 N₂) he
    have hComp : (SSet.toTop.map (g ≫ f)).hom =
        (SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom := by
      rewrite [SSet.toTop.map_comp]
      rfl
    have hId : (SSet.toTop.map (𝟙 N₂)).hom = ContinuousMap.id (SSet.toTop.obj N₂) := by
      rewrite [SSet.toTop.map_id]
      rfl
    exact ⟨ht.cast hComp hId⟩

/-- The forward map is exactly the original strict-fiber inclusion in the left comma. -/
theorem fiberCommaRealizedEquiv_toFun (s : S) :
    (fiberCommaRealizedEquiv (p := p) s).toFun =
      (SSet.toTop.map (nerveMap (Functor.fiberToStructuredArrow (p := p) s))).hom := rfl

/-- The inverse map is exactly the actual chosen Cartesian right adjoint. -/
theorem fiberCommaRealizedEquiv_invFun (s : S) :
    (fiberCommaRealizedEquiv (p := p) s).invFun =
      (SSet.toTop.map (nerveMap (structuredToFiber (p := p) s))).hom := rfl

/-- Weakness of the actual inclusion follows from its original adjunction. -/
theorem fiberToStructuredArrow_mem_realizationWeakEquivalences (s : S) :
    SSet.realizationWeakEquivalences (nerveMap (Functor.fiberToStructuredArrow (p := p) s)) := by
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (nerveMap (Functor.fiberToStructuredArrow (p := p) s)))
  exact TopCat.mem_of_eq_toFun (fiberCommaRealizedEquiv (p := p) s) rfl

end CategoryTheory.Functor.IsPreFibered

end
