/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.FinitePowerSite
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Original finite-site transport contracts

The clients retain whole original arrows, a nonmonic simplex collapse, the ordered two-coordinate
constancy arrow, and an actual nonidentity factor in the product/opposite transport.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.FinitePowerSite Opposite
open scoped Simplicial CategoryTheory.Prod

namespace CategoryTheory.FinitePowerSiteTest

example (n : ℕ) : ((Source n)ᵒᵖ ⥤ SSet.{u}) ≌ (Index n ⥤ SSet.{u}) :=
  diagramEquiv n SSet.{u}

example (n : ℕ) {x y : Index n} (f : x ⟶ y) :
    HEq ((sourceOpEquiv n).inverse.map f)
      (Quiver.Hom.op (X := fun i => (y i).unop) (Y := fun i => (x i).unop)
        (fun i => (f i).unop)) :=
  sourceOpEquiv_inverse_map n f

example (n : ℕ) {X Y : (Source n)ᵒᵖ ⥤ SSet.{u}} (f : X ⟶ Y) (x : Index n) :
    ((diagramEquiv n SSet.{u}).functor.map f).app x =
      f.app ((sourceOpEquiv n).inverse.obj x) :=
  diagramEquiv_functor_map_app n f x

private def simplexCollapse : SSet.stdSimplex.{u}.obj ⦋1⦌ ⟶ SSet.stdSimplex.{u}.obj ⦋0⦌ :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

private theorem simplexCollapse_not_mono : ¬ Mono (simplexCollapse.{u}) := by
  intro h
  change Mono (SSet.stdSimplex.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)) at h
  have hm := (SSet.stdSimplex.{u}).mono_of_mono_map h
  have hi := SimplexCategory.mono_iff_injective.mp hm
  exact (by decide : (0 : Fin 2) ≠ 1) (hi rfl)

private def collapseArrow (n : ℕ) : Arrow (Index n ⥤ SSet.{u}) :=
  Arrow.mk ((Functor.const (Index n)).map simplexCollapse)

private theorem collapseArrow_not_mono (n : ℕ) : ¬ Mono (collapseArrow.{u} n).hom := by
  intro h
  let _ := h
  have hm : Mono ((collapseArrow.{u} n).hom.app (fun _ => op ⦋0⦌)) := inferInstance
  exact simplexCollapse_not_mono hm

example : ¬ Mono (collapseArrow.{u} 2).hom := collapseArrow_not_mono 2

example :
    (diagramEquiv 2 SSet.{u}).functor.map
        ((diagramEquiv 2 SSet.{u}).inverse.map (collapseArrow 2).hom) ≫
      (targetArrowCounitIso 2 (collapseArrow 2)).hom.right =
        (targetArrowCounitIso 2 (collapseArrow 2)).hom.left ≫ (collapseArrow 2).hom :=
  targetArrowCounitIso_hom_square 2 (collapseArrow 2)

example :
    (collapseArrow.{u} 2).hom ≫ (targetArrowCounitIso 2 (collapseArrow 2)).inv.right =
      (targetArrowCounitIso 2 (collapseArrow 2)).inv.left ≫
        (diagramEquiv 2 SSet.{u}).functor.map
          ((diagramEquiv 2 SSet.{u}).inverse.map (collapseArrow 2).hom) :=
  targetArrowCounitIso_inv_square 2 (collapseArrow 2)

example (X : SSet.{u}) (a : Index 0) :
    ((zeroDiagramEquiv SSet.{u}).inverse.obj X).obj a = X :=
  zeroDiagramEquiv_inverse_obj X a

example {X Y : SSet.{u}} (f : X ⟶ Y) (a : Index 0) :
    ((zeroDiagramEquiv SSet.{u}).inverse.map f).app a = f :=
  zeroDiagramEquiv_inverse_map_app f a

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (a : Index 1) :
    ((oneDiagramEquiv SSet.{u}).inverse.obj X).obj a = X.obj (a 0) :=
  oneDiagramEquiv_inverse_obj X a

example (x y : SimplexCategoryᵒᵖ) :
    ((orderedSplitIndex 1).functor.obj (Fin.cases x (fun _ : Fin 1 => y))).1 = x ∧
      ((orderedSplitIndex 1).functor.obj (Fin.cases x (fun _ : Fin 1 => y))).2 0 = y :=
  ⟨orderedSplitTwo_first x y, orderedSplitTwo_second x y⟩

private def constancySource : Source 2 := Fin.cases ⦋0⦌ (fun _ : Fin 1 => ⦋1⦌)

private def constancyTarget : Source 2 := fun _ => ⦋0⦌

private def constancyIndexMap : constancySource ⟶ constancyTarget :=
  Fin.cases (𝟙 ⦋0⦌) (fun _ : Fin 1 => SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

private def discreteValue : Type ⥤ SSet.{0} := Functor.const SimplexCategoryᵒᵖ

/-- The original F(0,1)→F(0,0) arrow, as constant-inner representable diagrams. -/
private def constancyArrow : Arrow ((Source 2)ᵒᵖ ⥤ SSet.{0}) :=
  Arrow.mk (((Functor.whiskeringRight (Source 2)ᵒᵖ (Type) SSet.{0}).obj discreteValue).map
    (yoneda.map constancyIndexMap))

example :
    constancyArrow.hom ≫ (sourceArrowUnitIso 2 constancyArrow).hom.right =
      (sourceArrowUnitIso 2 constancyArrow).hom.left ≫
        (diagramEquiv 2 SSet.{0}).inverse.map
          ((diagramEquiv 2 SSet.{0}).functor.map constancyArrow.hom) :=
  sourceArrowUnitIso_hom_square 2 constancyArrow

example : constancyIndexMap 0 = 𝟙 ⦋0⦌ := rfl

example : constancyIndexMap 1 = SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 := rfl

example (n : ℕ) {g h : SimplexCategory} (f : g ⟶ h) {a b : Index n} (k : a ⟶ b) :
    HEq ((productSourceOpEquiv n SimplexCategory).inverse.map (f ×ₘ k))
      (Quiver.Hom.op (X := (op h, fun i => (b i).unop))
        (Y := (op g, fun i => (a i).unop)) (f.op ×ₘ (fun i => (k i).unop))) :=
  productSourceOpEquiv_inverse_map n f k

example :
    HEq ((productSourceOpEquiv 2 SimplexCategory).inverse.map
      (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 ×ₘ
        (sourceOpEquiv 2).functor.map constancyIndexMap.op))
      (Quiver.Hom.op (X := (op ⦋0⦌, constancySource))
        (Y := (op ⦋1⦌, constancyTarget))
        ((SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op ×ₘ constancyIndexMap)) := by
  rfl

example (n : ℕ) (X : (SimplexCategoryᵒᵖ × Source n)ᵒᵖ ⥤ SSet.{u + 1}) :
    ((productDiagramEquiv n SimplexCategory SSet.{u + 1}).functor.obj X).obj
      (⦋0⦌, fun _ => op ⦋0⦌) =
      X.obj ((productSourceOpEquiv n SimplexCategory).inverse.obj
        (⦋0⦌, fun _ => op ⦋0⦌)) :=
  productDiagramEquiv_functor_obj n X _

end CategoryTheory.FinitePowerSiteTest
