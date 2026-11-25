/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Totalization of diagrams with specified totals

Totalization is an additive functor on the full subcategory of bicomplexes
whose totals exist. A diagram in this subcategory therefore totalizes
without requiring totals for every bicomplex. Natural transformations
retain their component maps and diagonal coprojection formulas.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex₂.total

universe uC vC u₁ u₂ u₁₂

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {I₁ : Type u₁} {I₂ : Type u₂} {I₁₂ : Type u₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c₁₂] [L.HasTotal c₁₂]

/-- The native total of the original zero map is zero on every original coprojection. -/
@[simp]
theorem map_zero : total.map (0 : K ⟶ L) c₁₂ = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply total.hom_ext c₁₂
  intro i j h
  simp only [HomologicalComplex.zero_f_apply, ιTotal_map, comp_zero, zero_comp]

/-- The native total map is additive without a global totalization assumption. -/
@[simp]
theorem map_add (f g : K ⟶ L) : total.map (f + g) c₁₂ = total.map f c₁₂ + total.map g c₁₂ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply total.hom_ext c₁₂
  intro i j h
  simp only [HomologicalComplex.add_f_apply, Preadditive.comp_add,
    ιTotal_map, Preadditive.add_comp]

end HomologicalComplex₂.total

namespace HomologicalComplex₂

universe uC vC u₁ u₂ u₁₂ uJ vJ

section PartialTotal

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  {I₁ : Type u₁} {I₂ : Type u₂} {I₁₂ : Type u₁₂}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂]

/-- The original bicomplex admits its displayed native total. -/
def hasTotalProperty : ObjectProperty (HomologicalComplex₂ C c₁ c₂) :=
  fun K => K.HasTotal c₁₂

/-- Original bicomplexes with an actual total, and all original bicomplex maps. -/
abbrev BicomplexWithTotal := (hasTotalProperty C c₁ c₂ c₁₂).FullSubcategory

instance bicomplexWithTotal_hasTotal (K : BicomplexWithTotal C c₁ c₂ c₁₂) :
    K.obj.HasTotal c₁₂ := K.property

variable [DecidableEq I₁₂]

/-- The native totalization functor on exactly the objects with the displayed total. -/
def totalFunctorOnHasTotal : BicomplexWithTotal C c₁ c₂ c₁₂ ⥤ HomologicalComplex C c₁₂ where
  obj K := K.obj.total c₁₂
  map f := total.map f.hom c₁₂
  map_id K := total.map_id K.obj c₁₂
  map_comp f g := total.map_comp f.hom g.hom c₁₂

instance totalFunctorOnHasTotal_additive : (totalFunctorOnHasTotal C c₁ c₂ c₁₂).Additive where
  map_add {_K _L f g} := total.map_add c₁₂ f.hom g.hom

variable {C c₁ c₂ c₁₂}

@[simp]
theorem totalFunctorOnHasTotal_obj (K : BicomplexWithTotal C c₁ c₂ c₁₂) :
    (totalFunctorOnHasTotal C c₁ c₂ c₁₂).obj K = K.obj.total c₁₂ := rfl

@[simp]
theorem totalFunctorOnHasTotal_map {K L : BicomplexWithTotal C c₁ c₂ c₁₂} (f : K ⟶ L) :
    (totalFunctorOnHasTotal C c₁ c₂ c₁₂).map f = total.map f.hom c₁₂ := rfl

/-- The partial functor retains the original diagonal-coordinate equation. -/
@[reassoc]
theorem totalFunctorOnHasTotal_map_ι {K L : BicomplexWithTotal C c₁ c₂ c₁₂} (f : K ⟶ L)
    (i : I₁) (j : I₂) (n : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i, j) = n) :
    K.obj.ιTotal c₁₂ i j n h ≫ ((totalFunctorOnHasTotal C c₁ c₂ c₁₂).map f).f n =
      (f.hom.f i).f j ≫ L.obj.ιTotal c₁₂ i j n h :=
  ιTotal_map K.obj L.obj f.hom c₁₂ i j n h

/-- Where global totalization exists, its restriction is the same original functor. -/
theorem totalFunctorOnHasTotal_eq_comp
    [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotal c₁₂] :
    totalFunctorOnHasTotal C c₁ c₂ c₁₂ =
      (hasTotalProperty C c₁ c₂ c₁₂).ι ⋙ totalFunctor C c₁ c₂ c₁₂ := rfl

instance totalFunctor_additive
    [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotal c₁₂] :
    (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add {_K _L f g} := total.map_add c₁₂ f g

end PartialTotal

section Diagrams

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {I₁ : Type u₁} {I₂ : Type u₂} {I₁₂ : Type u₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {J : Type uJ} [Category.{vJ} J]

/-- Totalization of an actual strict diagram requires only that diagram's actual totals. -/
def totalDiagram (K : J ⥤ HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] : J ⥤ HomologicalComplex C c₁₂ :=
  (hasTotalProperty C c₁ c₂ c₁₂).lift K (fun j => show (K.obj j).HasTotal c₁₂ from inferInstance) ⋙
    totalFunctorOnHasTotal C c₁ c₂ c₁₂

@[simp]
theorem totalDiagram_obj (K : J ⥤ HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] (j : J) :
    (totalDiagram K c₁₂).obj j = (K.obj j).total c₁₂ := rfl

@[simp]
theorem totalDiagram_map (K : J ⥤ HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] {i j : J} (f : i ⟶ j) :
    (totalDiagram K c₁₂).map f = total.map (K.map f) c₁₂ := rfl

instance totalDiagram_additive [Preadditive J]
    (K : J ⥤ HomologicalComplex₂ C c₁ c₂) [K.Additive] (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] : (totalDiagram K c₁₂).Additive where
  map_add {_i _j f g} := by
    change total.map (K.map (f + g)) c₁₂ =
      total.map (K.map f) c₁₂ + total.map (K.map g) c₁₂
    rw [K.map_add, total.map_add]

/-- An original transformation gives its actual componentwise native total maps. -/
def totalDiagramMap {K L : J ⥤ HomologicalComplex₂ C c₁ c₂} (α : K ⟶ L)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] [∀ j, (L.obj j).HasTotal c₁₂] :
    totalDiagram K c₁₂ ⟶ totalDiagram L c₁₂ where
  app j := total.map (α.app j) c₁₂
  naturality {i j} f := by
    change total.map (K.map f) c₁₂ ≫ total.map (α.app j) c₁₂ =
      total.map (α.app i) c₁₂ ≫ total.map (L.map f) c₁₂
    rw [← total.map_comp, ← total.map_comp, α.naturality]

@[simp]
theorem totalDiagramMap_app {K L : J ⥤ HomologicalComplex₂ C c₁ c₂} (α : K ⟶ L)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] [∀ j, (L.obj j).HasTotal c₁₂] (j : J) :
    (totalDiagramMap α c₁₂).app j = total.map (α.app j) c₁₂ := rfl

@[simp]
theorem totalDiagramMap_id (K : J ⥤ HomologicalComplex₂ C c₁ c₂)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] :
    totalDiagramMap (𝟙 K) c₁₂ = 𝟙 (totalDiagram K c₁₂) := by
  apply NatTrans.ext
  funext j
  change total.map (𝟙 (K.obj j)) c₁₂ = 𝟙 ((K.obj j).total c₁₂)
  exact total.map_id (K.obj j) c₁₂

@[simp]
theorem totalDiagramMap_comp {K L M : J ⥤ HomologicalComplex₂ C c₁ c₂}
    (α : K ⟶ L) (β : L ⟶ M) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] [∀ j, (L.obj j).HasTotal c₁₂]
    [∀ j, (M.obj j).HasTotal c₁₂] :
    totalDiagramMap (α ≫ β) c₁₂ = totalDiagramMap α c₁₂ ≫ totalDiagramMap β c₁₂ := by
  apply NatTrans.ext
  funext j
  change total.map (α.app j ≫ β.app j) c₁₂ =
    total.map (α.app j) c₁₂ ≫ total.map (β.app j) c₁₂
  exact total.map_comp (α.app j) (β.app j) c₁₂

@[simp]
theorem totalDiagramMap_zero (K L : J ⥤ HomologicalComplex₂ C c₁ c₂)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] [∀ j, (L.obj j).HasTotal c₁₂] :
    totalDiagramMap (0 : K ⟶ L) c₁₂ = 0 := by
  apply NatTrans.ext
  funext j
  change total.map (0 : K.obj j ⟶ L.obj j) c₁₂ = 0
  exact total.map_zero (K := K.obj j) (L := L.obj j) c₁₂

/-- Addition of original transformations gives addition of their actual total maps. -/
theorem totalDiagramMap_add {K L : J ⥤ HomologicalComplex₂ C c₁ c₂}
    (α β : K ⟶ L) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ j, (K.obj j).HasTotal c₁₂] [∀ j, (L.obj j).HasTotal c₁₂] :
    totalDiagramMap (α + β) c₁₂ = totalDiagramMap α c₁₂ + totalDiagramMap β c₁₂ := by
  apply NatTrans.ext
  funext j
  change total.map (α.app j + β.app j) c₁₂ =
    total.map (α.app j) c₁₂ + total.map (β.app j) c₁₂
  exact total.map_add c₁₂ (α.app j) (β.app j)

end Diagrams

end HomologicalComplex₂
