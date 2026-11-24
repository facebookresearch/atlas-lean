/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# Cross-universe and hom-universe nerve map consumer tests

Focused compile-level pins for the down-universe map `nerveMapCross` and both
mixed-composition orientations: ordinary-then-Cross and Cross-then-ordinary.

The ULift sections pin the fully general adapter `SSet.nerveMapULift` and its
bridges to `nerveMap`, `nerveMapHomDown`, and `nerveMapCross`.

The HomDown tests pin independent hom universes in one common ambient object
universe, including the genuine `Type 2` / `Type 1 -> Type 0` case, identity
and all composition shapes, low-dimensional simplicial naturality, and
natural-transformation homotopy endpoints and whiskering.

Nonclaims: no equivalence, realization theorem, weak-equivalence theorem,
Quillen comparison, or global instance.
-/

open CategoryTheory Simplicial MonoidalCategory Opposite
open scoped CategoryTheory.Prod Simplicial

universe v u w v₁ v₂ v₃

namespace MathlibExtTest.CategoryTheory.NerveCrossUniverseTests

noncomputable section

variable {A : Type (max u v)} [Category.{v} A] {B : Type u} [Category.{v} B]

/-- Down-universe nerve map type. -/
example (F : A ⥤ B) : nerve A ⟶ nerve B :=
  CategoryTheory.nerveMapCross F

/-- Ordinary-then-Cross composition collapses to the composed functor. -/
example {X Y : Type (max u v)} [Category.{v} X] [Category.{v} Y]
    {Z : Type u} [Category.{v} Z] (F : X ⥤ Y) (G : Y ⥤ Z) :
    nerveMap F ≫ nerveMapCross G = nerveMapCross (F ⋙ G) :=
  CategoryTheory.nerveMap_nerveMapCross_comp F G

/-- Cross-then-ordinary composition collapses to the composed functor. -/
example {X : Type (max u v)} [Category.{v} X]
    {Y Z : Type u} [Category.{v} Y] [Category.{v} Z] (F : X ⥤ Y) (G : Y ⥤ Z) :
    nerveMapCross F ≫ nerveMap G = nerveMapCross (F ⋙ G) :=
  CategoryTheory.nerveMapCross_nerveMap_comp F G

/-- At coinciding universes, the cross-universe nerve map is the ordinary nerve map. -/
example {A B : Type u} [Category.{0} A] [Category.{0} B] (F : A ⥤ B) :
    nerveMapCross F = nerveMap F :=
  CategoryTheory.nerveMapCross_eq_nerveMap F

section HomDownApi

variable {C D : Type (max w v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]

/-- The common-ambient construction needs no faithfulness hypothesis. -/
example (F : C ⥤ D) : nerve C ⟶ nerve D :=
  CategoryTheory.nerveMapHomDown F

/-- The HomDown map acts literally on vertices. -/
example (F : C ⥤ D) (x : C) :
    (nerveMapHomDown F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  CategoryTheory.nerveMapHomDown_app_mk₀ F x

/-- The HomDown map acts literally on edges. -/
example (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    (nerveMapHomDown F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  CategoryTheory.nerveMapHomDown_app_mk₁ f

example {C D : Type (max w v₁)} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) :
    nerveMapHomDown F = nerveMap F :=
  CategoryTheory.nerveMapHomDown_eq_nerveMap F

example {C : Type (max w v₁)} [Category.{v₁} C] :
    nerveMapHomDown (𝟭 C) = 𝟙 (nerve C) :=
  CategoryTheory.nerveMapHomDown_id

example {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown.{max w v₃, v₁, v₂} F ≫
        nerveMapHomDown.{max w v₁, v₂, v₃} G =
      nerveMapHomDown.{max w v₂, v₁, v₃} (F ⋙ G) :=
  CategoryTheory.nerveMapHomDown_comp F G

example {C D E : Type (max w v₁ v₂)}
    [Category.{v₁} C] [Category.{v₁} D] [Category.{v₂} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap F ≫ nerveMapHomDown G = nerveMapHomDown (F ⋙ G) :=
  CategoryTheory.nerveMap_nerveMapHomDown_comp F G

example {C D E : Type (max w v₁ v₂)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₂} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown F ≫ nerveMap G = nerveMapHomDown (F ⋙ G) :=
  CategoryTheory.nerveMapHomDown_nerveMap_comp F G

section SimplicialNaturality

variable (F : C ⥤ D)

example (i : Fin 2) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapHomDown F).app (op ⦋0⦌) =
      (nerveMapHomDown F).app (op ⦋1⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapHomDown F).naturality _

example (i : Fin 3) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapHomDown F).app (op ⦋1⦌) =
      (nerveMapHomDown F).app (op ⦋2⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapHomDown F).naturality _

example (i : Fin 4) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapHomDown F).app (op ⦋2⦌) =
      (nerveMapHomDown F).app (op ⦋3⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapHomDown F).naturality _

example (i : Fin 1) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapHomDown F).app (op ⦋1⦌) =
      (nerveMapHomDown F).app (op ⦋0⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapHomDown F).naturality _

example (i : Fin 2) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapHomDown F).app (op ⦋2⦌) =
      (nerveMapHomDown F).app (op ⦋1⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapHomDown F).naturality _

example (i : Fin 3) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapHomDown F).app (op ⦋3⦌) =
      (nerveMapHomDown F).app (op ⦋2⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapHomDown F).naturality _

end SimplicialNaturality

section Homotopy

variable {F G : C ⥤ D} (α : F ⟶ G)

example : SSet.Homotopy (nerveMapHomDown F) (nerveMapHomDown G) :=
  CategoryTheory.NatTrans.nerveHomotopyHomDown α

example :
    SSet.ι₀ ≫ (CategoryTheory.NatTrans.nerveHomotopyHomDown α).h =
      nerveMapHomDown F :=
  (CategoryTheory.NatTrans.nerveHomotopyHomDown α).h₀

example :
    SSet.ι₁ ≫ (CategoryTheory.NatTrans.nerveHomotopyHomDown α).h =
      nerveMapHomDown G :=
  (CategoryTheory.NatTrans.nerveHomotopyHomDown α).h₁

example (X : C) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorHomDown α).obj (X, 0) =
      F.obj X := by
  simp

example (X : C) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorHomDown α).obj (X, 1) =
      G.obj X := by
  simp

example {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorHomDown α).map
        (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp

example {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorHomDown α).map
        (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp

end Homotopy

end HomDownApi

section HomotopyWhiskering

variable {X C D E : Type (max w v₁ v₂ v₃)}
  [Category.{v₁} X] [Category.{v₂} C]
  [Category.{v₃} D] [Category.{v₁} E]
  {F G : C ⥤ D}

example (K : X ⥤ C) (α : F ⟶ G) :
    (nerveMapHomDown.{max w v₃, v₁, v₂} K ▷
        (Δ[1] : SSet.{max w v₁ v₂ v₃})) ≫
      CategoryTheory.NatTrans.nerveHomotopyMapHomDown.{max w v₁, v₂, v₃} α =
        CategoryTheory.NatTrans.nerveHomotopyMapHomDown.{max w v₂, v₁, v₃}
          (Functor.whiskerLeft K α) :=
  CategoryTheory.NatTrans.nerveHomotopyMapHomDown_precomp K α

example (α : F ⟶ G) (L : D ⥤ E) :
    CategoryTheory.NatTrans.nerveHomotopyMapHomDown.{max w v₁, v₂, v₃} α ≫
        nerveMapHomDown.{max w v₂, v₃, v₁} L =
      CategoryTheory.NatTrans.nerveHomotopyMapHomDown.{max w v₃, v₂, v₁}
        (Functor.whiskerRight α L) :=
  CategoryTheory.NatTrans.nerveHomotopyMapHomDown_postcomp α L

end HomotopyWhiskering

section UniverseMatrix

variable {Cuv Duv : Type (max u v)}
  [Category.{max u v} Cuv] [Category.{v} Duv]

/-- The exact symbolic hom-down contract needed by the Quillen Stage
projection. -/
example (F : Cuv ⥤ Duv) : nerve Cuv ⟶ nerve Duv :=
  nerveMapHomDown.{0, max u v, v} F

variable {C₀₀ D₀₀ : Type} [Category C₀₀] [Category D₀₀]
variable {C₁₀ D₁₀ : Type 1} [Category.{1} C₁₀] [Category.{0} D₁₀]
variable {C₀₁ D₀₁ : Type 1} [Category.{1} C₀₁] [Category.{1} D₀₁]
variable {CUp DUp : Type 1} [Category.{0} CUp] [Category.{1} DUp]
variable {C₂₁ D₂₀ : Type 2} [Category.{1} C₂₁] [Category.{0} D₂₀]

example (F : C₀₀ ⥤ D₀₀) : nerve C₀₀ ⟶ nerve D₀₀ :=
  nerveMapHomDown.{0, 0, 0} F

example (F : C₁₀ ⥤ D₁₀) : nerve C₁₀ ⟶ nerve D₁₀ :=
  nerveMapHomDown.{0, 1, 0} F

example (F : C₀₁ ⥤ D₀₁) : nerve C₀₁ ⟶ nerve D₀₁ :=
  nerveMapHomDown.{0, 1, 1} F

/-- The common-ambient API is honest in the reverse hom-universe direction
as well, although HomDown is its intended use. -/
example (F : CUp ⥤ DUp) : nerve CUp ⟶ nerve DUp :=
  nerveMapHomDown.{0, 0, 1} F

/-- Object universe `2`, with a genuine hom-universe descent `1 -> 0`. -/
example (F : C₂₁ ⥤ D₂₀) : nerve C₂₁ ⟶ nerve D₂₀ :=
  nerveMapHomDown.{2, 1, 0} F

variable {C₂ D₂ E₂ : Type 2}
  [Category.{2} C₂] [Category.{1} D₂] [Category.{0} E₂]

/-- A genuine two-step hom-universe tower. -/
example (F : C₂ ⥤ D₂) (G : D₂ ⥤ E₂) :
    nerveMapHomDown.{0, 2, 1} F ≫ nerveMapHomDown.{2, 1, 0} G =
      nerveMapHomDown.{1, 2, 0} (F ⋙ G) :=
  CategoryTheory.nerveMapHomDown_comp F G

end UniverseMatrix

section NoFaithfulness

variable {C : Type 1} [Category.{1} C]
  {D : Type 1} [Category.{0} D] (F : C ⥤ D)

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth F.Faithful

example : nerve C ⟶ nerve D := nerveMapHomDown.{0, 1, 0} F

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsIso (nerveMapHomDown.{0, 1, 0} F)

end NoFaithfulness

section Nonclaims

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapHomDown_mem_realizationWeakEquivalences

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapHomDownEquivalence

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapHomDownQuillenComparison

end Nonclaims

#print axioms CategoryTheory.nerveMapHomDown
#print axioms CategoryTheory.nerveMapHomDown_app_mk₀
#print axioms CategoryTheory.nerveMapHomDown_app_mk₁
#print axioms CategoryTheory.nerveMapHomDown_eq_nerveMap
#print axioms CategoryTheory.nerveMapHomDown_id
#print axioms CategoryTheory.nerveMapHomDown_comp
#print axioms CategoryTheory.nerveMap_nerveMapHomDown_comp
#print axioms CategoryTheory.nerveMapHomDown_nerveMap_comp
#print axioms CategoryTheory.NatTrans.nerveCylinderFunctorHomDown
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapHomDown
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapHomDown_precomp
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapHomDown_postcomp
#print axioms CategoryTheory.NatTrans.nerveHomotopyHomDown

universe v₄

section CommonValueApi

variable {C D : Type (max w v₁ v₂)} [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D]

/-- The common-ambient construction needs no faithfulness hypothesis. -/
example (F : C ⥤ D) : nerve C ⟶ nerve D :=
  CategoryTheory.nerveMapCommonValue.{w, v₁, v₂, v₄} F

/-- The CommonValue map acts literally on vertices. -/
example (F : C ⥤ D) (x : C) :
    (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      ComposableArrows.mk₀ (F.obj x) :=
  CategoryTheory.nerveMapCommonValue_app_mk₀.{w, v₁, v₂, v₄} F x

/-- The CommonValue map acts literally on edges. -/
example (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  CategoryTheory.nerveMapCommonValue_app_mk₁.{w, v₁, v₂, v₄} f

example {C D : Type (max w v₁)} [Category.{max v₁ v₄} C] [Category.{max v₁ v₄} D]
    (F : C ⥤ D) :
    nerveMapCommonValue.{w, v₁, v₁, v₄} F = nerveMap F :=
  CategoryTheory.nerveMapCommonValue_eq_nerveMap.{w, v₁, v₄} F

example {C : Type (max w v₁)} [Category.{max v₁ v₄} C] :
    nerveMapCommonValue.{w, v₁, v₁, v₄} (𝟭 C) = 𝟙 (nerve C) :=
  CategoryTheory.nerveMapCommonValue_id.{w, v₁, v₄}

example {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D] [Category.{max v₃ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapCommonValue.{max w v₃, v₁, v₂, v₄} F ≫
        nerveMapCommonValue.{max w v₁, v₂, v₃, v₄} G =
      nerveMapCommonValue.{max w v₂, v₁, v₃, v₄} (F ⋙ G) :=
  CategoryTheory.nerveMapCommonValue_comp.{w, v₁, v₂, v₃, v₄} F G

example {C D E : Type (max w v₁ v₂)}
    [Category.{max v₁ v₄} C] [Category.{max v₁ v₄} D] [Category.{max v₂ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap F ≫ nerveMapCommonValue.{w, v₁, v₂, v₄} G = nerveMapCommonValue.{w, v₁, v₂, v₄} (F ⋙ G) :=
  CategoryTheory.nerveMap_nerveMapCommonValue_comp.{w, v₁, v₂, v₄} F G

example {C D E : Type (max w v₁ v₂)}
    [Category.{max v₁ v₄} C] [Category.{max v₂ v₄} D] [Category.{max v₂ v₄} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapCommonValue.{w, v₁, v₂, v₄} F ≫ nerveMap G = nerveMapCommonValue.{w, v₁, v₂, v₄} (F ⋙ G) :=
  CategoryTheory.nerveMapCommonValue_nerveMap_comp.{w, v₁, v₂, v₄} F G

section SimplicialNaturality

variable (F : C ⥤ D)

example (i : Fin 2) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋0⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

example (i : Fin 3) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋2⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

example (i : Fin 4) :
    (nerve C).map (SimplexCategory.δ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋2⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋3⦌) ≫
        (nerve D).map (SimplexCategory.δ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

example (i : Fin 1) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋0⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

example (i : Fin 2) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋2⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋1⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

example (i : Fin 3) :
    (nerve C).map (SimplexCategory.σ i).op ≫
        (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋3⦌) =
      (nerveMapCommonValue.{w, v₁, v₂, v₄} F).app (op ⦋2⦌) ≫
        (nerve D).map (SimplexCategory.σ i).op :=
  (nerveMapCommonValue.{w, v₁, v₂, v₄} F).naturality _

end SimplicialNaturality

section Homotopy

variable {F G : C ⥤ D} (α : F ⟶ G)

example : SSet.Homotopy (nerveMapCommonValue.{w, v₁, v₂, v₄} F) (nerveMapCommonValue.{w, v₁, v₂, v₄} G) :=
  CategoryTheory.NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, v₄} α

example :
    SSet.ι₀ ≫ (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, v₄} α).h =
      nerveMapCommonValue.{w, v₁, v₂, v₄} F :=
  (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, v₄} α).h₀

example :
    SSet.ι₁ ≫ (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, v₄} α).h =
      nerveMapCommonValue.{w, v₁, v₂, v₄} G :=
  (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, v₄} α).h₁

example (X : C) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).obj (X, 0) =
      F.obj X := by
  simp

example (X : C) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).obj (X, 1) =
      G.obj X := by
  simp

example {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).map
        (f ×ₘ 𝟙 (0 : Fin 2)) = F.map f := by
  simp

example {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.NatTrans.nerveCylinderFunctorCommonValue.{w, v₁, v₂, v₄} α).map
        (f ×ₘ 𝟙 (1 : Fin 2)) = G.map f := by
  simp

end Homotopy

end CommonValueApi

section HomotopyWhiskering

variable {X C D E : Type (max w v₁ v₂ v₃)}
  [Category.{max v₁ v₄} X] [Category.{max v₂ v₄} C]
  [Category.{max v₃ v₄} D] [Category.{max v₁ v₄} E]
  {F G : C ⥤ D}

example (K : X ⥤ C) (α : F ⟶ G) :
    (nerveMapCommonValue.{max w v₃, v₁, v₂, v₄} K ▷
        (Δ[1] : SSet.{max w v₁ v₂ v₃ v₄})) ≫
      CategoryTheory.NatTrans.nerveHomotopyMapCommonValue.{max w v₁, v₂, v₃, v₄} α =
        CategoryTheory.NatTrans.nerveHomotopyMapCommonValue.{max w v₂, v₁, v₃, v₄}
          (Functor.whiskerLeft K α) :=
  CategoryTheory.NatTrans.nerveHomotopyMapCommonValue_precomp.{w, v₁, v₂, v₃, v₄} K α

example (α : F ⟶ G) (L : D ⥤ E) :
    CategoryTheory.NatTrans.nerveHomotopyMapCommonValue.{max w v₁, v₂, v₃, v₄} α ≫
        nerveMapCommonValue.{max w v₂, v₃, v₁, v₄} L =
      CategoryTheory.NatTrans.nerveHomotopyMapCommonValue.{max w v₃, v₂, v₁, v₄}
        (Functor.whiskerRight α L) :=
  CategoryTheory.NatTrans.nerveHomotopyMapCommonValue_postcomp.{w, v₂, v₃, v₁, v₄} α L

end HomotopyWhiskering

section UniverseMatrix

variable {Cuv Duv : Type (max u v)}
  [Category.{max u v} Cuv] [Category.{v} Duv]

/-- The exact symbolic hom-down contract needed by the Quillen Stage
projection. -/
example (F : Cuv ⥤ Duv) : nerve Cuv ⟶ nerve Duv :=
  nerveMapCommonValue.{0, max u v, v, 0} F

variable {C₀₀ D₀₀ : Type} [Category C₀₀] [Category D₀₀]
variable {C₁₀ D₁₀ : Type 1} [Category.{1} C₁₀] [Category.{0} D₁₀]
variable {C₀₁ D₀₁ : Type 1} [Category.{1} C₀₁] [Category.{1} D₀₁]
variable {CUp DUp : Type 1} [Category.{0} CUp] [Category.{1} DUp]
variable {C₂₁ D₂₀ : Type 2} [Category.{1} C₂₁] [Category.{0} D₂₀]

example (F : C₀₀ ⥤ D₀₀) : nerve C₀₀ ⟶ nerve D₀₀ :=
  nerveMapCommonValue.{0, 0, 0, 0} F

example (F : C₁₀ ⥤ D₁₀) : nerve C₁₀ ⟶ nerve D₁₀ :=
  nerveMapCommonValue.{0, 1, 0, 0} F

example (F : C₀₁ ⥤ D₀₁) : nerve C₀₁ ⟶ nerve D₀₁ :=
  nerveMapCommonValue.{0, 1, 1, 0} F

/-- The common-ambient API is honest in the reverse hom-universe direction
as well, although CommonValue is its intended use. -/
example (F : CUp ⥤ DUp) : nerve CUp ⟶ nerve DUp :=
  nerveMapCommonValue.{0, 0, 1, 0} F

/-- Object universe `2`, with a genuine hom-universe descent `1 -> 0`. -/
example (F : C₂₁ ⥤ D₂₀) : nerve C₂₁ ⟶ nerve D₂₀ :=
  nerveMapCommonValue.{2, 1, 0, 0} F

variable {C₂ D₂ E₂ : Type 2}
  [Category.{2} C₂] [Category.{1} D₂] [Category.{0} E₂]

/-- A genuine two-step hom-universe tower. -/
example (F : C₂ ⥤ D₂) (G : D₂ ⥤ E₂) :
    nerveMapCommonValue.{0, 2, 1, 0} F ≫ nerveMapCommonValue.{2, 1, 0, 0} G =
      nerveMapCommonValue.{1, 2, 0, 0} (F ⋙ G) :=
  CategoryTheory.nerveMapCommonValue_comp F G

end UniverseMatrix


section SharedHomAboveObjects

variable {Ccore Dpair : Type u} [Category.{v} Ccore] [Category.{max u v} Dpair]

/-- The exact symbolic core-to-pair pattern retains independent object and hom levels. -/
example (F : Ccore ⥤ Dpair) : nerve Ccore ⟶ nerve Dpair :=
  nerveMapCommonValue.{u, 0, u, v} F

example {F G : Ccore ⥤ Dpair} (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCommonValue.{u, 0, u, v} F)
      (nerveMapCommonValue.{u, 0, u, v} G) :=
  CategoryTheory.NatTrans.nerveHomotopyCommonValue.{u, 0, u, v} α

example {F G : Ccore ⥤ Dpair} (α : F ⟶ G) :
    SSet.ι₀ ≫ (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{u, 0, u, v} α).h =
      nerveMapCommonValue.{u, 0, u, v} F :=
  (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{u, 0, u, v} α).h₀

example {F G : Ccore ⥤ Dpair} (α : F ⟶ G) :
    SSet.ι₁ ≫ (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{u, 0, u, v} α).h =
      nerveMapCommonValue.{u, 0, u, v} G :=
  (CategoryTheory.NatTrans.nerveHomotopyCommonValue.{u, 0, u, v} α).h₁

variable {Csmall Dsmall : Type} [Category.{1} Csmall] [Category.{1} Dsmall]

/-- Hom universe one over object universe zero is now an ordinary canonical case. -/
example (F : Csmall ⥤ Dsmall) : nerve Csmall ⟶ nerve Dsmall :=
  nerveMapCommonValue.{0, 0, 0, 1} F

example {F G : Csmall ⥤ Dsmall} (α : F ⟶ G) :
    SSet.Homotopy (nerveMapCommonValue.{0, 0, 0, 1} F)
      (nerveMapCommonValue.{0, 0, 0, 1} G) :=
  CategoryTheory.NatTrans.nerveHomotopyCommonValue.{0, 0, 0, 1} α

end SharedHomAboveObjects

section NoFaithfulness

variable {C : Type 1} [Category.{1} C]
  {D : Type 1} [Category.{0} D] (F : C ⥤ D)

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth F.Faithful

example : nerve C ⟶ nerve D := nerveMapCommonValue.{0, 1, 0, 0} F

/- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsIso (nerveMapCommonValue.{0, 1, 0, 0} F)

end NoFaithfulness

section Nonclaims

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapCommonValue_mem_realizationWeakEquivalences

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapCommonValueEquivalence

/- error: Unknown -/
#guard_msgs (error, substring := true) in
#check CategoryTheory.nerveMapCommonValueQuillenComparison

end Nonclaims

#print axioms CategoryTheory.nerveMapCommonValue
#print axioms CategoryTheory.nerveMapCommonValue_app_mk₀
#print axioms CategoryTheory.nerveMapCommonValue_app_mk₁
#print axioms CategoryTheory.nerveMapCommonValue_eq_nerveMap
#print axioms CategoryTheory.nerveMapCommonValue_id
#print axioms CategoryTheory.nerveMapCommonValue_comp
#print axioms CategoryTheory.nerveMap_nerveMapCommonValue_comp
#print axioms CategoryTheory.nerveMapCommonValue_nerveMap_comp
#print axioms CategoryTheory.NatTrans.nerveCylinderFunctorCommonValue
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapCommonValue
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapCommonValue_precomp
#print axioms CategoryTheory.NatTrans.nerveHomotopyMapCommonValue_postcomp
#print axioms CategoryTheory.NatTrans.nerveHomotopyCommonValue


section LegacyCompatibility

variable {C D : Type (max w v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]

/-- Ordinary callers retain the exact original three-universe map arity. -/
example (F : C ⥤ D) : nerve C ⟶ nerve D :=
  nerveMapHomDown.{w, v₁, v₂} F

/-- The original map is the exact shared-zero specialization of the new map. -/
example (F : C ⥤ D) :
    nerveMapCommonValue.{w, v₁, v₂, 0} F = nerveMapHomDown.{w, v₁, v₂} F :=
  nerveMapCommonValue_eq_nerveMapHomDown F

example {F G : C ⥤ D} (α : F ⟶ G) :
    NatTrans.nerveHomotopyMapCommonValue.{w, v₁, v₂, 0} α =
      NatTrans.nerveHomotopyMapHomDown.{w, v₁, v₂} α :=
  NatTrans.nerveHomotopyMapCommonValue_eq_nerveHomotopyMapHomDown α

example {F G : C ⥤ D} (α : F ⟶ G) :
    NatTrans.nerveHomotopyCommonValue.{w, v₁, v₂, 0} α =
      NatTrans.nerveHomotopyHomDown.{w, v₁, v₂} α :=
  NatTrans.nerveHomotopyCommonValue_eq_nerveHomotopyHomDown α

/-- The original symbolic composition theorem retains its three-level map API. -/
example {C D E : Type (max w v₁ v₂ v₃)}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown.{max w v₃, v₁, v₂} F ≫
        nerveMapHomDown.{max w v₁, v₂, v₃} G =
      nerveMapHomDown.{max w v₂, v₁, v₃} (F ⋙ G) :=
  nerveMapHomDown_comp F G

/-- The published concrete three-level descent call remains an ordinary client. -/
example {C : Type 1} [Category.{1} C] {D : Type 1} [Category.{0} D]
    (F : C ⥤ D) : nerve C ⟶ nerve D :=
  nerveMapHomDown.{0, 1, 0} F

/-- The old concrete composition also closes using only the simplifier. -/
example {C D E : Type 2} [Category.{2} C] [Category.{1} D] [Category.{0} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    nerveMapHomDown.{0, 2, 1} F ≫ nerveMapHomDown.{2, 1, 0} G =
      nerveMapHomDown.{1, 2, 0} (F ⋙ G) := by
  simp

end LegacyCompatibility


section IndependentObjectAndHomUniverses

universe a b z

variable {C D : Type (max w a b)} [Category.{max a z} C] [Category.{max b z} D]

/- Raising the legacy hom levels also raises its required bundled object levels. -/
/-- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
#check fun (F : C ⥤ D) => nerveMapHomDown.{w, max a z, max b z} F

/-- The common-value map retains the original source and target nerve objects. -/
example (F : C ⥤ D) : nerve C ⟶ nerve D :=
  nerveMapCommonValue.{w, a, b, z} F

/- Object level zero with hom level one is a concrete instance of the obstruction. -/
/-- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
#check fun {C D : Type} [Category.{1} C] [Category.{1} D] (F : C ⥤ D) =>
  nerveMapHomDown.{0, 1, 1} F

end IndependentObjectAndHomUniverses

universe oa va ob vb uc vc

section ULiftAdapter

variable {A₀ : Type oa} [Category.{va} A₀] {B₀ : Type ob} [Category.{vb} B₀]

/-- The adapter acts by postcomposition under one `ULift`. -/
example (G : A₀ ⥤ B₀) (Δ : SimplexCategoryᵒᵖ)
    (X : ((SSet.uliftFunctor.{max ob vb, max oa va}).obj (nerve A₀)).obj Δ) :
    ((SSet.nerveMapULift G).app Δ X).down =
      (G.mapComposableArrows _).obj X.down :=
  SSet.nerveMapULift_app_down G Δ X

/-- The adapter sends identity to identity. -/
example : SSet.nerveMapULift (𝟭 A₀) = 𝟙 _ :=
  SSet.nerveMapULift_id

/-- The adapter preserves composition at shared levels. -/
example {C D E : Type oa} [Category.{va} C] [Category.{va} D]
    [Category.{va} E] (G : C ⥤ D) (H : D ⥤ E) :
    SSet.nerveMapULift (G ⋙ H) =
      SSet.nerveMapULift G ≫ SSet.nerveMapULift H :=
  SSet.nerveMapULift_comp G H

/-- The adapter acts on vertices by the object map. -/
example (G : A₀ ⥤ B₀) (x : A₀) :
    (SSet.nerveMapULift G).app (op ⦋0⦌)
        (ULift.up (ComposableArrows.mk₀ x)) =
      ULift.up (ComposableArrows.mk₀ (G.obj x)) :=
  SSet.nerveMapULift_app_mk₀ G x

/-- The adapter acts on edges by the morphism map. -/
example {G : A₀ ⥤ B₀} {x y : A₀} (f : x ⟶ y) :
    (SSet.nerveMapULift G).app (op ⦋1⦌)
        (ULift.up (ComposableArrows.mk₁ f)) =
      ULift.up (ComposableArrows.mk₁ (G.map f)) :=
  SSet.nerveMapULift_app_mk₁ f

end ULiftAdapter

section ULiftBridges

/-- At shared levels, the adapter is the `ulift` of the ordinary map. -/
example {C D : Type oa} [Category.{va} C] [Category.{va} D]
    (G : C ⥤ D) :
    SSet.nerveMapULift G =
      SSet.uliftFunctor.{max oa va, max oa va}.map (nerveMap G) :=
  SSet.nerveMapULift_eq_ulift_map_nerveMap G

/-- In the common-ambient setting, the adapter is the `ulift` of HomDown. -/
example {C : Type (max w v₁ v₂)} [Category.{v₁} C]
    {D : Type (max w v₁ v₂)} [Category.{v₂} D] (G : C ⥤ D) :
    SSet.nerveMapULift G =
      SSet.uliftFunctor.{max w v₁ v₂, max w v₁ v₂}.map
        (CategoryTheory.nerveMapHomDown G) :=
  SSet.nerveMapULift_eq_ulift_map_nerveMapHomDown G

/-- In the down-universe setting, the adapter is the `ulift` of Cross. -/
example {A : Type (max uc vc)} [Category.{vc} A] {B : Type uc}
    [Category.{vc} B] (G : A ⥤ B) :
    SSet.nerveMapULift G =
      SSet.uliftFunctor.{max uc vc, max uc vc}.map
        (CategoryTheory.nerveMapCross G) :=
  SSet.nerveMapULift_eq_ulift_map_nerveMapCross G

end ULiftBridges

#print axioms SSet.nerveMapULift_id
#print axioms SSet.nerveMapULift_app_mk₀

end

end MathlibExtTest.CategoryTheory.NerveCrossUniverseTests
