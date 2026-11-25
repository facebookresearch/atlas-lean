/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.CategoryTheory.Monoidal.DualComparison
import MathlibExt.CategoryTheory.Monoidal.RelCat
import Mathlib.Algebra.Category.FGModuleCat.Basic
open CategoryTheory MonoidalCategory
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]
example (X : C) [HasRightDual X] [HasRightDual (F.obj X)] :
    F.obj (Xᘁ) ≅ (F.obj X)ᘁ := F.mapRightDualIso X

open Functor.LaxMonoidal Functor.OplaxMonoidal

-- All statements remain usable without symmetric or braided structures.
example (X : C) [HasRightDual X] [HasRightDual (F.obj X)] :
    (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫ F.obj X ◁ (F.mapRightDualIso X).hom =
      η_ (F.obj X) ((F.obj X)ᘁ) := F.mapRightDualIso_coevaluation X
example (X : C) [HasRightDual X] [HasRightDual (F.obj X)] :
    (F.mapRightDualIso X).hom ▷ F.obj X ≫ ε_ (F.obj X) ((F.obj X)ᘁ) =
      μ F (Xᘁ) X ≫ F.map (ε_ X (Xᘁ)) ≫ η F := F.mapRightDualIso_evaluation X
example {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual (F.obj X)] [HasRightDual (F.obj Y)] (f : X ⟶ Y) :
    F.map (fᘁ) ≫ (F.mapRightDualIso X).hom =
      (F.mapRightDualIso Y).hom ≫ (F.map f)ᘁ := F.mapRightDualIso_naturality f
example {X Y : C} [HasRightDual X] [HasRightDual Y]
    [HasRightDual (F.obj X)] [HasRightDual (F.obj Y)] (f : X ⟶ Y) :
    (F.mapRightDualIso Y).inv ≫ F.map (fᘁ) ≫ (F.mapRightDualIso X).hom = (F.map f)ᘁ := by
  rw [F.mapRightDualIso_naturality]
  simp
example (X : C) [HasRightDual X] [HasRightDual (F.obj X)]
    (g : F.obj (Xᘁ) ⟶ (F.obj X)ᘁ)
    (h : (ε F ≫ F.map (η_ X (Xᘁ)) ≫ δ F X (Xᘁ)) ≫ F.obj X ◁ g =
      η_ (F.obj X) ((F.obj X)ᘁ)) : g = (F.mapRightDualIso X).hom :=
  F.mapRightDualIso_hom_unique X g h

-- Named pairings are independent of global choices of dual objects.
example {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    p.coevaluation' ≫ X ◁ (rightDualIso p q).hom = q.coevaluation' :=
  coevaluation_comp_rightDualIso p q
example {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) :
    (rightDualIso p q).hom ▷ X ≫ q.evaluation' = p.evaluation' :=
  rightDualIso_comp_evaluation p q
example {X Y Z : C} (p : ExactPairing X Y) (q : ExactPairing X Z) (f g : Y ⟶ Z)
    (hf : p.coevaluation' ≫ X ◁ f = q.coevaluation')
    (hg : p.coevaluation' ≫ X ◁ g = q.coevaluation') : f = g :=
  (rightDualIso_hom_unique p q f hf).trans (rightDualIso_hom_unique p q g hg).symm

-- Identity/composition use local projection bridges rather than new global dual instances.
local instance (X : C) [HasRightDual X] : HasRightDual ((𝟭 C).obj X) :=
  inferInstanceAs (HasRightDual X)
example (X : C) [HasRightDual X] :
    (𝟭 C).mapRightDualIso X = Iso.refl (Xᘁ) := Functor.mapRightDualIso_id X
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] (G : D ⥤ E) [G.Monoidal]
local instance (X : C) [HasRightDual (G.obj (F.obj X))] : HasRightDual ((F ⋙ G).obj X) :=
  inferInstanceAs (HasRightDual (G.obj (F.obj X)))
example (X : C) [HasRightDual X] [HasRightDual (F.obj X)] [HasRightDual (G.obj (F.obj X))] :
    (F ⋙ G).mapRightDualIso X = G.mapIso (F.mapRightDualIso X) ≪≫ G.mapRightDualIso (F.obj X) :=
  F.mapRightDualIso_comp G X

noncomputable section
-- Unit, zero and nonzero scalar maps in a concrete rigid category.
example : (𝟭 (FGModuleCat ℚ)).mapRightDualIso (𝟙_ (FGModuleCat ℚ)) =
    Iso.refl ((𝟙_ (FGModuleCat ℚ))ᘁ) := Functor.mapRightDualIso_id _
example (X Y : FGModuleCat ℚ) :
    (𝟭 (FGModuleCat ℚ)).map ((0 : X ⟶ Y)ᘁ) ≫ ((𝟭 (FGModuleCat ℚ)).mapRightDualIso X).hom =
      ((𝟭 (FGModuleCat ℚ)).mapRightDualIso Y).hom ≫ ((𝟭 (FGModuleCat ℚ)).map (0 : X ⟶ Y))ᘁ :=
  (𝟭 (FGModuleCat ℚ)).mapRightDualIso_naturality (0 : X ⟶ Y)
example (X : FGModuleCat ℚ) :
    (𝟭 (FGModuleCat ℚ)).map (((2 : ℚ) • 𝟙 X)ᘁ) ≫ ((𝟭 (FGModuleCat ℚ)).mapRightDualIso X).hom =
      ((𝟭 (FGModuleCat ℚ)).mapRightDualIso X).hom ≫
        ((𝟭 (FGModuleCat ℚ)).map ((2 : ℚ) • 𝟙 X))ᘁ :=
  (𝟭 (FGModuleCat ℚ)).mapRightDualIso_naturality ((2 : ℚ) • 𝟙 X)
example (X : RelCat.{0}) : (𝟭 RelCat.{0}).mapRightDualIso X = Iso.refl X :=
  Functor.mapRightDualIso_id X
