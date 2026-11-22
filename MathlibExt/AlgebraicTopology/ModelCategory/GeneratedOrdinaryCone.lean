/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedArrowFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe

/-!
# Ordinary cones from the original fixed-cardinal factorization

The original I factory is applied to each actual arrow to the caller's zero
object. Its middle functor, insertion, contraction and maps are retained.
The cofibration and weak-contraction hypotheses used by ordinary Puppe
constructions are consequences of the original factor classes. The cofiber
cocones below are the original chosen pushouts, with both legs unchanged.
-/

set_option autoImplicit false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty
open HomotopicalAlgebra.OrdinaryHoChosenPuppe

namespace HomotopicalAlgebra.GeneratedOrdinaryCone

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The original I middle functor on the actual object-to-zero arrows. -/
def cone : C ⥤ C :=
  zeroArrowFunctor Z hZ ⋙ (GeneratedArrowFactorizations.cofibrant d).Z

/-- The insertion is the same original I left factor at every object. -/
def inclusion : 𝟭 C ⟶ cone d Z hZ where
  app X := (GeneratedArrowFactorizations.cofibrant d).i.app
    ((zeroArrowFunctor Z hZ).obj X)
  naturality _ _ f := (GeneratedArrowFactorizations.cofibrant d).i.naturality
    ((zeroArrowFunctor Z hZ).map f)

/-- The contraction is the same original I right factor into the actual zero. -/
def contraction : cone d Z hZ ⟶ (Functor.const C).obj Z where
  app X := (GeneratedArrowFactorizations.cofibrant d).p.app
    ((zeroArrowFunctor Z hZ).obj X)
  naturality _ _ f := (GeneratedArrowFactorizations.cofibrant d).p.naturality
    ((zeroArrowFunctor Z hZ).map f)

/-- The two original factors recover the unchanged collapse of the input. -/
theorem inclusion_contraction (X : C) :
    (inclusion d Z hZ).app X ≫ (contraction d Z hZ).app X = toZero Z hZ X :=
  (GeneratedArrowFactorizations.cofibrant d).fac_app

/-- The source insertion is a cofibration by the original I factor class. -/
theorem inclusion_cofibration (X : C) :
    cofibrations C ((inclusion d Z hZ).app X) :=
  (GeneratedArrowFactorizations.cofibrant d).hi ((zeroArrowFunctor Z hZ).obj X)

/-- The actual contraction is a trivial fibration by the original right class. -/
theorem contraction_trivialFibration (X : C) :
    trivialFibrations C ((contraction d Z hZ).app X) :=
  (GeneratedArrowFactorizations.cofibrant d).hp ((zeroArrowFunctor Z hZ).obj X)

/-- The contraction's weakness is earned from the original trivial fibration. -/
theorem contraction_weak (X : C) :
    weakEquivalences C ((contraction d Z hZ).app X) :=
  (contraction_trivialFibration d Z hZ X).2

/-- The original right factor is the literal zero endpoint function. -/
theorem contraction_eq_toZero (X : C) :
    (contraction d Z hZ).app X = toZero Z hZ ((cone d Z hZ).obj X) :=
  hZ.isTerminal.hom_ext _ _

/-- This is the weak zero contraction required by the chosen Puppe source. -/
theorem toZero_cone_weak (X : C) :
    weakEquivalences C (toZero Z hZ ((cone d Z hZ).obj X)) := by
  rw [← contraction_eq_toZero]
  exact contraction_weak d Z hZ X

/-- Cofibrancy propagates along the same original insertion. -/
theorem cone_isCofibrant (X : C) [IsCofibrant X] :
    IsCofibrant ((cone d Z hZ).obj X) := by
  let _ : IsCofibrant ((𝟭 C).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : Cofibration ((inclusion d Z hZ).app X) :=
    (cofibration_iff _).mpr (inclusion_cofibration d Z hZ X)
  exact isCofibrant_of_cofibration ((inclusion d Z hZ).app X)

/-- Every cone is fibrant because its original contraction targets a zero object. -/
theorem cone_isFibrant (X : C) : IsFibrant ((cone d Z hZ).obj X) :=
  (isFibrant_iff_of_isTerminal ((contraction d Z hZ).app X) hZ.isTerminal).mpr
    ((fibration_iff _).mpr (contraction_trivialFibration d Z hZ X).1)

/-- Every cone map remains the original middle map of its full zero-target square. -/
theorem cone_map {X Y : C} (f : X ⟶ Y) :
    (cone d Z hZ).map f = (GeneratedArrowFactorizations.cofibrant d).Z.map
      ((zeroArrowFunctor Z hZ).map f) := rfl

/-- Every original cone map is weak by both actual contraction maps and naturality. -/
theorem cone_map_weak {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C ((cone d Z hZ).map f) := by
  have h : (cone d Z hZ).map f ≫ (contraction d Z hZ).app Y =
      (contraction d Z hZ).app X :=
    ((contraction d Z hZ).naturality f).trans (Category.comp_id _)
  exact (weakEquivalences C).of_postcomp _ ((contraction d Z hZ).app Y)
    (contraction_weak d Z hZ Y) (h.symm ▸ contraction_weak d Z hZ X)

/-- The cofiber uses the chosen pushout of the original insertion and input arrow. -/
def cofiberCocone (F : Arrow C) :
    PushoutCocone ((inclusion d Z hZ).app F.left) F.hom :=
  pushout.cocone ((inclusion d Z hZ).app F.left) F.hom

/-- The original chosen pushout witness supplies the full cofiber universal property. -/
def cofiberIsColimit (F : Arrow C) : IsColimit (cofiberCocone d Z hZ F) :=
  pushout.isColimit ((inclusion d Z hZ).app F.left) F.hom

end HomotopicalAlgebra.GeneratedOrdinaryCone
