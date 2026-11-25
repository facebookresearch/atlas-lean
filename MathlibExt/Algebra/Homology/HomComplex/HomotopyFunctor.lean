/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.HomComplex.LinearHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The original linear Hom input on the homotopy category

Native quotient lifting uses the actual linear postcomposition homotopy.
Objects remain the original linear Hom complexes; maps remain their
original quotient classes. The first-variable maps are the original
linear precomposition classes, lifted as native natural transformations.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex.HomComplex

universe uR uC vC

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]

/-- Actual postcomposition is well defined modulo the native homotopy relation. -/
theorem linearHomotopyInput_respects (P : CochainComplex C ℤ)
    (L L' : CochainComplex C ℤ) (g₀ g₁ : L ⟶ L')
    (h : homotopic C (.up ℤ) g₀ g₁) :
    (((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map g₀ =
      (((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map g₁ :=
  HomotopyCategory.eq_of_homotopy _ _ (linearComplexMapPostHomotopy R P h.some)

/-- The actual native quotient lift, with no alternate underived Hom model. -/
def linearHomotopyFunctor (P : CochainComplex C ℤ) :
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory (ModuleCat.{vC} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic C (.up ℤ))
    (((linearFunctor R C).obj (Opposite.op P)) ⋙
      HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ))
    (linearHomotopyInput_respects R P)

/-- Its original complex input factors by the native quotient-lift Iso. -/
def linearHomotopyFunctorFactors (P : CochainComplex C ℤ) :
    HomotopyCategory.quotient C (.up ℤ) ⋙ linearHomotopyFunctor R P ≅
      ((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift.isLift _ _ (linearHomotopyInput_respects R P)

@[simp]
theorem linearHomotopyFunctor_obj (P L : CochainComplex C ℤ) :
    (linearHomotopyFunctor R P).obj ((HomotopyCategory.quotient C (.up ℤ)).obj L) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).obj (linearComplex R P L) := rfl

/-- Every original target map keeps precisely its original quotient class. -/
@[simp]
theorem linearHomotopyFunctor_map (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') :
    (linearHomotopyFunctor R P).map ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R (𝟙 P) g) := rfl

/-- Original source precomposition, lifted by native quotient natural-transformation lifting. -/
def linearHomotopyPrecomp {P P' : CochainComplex C ℤ} (f : P' ⟶ P) :
    linearHomotopyFunctor R P ⟶ linearHomotopyFunctor R P' :=
  CategoryTheory.Quotient.natTransLift (homotopic C (.up ℤ))
    ((linearHomotopyFunctorFactors R P).hom ≫
      whiskerRight ((linearFunctor R C).map f.op)
        (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)) ≫
      (linearHomotopyFunctorFactors R P').inv)

@[simp]
theorem linearHomotopyPrecomp_app {P P' : CochainComplex C ℤ} (f : P' ⟶ P)
    (L : HomotopyCategory C (.up ℤ)) :
    (linearHomotopyPrecomp R f).app L =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R f (𝟙 L.as)) := by
  change 𝟙 _ ≫
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R f (𝟙 L.as)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The curried actual Hom input retains the original first-variable maps. -/
def linearHomotopySourceFunctor : (CochainComplex C ℤ)ᵒᵖ ⥤
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory (ModuleCat.{vC} R) (.up ℤ) where
  obj P := linearHomotopyFunctor R P.unop
  map f := linearHomotopyPrecomp R f.unop
  map_id P := by
    apply NatTrans.ext
    funext L
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [linearHomotopyPrecomp_app, CategoryTheory.unop_id,
      HomotopyCategory.quotient_obj_as, linearComplexMap_id, NatTrans.id_app]
    exact (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map_id
      (linearComplex R P.unop L)
  map_comp f g := by
    apply NatTrans.ext
    funext L
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [linearHomotopyPrecomp_app, CategoryTheory.unop_comp,
      HomotopyCategory.quotient_obj_as, NatTrans.comp_app]
    have hcomp : linearComplexMap R (g.unop ≫ f.unop) (𝟙 L) =
        linearComplexMap R f.unop (𝟙 L) ≫ linearComplexMap R g.unop (𝟙 L) := by
      simpa only [Category.id_comp] using
        (linearComplexMap_comp R f.unop g.unop (𝟙 L) (𝟙 L)).symm
    exact (congrArg
      (fun a => (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map a)
      hcomp).trans
      ((HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map_comp
        (linearComplexMap R f.unop (𝟙 L)) (linearComplexMap R g.unop (𝟙 L)))

/-- Homotopic original source maps also have precisely the same quotient class. -/
theorem linearHomotopyPrecomp_eq_of_homotopy {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) :
    linearHomotopyPrecomp R f₀ = linearHomotopyPrecomp R f₁ := by
  apply NatTrans.ext
  funext L
  simp only [linearHomotopyPrecomp_app]
  exact HomotopyCategory.eq_of_homotopy _ _ (linearComplexMapPreHomotopy R h L.as)

/-- The right opposite of the original source functor respects the native
homotopy relation, before the source variable is quotiented. -/
theorem linearHomotopySourceRightOp_respects (P P' : CochainComplex C ℤ)
    (f₀ f₁ : P ⟶ P') (h : homotopic C (.up ℤ) f₀ f₁) :
    (linearHomotopySourceFunctor R (C := C)).rightOp.map f₀ =
      (linearHomotopySourceFunctor R (C := C)).rightOp.map f₁ := by
  change (linearHomotopyPrecomp R f₀).op = (linearHomotopyPrecomp R f₁).op
  exact congrArg
    (fun a : linearHomotopyFunctor R P' ⟶ linearHomotopyFunctor R P => a.op)
    (linearHomotopyPrecomp_eq_of_homotopy R h.some)

/-- The original product Hom on both native homotopy categories. The first
input remains opposite, and its quotient lift earns all source map classes. -/
def linearHomotopyBifunctor : (HomotopyCategory C (.up ℤ))ᵒᵖ ⥤
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory (ModuleCat.{vC} R) (.up ℤ) :=
  (CategoryTheory.Quotient.lift (homotopic C (.up ℤ))
    (linearHomotopySourceFunctor R (C := C)).rightOp
      (linearHomotopySourceRightOp_respects R)).leftOp

@[simp]
theorem linearHomotopyBifunctor_obj_obj
    (P L : HomotopyCategory C (.up ℤ)) :
    ((linearHomotopyBifunctor R).obj (Opposite.op P)).obj L =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).obj
        (linearComplex R P.as L.as) := rfl

/-- Each original first-variable map retains its actual precomposition class. -/
@[simp]
theorem linearHomotopyBifunctor_map_app {P P' : CochainComplex C ℤ} (f : P' ⟶ P)
    (L : HomotopyCategory C (.up ℤ)) :
    ((linearHomotopyBifunctor R).map
        ((HomotopyCategory.quotient C (.up ℤ)).map f).op).app L =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R f (𝟙 L.as)) :=
  linearHomotopyPrecomp_app R f L

/-- Each original second-variable map retains its actual postcomposition class. -/
@[simp]
theorem linearHomotopyBifunctor_obj_map (P : HomotopyCategory C (.up ℤ))
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') :
    ((linearHomotopyBifunctor R).obj (Opposite.op P)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R (𝟙 P.as) g) := rfl

/-- The simultaneous map is the quotient class of the same original
precomposition and postcomposition map. -/
theorem linearHomotopyBifunctor_uncurry_map
    {P P' L L' : CochainComplex C ℤ} (f : P' ⟶ P) (g : L ⟶ L') :
    (CategoryTheory.Functor.uncurry.obj (linearHomotopyBifunctor R (C := C))).map
        (X := (Opposite.op ((HomotopyCategory.quotient C (.up ℤ)).obj P),
          (HomotopyCategory.quotient C (.up ℤ)).obj L))
        (Y := (Opposite.op ((HomotopyCategory.quotient C (.up ℤ)).obj P'),
          (HomotopyCategory.quotient C (.up ℤ)).obj L'))
        (((HomotopyCategory.quotient C (.up ℤ)).map f).op,
          (HomotopyCategory.quotient C (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R f g) := by
  change (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
      (linearComplexMap R f (𝟙 L)) ≫
    (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
      (linearComplexMap R (𝟙 P') g) = _
  have hcomp : linearComplexMap R f (𝟙 L) ≫ linearComplexMap R (𝟙 P') g =
      linearComplexMap R f g := by
    simpa only [Category.id_comp] using
      linearComplexMap_comp R f (𝟙 P') (𝟙 L) g
  exact ((HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map_comp
    (linearComplexMap R f (𝟙 L)) (linearComplexMap R (𝟙 P') g)).symm.trans
    (congrArg
      (fun a => (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map a)
      hcomp)

end CochainComplex.HomComplex
