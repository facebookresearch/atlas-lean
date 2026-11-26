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
# Linear Hom cochains on homotopy categories

Let `R` be a ring and `C` an `R`-linear preadditive category, with independent scalar, object,
and morphism universes. Full-product integer Hom cochains form a cochain complex of
`R`-modules in the morphism universe of `C`.

For fixed source complex `P`, postcomposition with homotopic target maps gives the same map in
the module homotopy category. Thus the linear Hom functor descends in its target.
Precomposition is natural and depends only on the homotopy class of the source map.

These constructions give a bifunctor from the opposite source homotopy category and the target
homotopy category to the homotopy category of `R`-module cochains. Its maps are the quotient
classes of linear precomposition and postcomposition on the full Hom complexes.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex.HomComplex

universe uR uC vC

variable (R : Type uR) [Ring R]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]

/-- Linear Hom target maps respect homotopy after quotienting.

For fixed cochain source `P`, homotopic maps `g₀, g₁ : L ⟶ L'` induce equal maps after
applying the linear Hom functor and quotienting in the `R`-module homotopy category. -/
theorem linearHomotopyInput_respects (P : CochainComplex C ℤ)
    (L L' : CochainComplex C ℤ) (g₀ g₁ : L ⟶ L')
    (h : homotopic C (.up ℤ) g₀ g₁) :
    (((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map g₀ =
      (((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map g₁ :=
  HomotopyCategory.eq_of_homotopy _ _ (linearComplexMapPostHomotopy R P h.some)

/-- Linear Hom with fixed source descends to the target homotopy category.

For a cochain complex `P` in an `R`-linear preadditive category, the functor `Hom_C(P,-)`
descends from target cochains to their homotopy category, valued in the homotopy category of
`R`-module cochains. -/
def linearHomotopyFunctor (P : CochainComplex C ℤ) :
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory (ModuleCat.{vC} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic C (.up ℤ))
    (((linearFunctor R C).obj (Opposite.op P)) ⋙
      HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ))
    (linearHomotopyInput_respects R P)

/-- Fixed-source linear Hom descent has its quotient factorization.

The source homotopy quotient followed by the descended Hom functor is naturally isomorphic to
the cochain linear Hom functor followed by the module homotopy quotient. -/
def linearHomotopyFunctorFactors (P : CochainComplex C ℤ) :
    HomotopyCategory.quotient C (.up ℤ) ⋙ linearHomotopyFunctor R P ≅
      ((linearFunctor R C).obj (Opposite.op P)) ⋙
        HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ) :=
  CategoryTheory.Quotient.lift.isLift _ _ (linearHomotopyInput_respects R P)

/-- Object of the descended fixed-source Hom functor.

At the homotopy quotient of `L`, the descended functor gives the quotient of `linearComplex R
P L`. -/
@[simp]
theorem linearHomotopyFunctor_obj (P L : CochainComplex C ℤ) :
    (linearHomotopyFunctor R P).obj ((HomotopyCategory.quotient C (.up ℤ)).obj L) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).obj (linearComplex R P L) := rfl

/-- Target map of descended Hom is the postcomposition class.

For a target cochain map `g`, the descended functor on its quotient class is the quotient
image of `linearComplexMap R (𝟙 P) g`. -/
@[simp]
theorem linearHomotopyFunctor_map (P : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') :
    (linearHomotopyFunctor R P).map ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R (𝟙 P) g) := rfl

/-- Source precomposition gives a transformation of descended Hom functors.

A cochain map `f : P' ⟶ P` induces a natural transformation from the descended Hom functor
with source `P` to that with source `P'`. -/
def linearHomotopyPrecomp {P P' : CochainComplex C ℤ} (f : P' ⟶ P) :
    linearHomotopyFunctor R P ⟶ linearHomotopyFunctor R P' :=
  CategoryTheory.Quotient.natTransLift (homotopic C (.up ℤ))
    ((linearHomotopyFunctorFactors R P).hom ≫
      whiskerRight ((linearFunctor R C).map f.op)
        (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)) ≫
      (linearHomotopyFunctorFactors R P').inv)

/-- Descended source-precomposition component is its linear Hom map class.

At homotopy object `L`, the precomposition transformation is the quotient class of
`linearComplexMap R f (𝟙 L.as)`. -/
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

/-- Contravariant source functor of target-descended linear Hom.

The assignment of a source cochain complex to its descended target Hom functor is a functor
from the opposite cochain category. -/
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

/-- Homotopic source maps give equal descended Hom transformations.

If cochain maps `f₀, f₁ : P' ⟶ P` are homotopic, then `linearHomotopyPrecomp R f₀ =
linearHomotopyPrecomp R f₁`. -/
theorem linearHomotopyPrecomp_eq_of_homotopy {P P' : CochainComplex C ℤ}
    {f₀ f₁ : P' ⟶ P} (h : Homotopy f₀ f₁) :
    linearHomotopyPrecomp R f₀ = linearHomotopyPrecomp R f₁ := by
  apply NatTrans.ext
  funext L
  simp only [linearHomotopyPrecomp_app]
  exact HomotopyCategory.eq_of_homotopy _ _ (linearComplexMapPreHomotopy R h L.as)

/-- Source Hom functor respects homotopy with its opposite variance.

Two homotopic source cochain maps have equal images under the opposite-variance form of the
source Hom functor. This gives the source quotient compatibility. -/
theorem linearHomotopySourceRightOp_respects (P P' : CochainComplex C ℤ)
    (f₀ f₁ : P ⟶ P') (h : homotopic C (.up ℤ) f₀ f₁) :
    (linearHomotopySourceFunctor R (C := C)).rightOp.map f₀ =
      (linearHomotopySourceFunctor R (C := C)).rightOp.map f₁ := by
  change (linearHomotopyPrecomp R f₀).op = (linearHomotopyPrecomp R f₁).op
  exact congrArg
    (fun a : linearHomotopyFunctor R P' ⟶ linearHomotopyFunctor R P => a.op)
    (linearHomotopyPrecomp_eq_of_homotopy R h.some)

/-- Linear Hom bifunctor of integer homotopy categories.

Linear Hom descends in both variables to a bifunctor from the opposite homotopy category of
`C`-cochains and its covariant homotopy category to the homotopy category of `R`-module
cochains. -/
def linearHomotopyBifunctor : (HomotopyCategory C (.up ℤ))ᵒᵖ ⥤
    HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory (ModuleCat.{vC} R) (.up ℤ) :=
  (CategoryTheory.Quotient.lift (homotopic C (.up ℤ))
    (linearHomotopySourceFunctor R (C := C)).rightOp
      (linearHomotopySourceRightOp_respects R)).leftOp

/-- Object formula for the homotopy linear Hom bifunctor.

For homotopy objects `P` and `L`, the bifunctor value is the module homotopy quotient of
`linearComplex R P.as L.as`. -/
@[simp]
theorem linearHomotopyBifunctor_obj_obj
    (P L : HomotopyCategory C (.up ℤ)) :
    ((linearHomotopyBifunctor R).obj (Opposite.op P)).obj L =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).obj
        (linearComplex R P.as L.as) := rfl

/-- Source component of the homotopy Hom bifunctor.

For `f : P' ⟶ P`, the source-variable transformation at `L` is the quotient class of
`linearComplexMap R f (𝟙 L.as)`. -/
@[simp]
theorem linearHomotopyBifunctor_map_app {P P' : CochainComplex C ℤ} (f : P' ⟶ P)
    (L : HomotopyCategory C (.up ℤ)) :
    ((linearHomotopyBifunctor R).map
        ((HomotopyCategory.quotient C (.up ℤ)).map f).op).app L =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R f (𝟙 L.as)) :=
  linearHomotopyPrecomp_app R f L

/-- Target map of the homotopy Hom bifunctor.

For fixed homotopy source `P` and target cochain map `g : L ⟶ L'`, the target map is the
quotient image of `linearComplexMap R (𝟙 P.as) g`. -/
@[simp]
theorem linearHomotopyBifunctor_obj_map (P : HomotopyCategory C (.up ℤ))
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') :
    ((linearHomotopyBifunctor R).obj (Opposite.op P)).map
        ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      (HomotopyCategory.quotient (ModuleCat.{vC} R) (.up ℤ)).map
        (linearComplexMap R (𝟙 P.as) g) := rfl

/-- Two-variable homotopy Hom map is the class of the linear Hom map.

For `f : P' ⟶ P` and `g : L ⟶ L'`, the uncurried homotopy Hom bifunctor sends their quotient
classes to the quotient class of `linearComplexMap R f g`. -/
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
