/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionComparisonHomotopy

/-!
# The homotopy functor of an original finite-resolution family

A given family of finite resolutions defines a functor to Mathlib's original
homotopy category. Its objects are the original resolving complexes and its
maps are the quotient images of the existing chosen comparison maps.
Constructed comparison homotopies prove the functor laws.

Identity comparisons give a natural isomorphism between two such families.
Its forward and inverse maps are the original chosen identity comparisons.
Each family's original object-dependent support bound remains visible on
the complex represented by its homotopy-category object.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] [i.Full] [i.Faithful]

/-- The original chosen comparison lifts make a given finite-resolution
family functorial in the stock homotopy category. -/
def finiteResolutionHomotopyFunctor (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    A ⥤ HomotopyCategory P (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R X).complex
  map {X Y} f := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
    (comparisonHom (R X) (R Y) f hproj).map
  map_id X := comparisonHom_quotient_id (R X) hproj
  map_comp {X Y Z} f g := comparisonHom_quotient_comp (R X) (R Y) (R Z) f g hproj

/-- The functor object is the stock quotient image of the original complex. -/
theorem finiteResolutionHomotopyFunctor_obj (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    (finiteResolutionHomotopyFunctor R hproj).obj X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R X).complex :=
  rfl

/-- The represented complex is exactly the given original resolving complex. -/
theorem finiteResolutionHomotopyFunctor_obj_as (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as = (R X).complex :=
  rfl

/-- Every represented term is the original resolving term of the given family. -/
theorem finiteResolutionHomotopyFunctor_obj_X (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n : ℕ) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as.X n = (R X).complex.X n :=
  rfl

/-- Every represented differential is the original differential. -/
theorem finiteResolutionHomotopyFunctor_obj_d (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n m : ℕ) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as.d n m = (R X).complex.d n m :=
  rfl

/-- The represented complex retains the exact original object-dependent
inclusive support bound. -/
theorem finiteResolutionHomotopyFunctor_obj_isZero_above
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) (n : ℕ) (hn : (R X).bound < n) :
    IsZero (((finiteResolutionHomotopyFunctor R hproj).obj X).as.X n) :=
  (R X).isZero_above n hn

/-- The literal functor map is the stock quotient image of the same original
chosen augmented comparison map. -/
theorem finiteResolutionHomotopyFunctor_map (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) {X Y : A} (f : X ⟶ Y) :
    (finiteResolutionHomotopyFunctor R hproj).map f =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (R X) (R Y) f hproj).map :=
  rfl

/-- The chosen representative of a quotient map is homotopic to the original
comparison map, using the stock quotient representative homotopy. -/
def finiteResolutionHomotopyFunctorMapOutHomotopy
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    {X Y : A} (f : X ⟶ Y) :
    Homotopy ((finiteResolutionHomotopyFunctor R hproj).map f).out
      (comparisonHom (R X) (R Y) f hproj).map :=
  HomotopyCategory.homotopyOutMap (comparisonHom (R X) (R Y) f hproj).map

/-- Original chosen identity comparisons give an isomorphism between the
stock quotient images of two original finite resolutions of the same object. -/
def finiteResolutionComparisonIso {X : A} (R S : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj R.complex ≅
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj S.complex where
  hom := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
    (comparisonHom R S (𝟙 X) hproj).map
  inv := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
    (comparisonHom S R (𝟙 X) hproj).map
  hom_inv_id := by
    let Q := HomotopyCategory.quotient P (ComplexShape.down ℕ)
    calc
      _ = Q.map ((comparisonHom R S (𝟙 X) hproj).map ≫
          (comparisonHom S R (𝟙 X) hproj).map) :=
        (Q.map_comp _ _).symm
      _ = Q.map (𝟙 R.complex) := by
        apply HomotopyCategory.eq_of_homotopy
        have hindex := congrArg (fun t : X ⟶ X => (comparisonHom R R t hproj).map)
          (Category.id_comp (𝟙 X))
        exact (comparisonHomotopyComp R S R (𝟙 X) (𝟙 X) hproj).symm.trans
          ((Homotopy.ofEq hindex).trans (comparisonHomotopyId R hproj))
      _ = 𝟙 (Q.obj R.complex) := Q.map_id R.complex
  inv_hom_id := by
    let Q := HomotopyCategory.quotient P (ComplexShape.down ℕ)
    calc
      _ = Q.map ((comparisonHom S R (𝟙 X) hproj).map ≫
          (comparisonHom R S (𝟙 X) hproj).map) :=
        (Q.map_comp _ _).symm
      _ = Q.map (𝟙 S.complex) := by
        apply HomotopyCategory.eq_of_homotopy
        have hindex := congrArg (fun t : X ⟶ X => (comparisonHom S S t hproj).map)
          (Category.id_comp (𝟙 X))
        exact (comparisonHomotopyComp S R S (𝟙 X) (𝟙 X) hproj).symm.trans
          ((Homotopy.ofEq hindex).trans (comparisonHomotopyId S hproj))
      _ = 𝟙 (Q.obj S.complex) := Q.map_id S.complex

/--
Identity comparison maps are natural in the original target objects, giving a natural isomorphism
between two resolution families.
-/
def finiteResolutionHomotopyFunctorComparison
    (R S : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    finiteResolutionHomotopyFunctor R hproj ≅ finiteResolutionHomotopyFunctor S hproj :=
  NatIso.ofComponents (fun X => finiteResolutionComparisonIso (R X) (S X) hproj) (by
    intro X Y f
    let Q := HomotopyCategory.quotient P (ComplexShape.down ℕ)
    change Q.map (comparisonHom (R X) (R Y) f hproj).map ≫
        Q.map (comparisonHom (R Y) (S Y) (𝟙 Y) hproj).map =
      Q.map (comparisonHom (R X) (S X) (𝟙 X) hproj).map ≫
        Q.map (comparisonHom (S X) (S Y) f hproj).map
    rw [← Q.map_comp, ← Q.map_comp]
    apply HomotopyCategory.eq_of_homotopy
    have hleft : Homotopy
        ((comparisonHom (R X) (R Y) f hproj).map ≫
          (comparisonHom (R Y) (S Y) (𝟙 Y) hproj).map)
        (comparisonHom (R X) (S Y) f hproj).map := by
      have hindex := congrArg
        (fun t : X ⟶ Y => (comparisonHom (R X) (S Y) t hproj).map) (Category.comp_id f)
      exact (comparisonHomotopyComp (R X) (R Y) (S Y) f (𝟙 Y) hproj).symm.trans
        (Homotopy.ofEq hindex)
    have hright : Homotopy (comparisonHom (R X) (S Y) f hproj).map
        ((comparisonHom (R X) (S X) (𝟙 X) hproj).map ≫
          (comparisonHom (S X) (S Y) f hproj).map) := by
      have hindex := congrArg
        (fun t : X ⟶ Y => (comparisonHom (R X) (S Y) t hproj).map) (Category.id_comp f)
      exact (Homotopy.ofEq hindex).symm.trans
        (comparisonHomotopyComp (R X) (S X) (S Y) (𝟙 X) f hproj)
    exact hleft.trans hright)

/-- The forward family-comparison component is the original chosen
identity comparison in the stock quotient. -/
theorem finiteResolutionHomotopyFunctorComparison_hom_app
    (R S : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) : (finiteResolutionHomotopyFunctorComparison R S hproj).hom.app X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (R X) (S X) (𝟙 X) hproj).map :=
  rfl

/-- The inverse component is the original reverse chosen identity comparison. -/
theorem finiteResolutionHomotopyFunctorComparison_inv_app
    (R S : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) : (finiteResolutionHomotopyFunctorComparison R S hproj).inv.app X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (S X) (R X) (𝟙 X) hproj).map :=
  rfl

/-- Comparing a family with itself gives the identity natural isomorphism. -/
theorem finiteResolutionHomotopyFunctorComparison_refl
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    finiteResolutionHomotopyFunctorComparison R R hproj =
      Iso.refl (finiteResolutionHomotopyFunctor R hproj) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact comparisonHom_quotient_id (R X) hproj

/--
Family comparison preserves composition of the original identity comparisons in the stock
quotient.
-/
theorem finiteResolutionHomotopyFunctorComparison_trans
    (R S T : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    finiteResolutionHomotopyFunctorComparison R S hproj ≪≫
        finiteResolutionHomotopyFunctorComparison S T hproj =
      finiteResolutionHomotopyFunctorComparison R T hproj := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (R X) (S X) (𝟙 X) hproj).map ≫
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (S X) (T X) (𝟙 X) hproj).map =
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
      (comparisonHom (R X) (T X) (𝟙 X) hproj).map
  have hindex := congrArg
    (fun t : X ⟶ X => (comparisonHom (R X) (T X) t hproj).map) (Category.id_comp (𝟙 X))
  exact (comparisonHom_quotient_comp (R X) (S X) (T X) (𝟙 X) (𝟙 X) hproj).symm.trans
    (congrArg (fun t : (R X).complex ⟶ (T X).complex =>
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map t) hindex)

end CategoryTheory.Abelian.FiniteResolution

end
