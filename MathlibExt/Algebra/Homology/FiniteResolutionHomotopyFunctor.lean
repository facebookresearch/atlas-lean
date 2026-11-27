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
# Homotopy functors of finite-resolution families

Let P be preadditive, A abelian and i : P → A additive full faithful, with every resolving image
i(P₀) projective. A chosen family R(X) of finite resolutions defines a functor X ↦
[R(X).complex] to the homotopy category of nonnegative complexes in P. Chosen comparison maps
give its morphisms, with identity and composition following from comparison homotopies.

Two families are naturally isomorphic by the identity comparisons in both directions. These
comparisons are reflexive and transitive. Each represented object retains its chosen complex,
terms, differentials and original object-dependent support bound.
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

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. Sending X to
[R(X).complex] and a morphism f to the homotopy class of its chosen augmented comparison defines
a functor A → HomotopyCategory(P,down ℕ). -/
def finiteResolutionHomotopyFunctor (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    A ⥤ HomotopyCategory P (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R X).complex
  map {X Y} f := (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
    (comparisonHom (R X) (R Y) f hproj).map
  map_id X := comparisonHom_quotient_id (R X) hproj
  map_comp {X Y Z} f g := comparisonHom_quotient_comp (R X) (R Y) (R Z) f g hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. The functor's
value at X is the homotopy-category object represented by R(X).complex. -/
theorem finiteResolutionHomotopyFunctor_obj (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    (finiteResolutionHomotopyFunctor R hproj).obj X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj (R X).complex :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. The complex
represented by the functor's object at X is exactly the chosen resolving complex R(X).complex. -/
theorem finiteResolutionHomotopyFunctor_obj_as (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as = (R X).complex :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For each n ∈ ℕ,
the degree-n term of the represented functor object at X is R(X)ₙ. -/
theorem finiteResolutionHomotopyFunctor_obj_X (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n : ℕ) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as.X n = (R X).complex.X n :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For n,m ∈ ℕ, the
differential of the represented functor object at X is the original differential R(X).d(n,m). -/
theorem finiteResolutionHomotopyFunctor_obj_d (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (X : A) (n m : ℕ) :
    ((finiteResolutionHomotopyFunctor R hproj).obj X).as.d n m = (R X).complex.d n m :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For n>R(X).bound,
the represented degree-n term is a zero object. Thus the original object-dependent support bound
is retained. -/
theorem finiteResolutionHomotopyFunctor_obj_isZero_above
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) (n : ℕ) (hn : (R X).bound < n) :
    IsZero (((finiteResolutionHomotopyFunctor R hproj).obj X).as.X n) :=
  (R X).isZero_above n hn

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For f : X → Y, the
functor's morphism is the homotopy class of the chosen augmented comparison R(X).complex →
R(Y).complex covering f. -/
theorem finiteResolutionHomotopyFunctor_map (R : ∀ X : A, FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) {X Y : A} (f : X ⟶ Y) :
    (finiteResolutionHomotopyFunctor R hproj).map f =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (R X) (R Y) f hproj).map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. A chosen chain-map
representative of the functor's morphism f : X → Y is homotopic to the original chosen augmented
comparison between R(X) and R(Y). -/
def finiteResolutionHomotopyFunctorMapOutHomotopy
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    {X Y : A} (f : X ⟶ Y) :
    Homotopy ((finiteResolutionHomotopyFunctor R hproj).map f).out
      (comparisonHom (R X) (R Y) f hproj).map :=
  HomotopyCategory.homotopyOutMap (comparisonHom (R X) (R Y) f hproj).map

/-- Let P be preadditive, A abelian and i : P → A additive full faithful, with all i(P₀) projective.
For finite resolutions R,S of the same X, the chosen comparisons over id_X in both directions
give [R.complex] ≅ [S.complex] in the homotopy category. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For another
resolution family S(X), the identity comparisons R(X) → S(X) define a natural isomorphism of
their finite-resolution homotopy functors. -/
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

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For another family
S, the forward comparison component at X is the homotopy class of the chosen augmented map R(X)
→ S(X) covering id_X. -/
theorem finiteResolutionHomotopyFunctorComparison_hom_app
    (R S : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) : (finiteResolutionHomotopyFunctorComparison R S hproj).hom.app X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (R X) (S X) (𝟙 X) hproj).map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For another family
S, the inverse comparison component at X is the homotopy class of the chosen reverse map S(X) →
R(X) covering id_X. -/
theorem finiteResolutionHomotopyFunctorComparison_inv_app
    (R S : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀))
    (X : A) : (finiteResolutionHomotopyFunctorComparison R S hproj).inv.app X =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom (S X) (R X) (𝟙 X) hproj).map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. Comparing the
family R with itself gives the identity natural isomorphism of its finite-resolution homotopy
functor. -/
theorem finiteResolutionHomotopyFunctorComparison_refl
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    finiteResolutionHomotopyFunctorComparison R R hproj =
      Iso.refl (finiteResolutionHomotopyFunctor R hproj) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact comparisonHom_quotient_id (R X) hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Assume i(P₀) is projective
for every object P₀ of P. Let R(X) be a chosen finite resolution of each X∈A. For families
R,S,T, the natural comparison R → S followed by S → T equals the direct natural comparison R →
T. -/
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
