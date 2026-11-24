/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Native mapping spaces of simplicial-algebra prestacks

An actual prestack is flipped to a simplicial object in the category of
algebra-indexed sets. Its mapping simplicial set is Mathlib's enriched
Hom, so every simplex is a compatible family of maps, including its
algebra and simplicial naturality. Mapping from an affine family times
X uses the actual augmented algebra replacement and the pointwise product.

An injectively fibrant replacement is constrained by the objectwise
trivial-monomorphism lifting property. The computed mapping object uses
that replacement; no geometricity, cotangent, symplectic or categorical
descent result is a field. Prestacks take values one universe above the
algebra elements: both objects of the indexing algebra category and the
values then lie in that universe. Ordinary small-diagram injective model
replacement applies to this exact type. Mapping spaces remain in that
same larger universe. The native affine mapping functor is lifted there.

References: PTVV, arXiv:1111.3209v4, conventions and §2.1;
Toën--Vaquié, arXiv:math/0503269v5, §§2.1 and 3.1; Bousfield--Kan,
Homotopy limits, completions and localizations, Chapters X--XI.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

open CategoryTheory MonoidalCategory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels

universe u

variable (k : Type u) [CommRing k]

/-- The actual category of space-valued algebra prestacks. -/
abbrev Prestack := SAlg k ⥤ SSet.{u + 1}

/-- The native lift puts affine simplicial values in the indexing universe. -/
def liftSimplicial : SSet.{u} ⥤ SSet.{u + 1} :=
  (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{u + 1, u})

/-- Literal lifted affine values, with all original simplicial maps. -/
def affineMapping (Q : AlgebraReplacementFunctor k) (A : SAlg k) : Prestack k :=
  derivedSpecFunctor Q A ⋙ liftSimplicial

/-- Flipping the two actual naturality directions retains every simplex. -/
def toSimplicial : Prestack k ⥤ SimplicialObject (SAlg k ⥤ Type (u + 1)) :=
  flipFunctor _ _ _

/-- The native simplicial Hom, rather than a freely chosen mapping space. -/
abbrev mapping (X Y : Prestack k) : SSet.{u + 1} :=
  SimplicialCategory.sHom ((toSimplicial k).obj X) ((toSimplicial k).obj Y)

/-- Native precomposition and postcomposition on all mapping simplices. -/
def mappingBifunctor : (Prestack k)ᵒᵖ ⥤ Prestack k ⥤ SSet.{u + 1} :=
  (toSimplicial k).op ⋙
    SimplicialCategory.sHomFunctor (SimplicialObject (SAlg k ⥤ Type (u + 1))) ⋙
    (Functor.whiskeringLeft _ _ _).obj (toSimplicial k)

/-- Ordinary natural maps identify with the actual zero simplices. -/
def mappingZero (X Y : Prestack k) :
    (X ⟶ Y) ≃ (mapping k X Y).obj (op (SimplexCategory.mk 0)) :=
  (Functor.flipping.fullyFaithfulFunctor.homEquiv).trans
    (SimplicialCategory.homEquiv' ((toSimplicial k).obj X) ((toSimplicial k).obj Y))

/-- The native affine Yoneda functor uses Map(QA,-) in both variables. -/
def affineYoneda (Q : AlgebraReplacementFunctor k) : (SAlg k)ᵒᵖ ⥤ Prestack k :=
  Q.functor.op ⋙ SimplicialCategory.sHomFunctor (SAlg k) ⋙
    (Functor.whiskeringRight _ _ _).obj liftSimplicial

/-- Literal affine-family products with the actual prestack X. -/
def affineTimes (Q : AlgebraReplacementFunctor k) (X : Prestack k) :
    (SAlg k)ᵒᵖ ⥤ Prestack k :=
  affineYoneda k Q ⋙ tensorRight X

variable {k}

@[simp]
theorem affineYoneda_obj (Q : AlgebraReplacementFunctor k) (A : SAlg k) :
    (affineYoneda k Q).obj (op A) = affineMapping k Q A := rfl

@[simp]
theorem affineYoneda_map (Q : AlgebraReplacementFunctor k) {A B : SAlg k}
    (f : A ⟶ B) : (affineYoneda k Q).map f.op =
      Functor.whiskerRight (derivedSpecMap Q f) liftSimplicial := rfl

/-- Injective fibrancy is tested in the actual algebra diagram category,
whose indexing objects and simplicial values are both small in u+1. -/
def IsInjectivelyFibrant (F : Prestack k) : Prop :=
  ∀ (A B : Prestack k) (i : A ⟶ B),
    (∀ C, Mono (i.app C) ∧ WeakEquivalence (i.app C)) →
    ∀ f : A ⟶ F, ∃ g : B ⟶ F, i ≫ g = f

/-- A genuine diagram replacement, with actual augmentation and lifting maps. -/
structure FibrantReplacement (F : Prestack k) where
  model : Prestack k
  augmentation : F ⟶ model
  weak : ∀ A, WeakEquivalence (augmentation.app A)
  fibrant : IsInjectivelyFibrant model
  kan : ∀ A, SSet.KanComplex (model.obj A)

variable (k)

/-- The actual derived mapping-family candidate Map(Spec(A) × X,F).
Its map on an algebra arrow is the native precomposition map. -/
def mappingPrestackFunctor (Q : AlgebraReplacementFunctor k)
    (X F : Prestack k) (R : FibrantReplacement F) : SAlg k ⥤ SSet.{u + 1} :=
  (opOpEquivalence (SAlg k)).inverse ⋙ (affineTimes k Q X).op ⋙
    (mappingBifunctor k).flip.obj R.model

/-- The computed mapping-family object is fixed in every affine degree. -/
theorem mappingPrestackFunctor_obj (Q : AlgebraReplacementFunctor k)
    (X F : Prestack k) (R : FibrantReplacement F) (A : SAlg k) :
    (mappingPrestackFunctor k Q X F R).obj A =
      mapping k (affineMapping k Q A ⊗ X) R.model := rfl

/-- The prestack laws for the fixed mapping functor are construction outputs. -/
structure MappingPrestackModel (Q : AlgebraReplacementFunctor k)
    (X F : DerivedPrestack.{u, u + 1} k) (R : FibrantReplacement F.functor) where
  prestack : DerivedPrestack.{u, u + 1} k
  functor_eq : prestack.functor = mappingPrestackFunctor k Q X.functor F.functor R

end MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
