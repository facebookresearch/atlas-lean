/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Native normalization and homology transport of augmented presentations

An original augmented simplicial or cosimplicial presentation includes its
augmentation or coaugmentation as a native comma-category morphism. Mapping
both sides by the native complex and homology functors keeps this map.
Natural isomorphisms of the original presentations therefore induce the
computed complex and homology comparisons, with identity, inverse and
composition preserved. No derived comparison isomorphism is an input.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.SimplicialObject.Augmented

variable {E : Type*} [Category* E] [Abelian E]

/-- The actual augmented presentation, mapped on both sides by native Dold--Kan normalization. -/
def normalizedAugmentationFunctor : Augmented E ⥤
    Comma (𝟭 (ChainComplex E ℕ))
      (SimplicialObject.const E ⋙ CategoryTheory.Abelian.DoldKan.N (A := E)) :=
  Comma.map (F₁ := CategoryTheory.Abelian.DoldKan.N (A := E)) (F₂ := 𝟭 E)
    (F := CategoryTheory.Abelian.DoldKan.N (A := E)) (Iso.refl _).hom (Iso.refl _).hom

/-- The normalized left object is computed from the original simplicial presentation. -/
theorem normalizedAugmentationFunctor_obj_left (X : Augmented E) :
    (normalizedAugmentationFunctor.obj X).left =
      CategoryTheory.Abelian.DoldKan.N.obj X.left := rfl

/-- The normalized augmentation is the native map of the original augmentation. -/
theorem normalizedAugmentationFunctor_obj_hom (X : Augmented E) :
    (normalizedAugmentationFunctor.obj X).hom =
      CategoryTheory.Abelian.DoldKan.N.map X.hom := by
  simp [normalizedAugmentationFunctor]

/-- Fixed-degree homology keeps both sides of the actual normalized augmentation. -/
def homologyAugmentationFunctor (n : ℕ) : Augmented E ⥤
    Comma (𝟭 E) (SimplicialObject.const E ⋙ CategoryTheory.Abelian.DoldKan.N (A := E) ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n) :=
  let H := CategoryTheory.Abelian.DoldKan.N (A := E) ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  Comma.map (F₁ := H) (F₂ := 𝟭 E) (F := H) (Iso.refl _).hom (Iso.refl _).hom

variable {J : Type*} [Category* J] {P Q : J ⥤ Augmented E}

/-- Original augmented-presentation isomorphisms induce the native normalized family comparison. -/
def normalizedPresentationIso (e : P ≅ Q) :
    P ⋙ normalizedAugmentationFunctor ≅ Q ⋙ normalizedAugmentationFunctor :=
  Functor.isoWhiskerRight e normalizedAugmentationFunctor

/-- The original augmented-presentation isomorphism gives its computed homology family comparison. -/
def homologyPresentationIso (e : P ≅ Q) (n : ℕ) :
    P ⋙ homologyAugmentationFunctor n ≅ Q ⋙ homologyAugmentationFunctor n :=
  Functor.isoWhiskerRight e (homologyAugmentationFunctor n)

/-- Identity augmented presentations yield the native identity comparison. -/
theorem homologyPresentationIso_refl (P : J ⥤ Augmented E) (n : ℕ) :
    homologyPresentationIso (Iso.refl P) n = Iso.refl (P ⋙ homologyAugmentationFunctor n) :=
  Functor.isoWhiskerRight_refl P (homologyAugmentationFunctor n)

/-- Inverses of the original presentation isomorphisms are preserved. -/
theorem homologyPresentationIso_symm (e : P ≅ Q) (n : ℕ) :
    (homologyPresentationIso e n).symm = homologyPresentationIso e.symm n :=
  Functor.isoWhiskerRight_symm e (homologyAugmentationFunctor n)

/-- Composing original presentation isomorphisms composes their homology comparisons. -/
theorem homologyPresentationIso_trans {R : J ⥤ Augmented E}
    (e : P ≅ Q) (f : Q ≅ R) (n : ℕ) :
    homologyPresentationIso (e ≪≫ f) n = homologyPresentationIso e n ≪≫ homologyPresentationIso f n :=
  Functor.isoWhiskerRight_trans e f (homologyAugmentationFunctor n)

end CategoryTheory.SimplicialObject.Augmented

namespace CategoryTheory.CosimplicialObject.Augmented

variable {E : Type*} [Category* E] [Abelian E]

/-- The original coaugmentation mapped by the native alternating-coface complex functor. -/
def cochainCoaugmentationFunctor : Augmented E ⥤
    Comma (CosimplicialObject.const E ⋙ AlgebraicTopology.alternatingCofaceMapComplex E)
      (𝟭 (CochainComplex E ℕ)) :=
  Comma.map (F₁ := 𝟭 E) (F₂ := AlgebraicTopology.alternatingCofaceMapComplex E)
    (F := AlgebraicTopology.alternatingCofaceMapComplex E) (Iso.refl _).hom (Iso.refl _).hom

/-- Fixed-degree cohomology retains both sides of the original coaugmentation. -/
def cohomologyCoaugmentationFunctor (n : ℕ) : Augmented E ⥤
    Comma (CosimplicialObject.const E ⋙ AlgebraicTopology.alternatingCofaceMapComplex E ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (𝟭 E) :=
  let H := AlgebraicTopology.alternatingCofaceMapComplex E ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n
  Comma.map (F₁ := 𝟭 E) (F₂ := H) (F := H) (Iso.refl _).hom (Iso.refl _).hom

variable {J : Type*} [Category* J] {P Q : J ⥤ Augmented E}

/-- The actual coaugmented-presentation isomorphism induces the native cochain family comparison. -/
def cochainPresentationIso (e : P ≅ Q) :
    P ⋙ cochainCoaugmentationFunctor ≅ Q ⋙ cochainCoaugmentationFunctor :=
  Functor.isoWhiskerRight e cochainCoaugmentationFunctor

/-- The native cohomology family comparison comes from the original coaugmented presentation. -/
def cohomologyPresentationIso (e : P ≅ Q) (n : ℕ) :
    P ⋙ cohomologyCoaugmentationFunctor n ≅ Q ⋙ cohomologyCoaugmentationFunctor n :=
  Functor.isoWhiskerRight e (cohomologyCoaugmentationFunctor n)

/-- Identity presentations retain the original identity cohomology comparison. -/
theorem cohomologyPresentationIso_refl (P : J ⥤ Augmented E) (n : ℕ) :
    cohomologyPresentationIso (Iso.refl P) n = Iso.refl (P ⋙ cohomologyCoaugmentationFunctor n) :=
  Functor.isoWhiskerRight_refl P (cohomologyCoaugmentationFunctor n)

/-- Inverse coaugmented presentation isomorphisms retain their computed inverse comparisons. -/
theorem cohomologyPresentationIso_symm (e : P ≅ Q) (n : ℕ) :
    (cohomologyPresentationIso e n).symm = cohomologyPresentationIso e.symm n :=
  Functor.isoWhiskerRight_symm e (cohomologyCoaugmentationFunctor n)

/-- The cohomology comparison retains composition of the original presentation isomorphisms. -/
theorem cohomologyPresentationIso_trans {R : J ⥤ Augmented E}
    (e : P ≅ Q) (f : Q ≅ R) (n : ℕ) :
    cohomologyPresentationIso (e ≪≫ f) n =
      cohomologyPresentationIso e n ≪≫ cohomologyPresentationIso f n :=
  Functor.isoWhiskerRight_trans e f (cohomologyCoaugmentationFunctor n)

end CategoryTheory.CosimplicialObject.Augmented
