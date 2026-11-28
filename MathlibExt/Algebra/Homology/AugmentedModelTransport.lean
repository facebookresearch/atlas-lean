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
# Normalization and homology of augmented presentations

In an abelian category E, an augmented simplicial object has a map X → const(A). Dold–Kan
normalization maps it to N(X) → N(const(A)); degree-n homology then maps both sides of this
augmentation. A coaugmented cosimplicial object const(A) → X similarly gives a map of
alternating-coface cochain complexes and of their degree-n cohomology.

For families of these presentations, a natural isomorphism induces the corresponding
normalized-complex or homology-family isomorphism. The induced comparisons preserve identity,
inverse and composition, retaining the augmentation or coaugmentation map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.SimplicialObject.Augmented

variable {E : Type*} [Category* E] [Abelian E]

/-- Dold–Kan normalization of an augmented simplicial object.

Apply normalization to both the simplicial object and its augmentation X → const(A), obtaining
N(X) → N(const(A)). -/
def normalizedAugmentationFunctor : Augmented E ⥤
    Comma (𝟭 (ChainComplex E ℕ))
      (SimplicialObject.const E ⋙ CategoryTheory.Abelian.DoldKan.N (A := E)) :=
  Comma.map (F₁ := CategoryTheory.Abelian.DoldKan.N (A := E)) (F₂ := 𝟭 E)
    (F := CategoryTheory.Abelian.DoldKan.N (A := E)) (Iso.refl _).hom (Iso.refl _).hom

/-- The source complex of a normalized augmentation.

The left object of the normalized augmentation is the Dold–Kan normalized complex of X.left. -/
theorem normalizedAugmentationFunctor_obj_left (X : Augmented E) :
    (normalizedAugmentationFunctor.obj X).left =
      CategoryTheory.Abelian.DoldKan.N.obj X.left := rfl

/-- The map of a normalized augmentation.

The normalized augmentation morphism is N applied to the simplicial augmentation X.hom. -/
theorem normalizedAugmentationFunctor_obj_hom (X : Augmented E) :
    (normalizedAugmentationFunctor.obj X).hom =
      CategoryTheory.Abelian.DoldKan.N.map X.hom := by
  simp [normalizedAugmentationFunctor]

/-- Degreewise homology of a normalized augmentation.

Apply degree-n homology to both sides of N(X) → N(const(A)), retaining the resulting morphism
in the augmented comma-category presentation. -/
def homologyAugmentationFunctor (n : ℕ) : Augmented E ⥤
    Comma (𝟭 E) (SimplicialObject.const E ⋙ CategoryTheory.Abelian.DoldKan.N (A := E) ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n) :=
  let H := CategoryTheory.Abelian.DoldKan.N (A := E) ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  Comma.map (F₁ := H) (F₂ := 𝟭 E) (F := H) (Iso.refl _).hom (Iso.refl _).hom

variable {J : Type*} [Category* J] {P Q : J ⥤ Augmented E}

/-- The normalized comparison of augmented presentation families.

For e : P ≅ Q between families of augmented simplicial objects, postcomposition with
normalizedAugmentationFunctor gives their normalized family isomorphism. -/
def normalizedPresentationIso (e : P ≅ Q) :
    P ⋙ normalizedAugmentationFunctor ≅ Q ⋙ normalizedAugmentationFunctor :=
  Functor.isoWhiskerRight e normalizedAugmentationFunctor

/-- The homology comparison of augmented presentation families.

For e : P ≅ Q and degree n, postcomposition with homologyAugmentationFunctor n gives the
family comparison on the homology of both sides of the augmentation. -/
def homologyPresentationIso (e : P ≅ Q) (n : ℕ) :
    P ⋙ homologyAugmentationFunctor n ≅ Q ⋙ homologyAugmentationFunctor n :=
  Functor.isoWhiskerRight e (homologyAugmentationFunctor n)

/-- Identity of the augmented homology-family comparison.

An identity presentation isomorphism induces the identity homology-family isomorphism. -/
theorem homologyPresentationIso_refl (P : J ⥤ Augmented E) (n : ℕ) :
    homologyPresentationIso (Iso.refl P) n = Iso.refl (P ⋙ homologyAugmentationFunctor n) :=
  Functor.isoWhiskerRight_refl P (homologyAugmentationFunctor n)

/-- Inverses of augmented homology-family comparisons.

The inverse comparison induced by e is the comparison induced by e⁻¹. -/
theorem homologyPresentationIso_symm (e : P ≅ Q) (n : ℕ) :
    (homologyPresentationIso e n).symm = homologyPresentationIso e.symm n :=
  Functor.isoWhiskerRight_symm e (homologyAugmentationFunctor n)

/-- Composition of augmented homology-family comparisons.

The comparison induced by e followed by f equals the composite of their induced homology-
family comparisons. -/
theorem homologyPresentationIso_trans {R : J ⥤ Augmented E}
    (e : P ≅ Q) (f : Q ≅ R) (n : ℕ) :
    homologyPresentationIso (e ≪≫ f) n = homologyPresentationIso e n ≪≫ homologyPresentationIso f
      n :=
  Functor.isoWhiskerRight_trans e f (homologyAugmentationFunctor n)

end CategoryTheory.SimplicialObject.Augmented

namespace CategoryTheory.CosimplicialObject.Augmented

variable {E : Type*} [Category* E] [Abelian E]

/-- The alternating-coface complex of a coaugmented presentation.

Apply the alternating-coface complex functor to const(A) → X, obtaining a map from the
constant-object cochain complex to that of X. -/
def cochainCoaugmentationFunctor : Augmented E ⥤
    Comma (CosimplicialObject.const E ⋙ AlgebraicTopology.alternatingCofaceMapComplex E)
      (𝟭 (CochainComplex E ℕ)) :=
  Comma.map (F₁ := 𝟭 E) (F₂ := AlgebraicTopology.alternatingCofaceMapComplex E)
    (F := AlgebraicTopology.alternatingCofaceMapComplex E) (Iso.refl _).hom (Iso.refl _).hom

/-- Degreewise cohomology of a coaugmented presentation.

Apply degree-n cohomology to both sides of the alternating-coface complex map determined by
the coaugmentation. -/
def cohomologyCoaugmentationFunctor (n : ℕ) : Augmented E ⥤
    Comma (CosimplicialObject.const E ⋙ AlgebraicTopology.alternatingCofaceMapComplex E ⋙
      HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) (𝟭 E) :=
  let H := AlgebraicTopology.alternatingCofaceMapComplex E ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n
  Comma.map (F₁ := 𝟭 E) (F₂ := H) (F := H) (Iso.refl _).hom (Iso.refl _).hom

variable {J : Type*} [Category* J] {P Q : J ⥤ Augmented E}

/-- The cochain comparison of coaugmented presentation families.

For a natural isomorphism e : P ≅ Q, postcomposition with cochainCoaugmentationFunctor gives
an isomorphism of their cochain presentations. -/
def cochainPresentationIso (e : P ≅ Q) :
    P ⋙ cochainCoaugmentationFunctor ≅ Q ⋙ cochainCoaugmentationFunctor :=
  Functor.isoWhiskerRight e cochainCoaugmentationFunctor

/-- The cohomology comparison of coaugmented presentation families.

For e : P ≅ Q and n ≥ 0, apply the cohomology-coaugmentation functor to obtain the comparison
of both coaugmentation sides. -/
def cohomologyPresentationIso (e : P ≅ Q) (n : ℕ) :
    P ⋙ cohomologyCoaugmentationFunctor n ≅ Q ⋙ cohomologyCoaugmentationFunctor n :=
  Functor.isoWhiskerRight e (cohomologyCoaugmentationFunctor n)

/-- Identity of the coaugmented cohomology-family comparison.

The identity presentation isomorphism induces the identity cohomology comparison. -/
theorem cohomologyPresentationIso_refl (P : J ⥤ Augmented E) (n : ℕ) :
    cohomologyPresentationIso (Iso.refl P) n = Iso.refl (P ⋙ cohomologyCoaugmentationFunctor n) :=
  Functor.isoWhiskerRight_refl P (cohomologyCoaugmentationFunctor n)

/-- Inverses of coaugmented cohomology-family comparisons.

The inverse induced cohomology comparison is the comparison induced by the inverse
presentation isomorphism. -/
theorem cohomologyPresentationIso_symm (e : P ≅ Q) (n : ℕ) :
    (cohomologyPresentationIso e n).symm = cohomologyPresentationIso e.symm n :=
  Functor.isoWhiskerRight_symm e (cohomologyCoaugmentationFunctor n)

/-- Composition of coaugmented cohomology-family comparisons.

Composing presentation isomorphisms composes the resulting cohomology-family comparisons. -/
theorem cohomologyPresentationIso_trans {R : J ⥤ Augmented E}
    (e : P ≅ Q) (f : Q ≅ R) (n : ℕ) :
    cohomologyPresentationIso (e ≪≫ f) n =
      cohomologyPresentationIso e n ≪≫ cohomologyPresentationIso f n :=
  Functor.isoWhiskerRight_trans e f (cohomologyCoaugmentationFunctor n)

end CategoryTheory.CosimplicialObject.Augmented
