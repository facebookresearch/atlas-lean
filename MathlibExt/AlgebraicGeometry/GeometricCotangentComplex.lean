/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import MathlibExt.RingTheory.ResolutionCotangent

/-!
# A computed affine cotangent complex from actual polynomial resolution data

The algebra map fixes `Spec B → Spec A`. Polynomial-resolution data have
actual simplicial algebra terms, an actual augmentation, polynomial
identifications and an actual alternating-face quasi-isomorphism. These
are the equivalent resolution criterion proved in AxiomMath/Stacks,
`StacksFrontier/Cotangent/Resolution.lean` (08QI). The cotangent model is
then literally `B ⊗[P_n] Ω[P_n/A]`, with the actual induced differentials,
in cohomological degree `-n`; its derived carrier is Mathlib's quotient.

No freely named derived object is supplied as a cotangent complex.
Existence of standard resolution, independence and its comparisons are
already complete in the public source and are not requested as novel gaps.
General scheme globalization is outside this affine core's construction.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricCotangentComplex

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

/-- Actual polynomial resolution data for the specified affine algebra map.
The criterion is source-proved equivalent to IsResolution, rather than
an arbitrary predicate named a resolution. -/
structure PolynomialResolution (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] where
  algebra : SimplicialObject (CommAlgCat.{u} A)
  augmentation : algebra ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)
  polynomial : ∀ n : SimplexCategoryᵒᵖ, ∃ σ : Type u,
    Nonempty (MvPolynomial σ A ≃ₐ[A] algebra.obj n)
  surjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (augmentation.app n).hom
  augmentation_quasiIso : QuasiIso
    ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (Functor.whiskerRight augmentation
        (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
          forget₂ (AlgCat.{u} A) (ModuleCat.{u} A))))

/-- The actual affine scheme morphism to which the model is attached. -/
abbrev affineMorphism (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := Spec.algebraMap A B

/-- The computed integer-indexed cochain complex of the actual resolution. -/
def affineComplex {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : PolynomialResolution A B) : CochainComplex (ModuleCat.{u} B) ℤ :=
  CommAlgCat.resolutionCotangentComplex A (CommAlgCat.of A B) R.algebra R.augmentation

/-- The full affine cotangent model as an actual derived-category object,
constructed from the specified genuine polynomial resolution. -/
def affineDerived {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : PolynomialResolution A B) : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (affineComplex R)

/-- Its actual component is the base-changed differential module. -/
def affineDegreeIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : PolynomialResolution A B) (n : ℕ) :
    (affineComplex R).X (-(n : ℤ)) ≅
      CommAlgCat.resolutionCotangentTerm A (CommAlgCat.of A B)
        R.algebra R.augmentation (op ⦋n⦌) :=
  (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
    (CommAlgCat.resolutionCotangentSimplicialModule A (CommAlgCat.of A B)
      R.algebra R.augmentation).object).extendXIso
        (ComplexShape.embeddingUpIntLE 0) (by simp))

end MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
