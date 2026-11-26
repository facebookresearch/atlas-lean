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
public import Mathlib.Algebra.MvPolynomial.Basic
public import MathlibExt.RingTheory.ResolutionCotangent

/-!
# The affine cotangent complex computed from a polynomial resolution

For an algebra `A → B`, a `PolynomialResolution A B` is a simplicial commutative `A`-algebra `P•`
with an augmentation `ε : P• ⟶ B` such that every `Pₙ` is a polynomial `A`-algebra, every `εₙ` is
surjective, and `ε` induces a quasi-isomorphism of alternating face map complexes. By Stacks
Remark 08QI, under the first two conditions the third is equivalent to `ε` being a trivial Kan
fibration of underlying simplicial sets, that is, to `P•` being a resolution of `B` over `A`.
AxiomMath/Stacks proves this as `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae` in
`StacksFrontier/Cotangent/Resolution.lean`, with the quasi-isomorphism stated for underlying
abelian groups, which is equivalent to the `A`-module version used here.

`affineComplex R` is the complex `Ω[P•⁄A] ⊗[P•] B` of `CommAlgCat.resolutionCotangentComplex`,
with `B ⊗[Pₙ] Ω[Pₙ⁄A]` and its induced differentials in cohomological degree `-n`
(`affineDegreeIso`), and `affineDerived R` is its image in the derived category. That it does not
depend on the resolution, and hence is the cotangent complex `L_{B/A}` of Stacks Tag 08PN, is not
proved here. Only the affine case is treated.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricCotangentComplex

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

attribute [local instance] HasDerivedCategory.standard

universe u

/-- Polynomial resolution data for `A → B` (Stacks, Remark 08QI): a simplicial commutative
`A`-algebra with an augmentation to `B` that is a degreewise surjection from polynomial
`A`-algebras and a quasi-isomorphism of alternating face map complexes of `A`-modules. Under the
first two conditions the third is equivalent to being a resolution, a trivial Kan fibration of
underlying simplicial sets (AxiomMath/Stacks,
`CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`). -/
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

/-- The complex `Ω[P•⁄A] ⊗[P•] B` computed from the resolution, with simplicial degree `n` in
cohomological degree `-n`. -/
def affineComplex {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : PolynomialResolution A B) : CochainComplex (ModuleCat.{u} B) ℤ :=
  CommAlgCat.resolutionCotangentComplex A (CommAlgCat.of A B) R.algebra R.augmentation

/-- The image of `affineComplex R` in the derived category of `B`-modules. -/
def affineDerived {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (R : PolynomialResolution A B) : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (affineComplex R)

/-- The component of `affineComplex R` in degree `-n` is `B ⊗[Pₙ] Ω[Pₙ⁄A]`. -/
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
