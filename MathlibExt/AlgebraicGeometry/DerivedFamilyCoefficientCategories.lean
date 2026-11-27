/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The DG coefficient category of all affine families

The objects are the actual algebra/simplex families of a prestack.
The Hom complex is the coproduct, over actual family arrows, of the
target normalized coefficient algebra. Composition first applies the
actual coefficient map and then the native coefficient product.

Covariant DG modules over this category are semilinear coefficient
diagrams. The opposite coefficient algebra is used because the affine
module convention in the source is a right module. The category model
fixes every homogeneous arrow-labelled generator, not only its H0.
Generic assembly of this explicit enrichment is requested separately.

References: PTVV arXiv:1111.3209v4, conventions and §2.1;
Keller, Deriving DG categories, §1; HAG II math/0404373v7, §1.3.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

universe u
variable {k : Type u} [CommRing k]

/-- Actual opposite coefficient Hom, with its transported normalization. -/
def affineCoefficient (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    (A : SAlg k) : Cochains (LargeScalar k) :=
  dgHomComplex (LargeScalar k) (op (coefficientObject L N A))
    (op (coefficientObject L N A))

/-- The entire actual coefficient cochain map, including the source algebra map. -/
def affineCoefficientMap (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    {A B : SAlg k} (f : A ⟶ B) : affineCoefficient L N A ⟶ affineCoefficient L N B :=
  (EnrichedFunctor.op (V := Cochains (LargeScalar k)) (coefficientLargeMap L N f)).map
    (op (coefficientObject L N A))
    (op (coefficientObject L N A))

/-- The actual enriched coefficient identity, with its exact cochain target. -/
def affineCoefficientUnit (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    (A : SAlg k) :
    (𝟙_ (Cochains (LargeScalar k))) ⟶ affineCoefficient L N A :=
  eId (Cochains (LargeScalar k)) (op (coefficientObject L N A))

/-- Every actual family arrow has its own target-coefficient summand. -/
def arrowCoefficients (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    (X : Prestack k) (j l : Families X) : Cochains (LargeScalar k) :=
  ∐ (fun _f : j ⟶ l => affineCoefficient L N ((algebraProjection X).obj l))

/-- The native coproduct inclusion followed by the fixed Hom comparison. -/
def coefficientGenerator {L : CochainLiftModel k} {N : ShuffleAlgebraFunctor k}
    {X : Prestack k} [DGCategory (LargeScalar k) (Families X)]
    (H : ∀ j l : Families X,
      dgHomComplex (LargeScalar k) j l ≅ arrowCoefficients L N X j l)
    {j l : Families X} (f : j ⟶ l) (p : ℤ)
    (a : (affineCoefficient L N ((algebraProjection X).obj l)).X p) :
    DGHom (LargeScalar k) p j l :=
  (((Sigma.ι (fun _f : j ⟶ l => affineCoefficient L N ((algebraProjection X).obj l)) f ≫
    (H j l).inv).f p).hom a)

/-- A family enrichment has the literal coproduct Hom and the full
semilinear composition formula. It asserts no global-section comparison. -/
structure FamilyCoefficientCategory (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    (X : Prestack k) where
  [enrichment : DGCategory (LargeScalar k) (Families X)]
  homIso : ∀ j l : Families X,
    dgHomComplex (LargeScalar k) j l ≅ arrowCoefficients L N X j l
  identity : ∀ j : Families X,
    dgId (LargeScalar k) j =
      coefficientGenerator homIso (𝟙 j) 0
        (dgId (LargeScalar k) (op (coefficientObject L N ((algebraProjection X).obj j))))
  composition : ∀ (j l z : Families X) (f : j ⟶ l) (g : l ⟶ z)
    (p q n : ℤ) (h : p + q = n)
    (a : (affineCoefficient L N ((algebraProjection X).obj l)).X p)
    (b : (affineCoefficient L N ((algebraProjection X).obj z)).X q),
    dgComp (LargeScalar k)
      (coefficientGenerator homIso f p a) (coefficientGenerator homIso g q b) h =
      coefficientGenerator homIso (f ≫ g) n
        (dgComp (LargeScalar k)
          (((affineCoefficientMap L N ((algebraProjection X).map g)).f p).hom a) b h)

/-- The actual generator labelled by the family arrow and homogeneous coefficient. -/
def generator {L : CochainLiftModel k} {N : ShuffleAlgebraFunctor k} {X : Prestack k}
    (C : FamilyCoefficientCategory L N X) {j l : Families X} (f : j ⟶ l) (p : ℤ)
    (a : (affineCoefficient L N ((algebraProjection X).obj l)).X p) :
    letI := C.enrichment; DGHom (LargeScalar k) p j l := by
  letI := C.enrichment
  exact coefficientGenerator C.homIso f p a

/-- A coefficient section is a native DG functor, retaining every family arrow
and every homogeneous coefficient action. -/
abbrev CoefficientSection {L : CochainLiftModel k} {N : ShuffleAlgebraFunctor k}
    {X : Prestack k} (C : FamilyCoefficientCategory L N X) :=
  letI := C.enrichment
  DGFunctor (LargeScalar k) (Families X) (Cochains (LargeScalar k))

/-- Full enriched Hom of coefficient sections, rather than pointwise vector spaces. -/
def sectionHom {L : CochainLiftModel k} {N : ShuffleAlgebraFunctor k}
    {X : Prestack k} {C : FamilyCoefficientCategory L N X}
    (E F : CoefficientSection C) : Cochains (LargeScalar k) := by
  letI := C.enrichment
  exact dgHomComplex (LargeScalar k) E F

end MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
