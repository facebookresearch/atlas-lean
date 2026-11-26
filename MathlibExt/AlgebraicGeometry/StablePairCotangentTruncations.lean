/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Generator-normalized cotangent truncations for smooth embeddings

The target is the actual two-term conormal/differential complex of the
surjective algebra extension. A polynomial degree-zero lift fixes the
map on d(p). In degree -1 the image is the actual conormal class of the
difference of the two lifted faces. Higher target degrees are zero.

These formulas fix the whole affine cochain map, and supply the
coherent source comparisons needed for the Huybrechts–Thomas
truncated cotangent model. No arbitrary cotangent comparison is given.

Reference: Huybrechts–Thomas, arXiv:0805.3527v2, §2.1;
Illusie cotangent comparison via a polynomial resolution, Stacks 08QI.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairCotangentTruncations

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
open GeometricCotangentComplex
open scoped TensorProduct

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable (P : Algebra.Extension.{0} k A) (R : PolynomialResolution k A)

/-- The actual conormal complex of the algebra extension. -/
def truncatedComplex : CochainComplex (ModuleCat A) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat A) 0).map (ModuleCat.ofHom P.cotangentComplex))

/-- A polynomial lift to the actual smooth ambient algebra, with its augmentation fixed. -/
structure PolynomialLift where
  map : R.algebra.obj (op ⦋0⦌) →ₐ[k] P.Ring
  augmentation : ∀ p, (algebraMap P.Ring A) (map p) = R.augmentation.app (op ⦋0⦌) p
  relation : ∀ p : R.algebra.obj (op ⦋1⦌),
    map (R.algebra.map (SimplexCategory.δ (0 : Fin 2)).op p) -
      map (R.algebra.map (SimplexCategory.δ (1 : Fin 2)).op p) ∈ P.ker

/-- The genuine conormal generator given by the lifted face difference. -/
def relationClass (L : PolynomialLift P R) (p : R.algebra.obj (op ⦋1⦌)) : P.Cotangent :=
  Algebra.Extension.Cotangent.mk
    ⟨L.map (R.algebra.map (SimplexCategory.δ (0 : Fin 2)).op p) -
      L.map (R.algebra.map (SimplexCategory.δ (1 : Fin 2)).op p), L.relation p⟩

/-- A comparison to the actual embedding conormal complex is fixed on
every native differential generator in both possibly nonzero degrees. -/
structure AffineTruncation (L : PolynomialLift P R) where
  map : affineComplex R ⟶ truncatedComplex P
  zero_normalized : ∀ p : R.algebra.obj (op ⦋0⦌),
    ((map.f 0) ≫
      (CochainComplex.mappingCone.snd
        ((CochainComplex.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom P.cotangentComplex))).v 0 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A P.CotangentSpace)).hom)
        ((affineDegreeIso R 0).inv
          (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k A)
            R.algebra R.augmentation (op ⦋0⦌) p)) =
        (1 : A) ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring (L.map p)
  negative_normalized : ∀ p : R.algebra.obj (op ⦋1⦌),
    ((map.f (-1)) ≫
      (CochainComplex.mappingCone.fst
        ((CochainComplex.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom P.cotangentComplex))).val.v (-1) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A P.Cotangent)).hom)
        ((affineDegreeIso R 1).inv
          (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k A)
            R.algebra R.augmentation (op ⦋1⦌) p)) =
        relationClass P R L p

end MathlibExt.AlgebraicGeometry.StablePairCotangentTruncations
