/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

/-!
# Affine-family evaluation with all simplices fixed

Evaluation uses the actual replacement augmentation QA → A. For a
mapping simplex, it evaluates the corresponding compatible natural
family at A and at that augmentation. The target is the specified
fibrant representative of F, which is weakly equivalent to F.

The affine-value universe lift is the native type lift in each simplicial degree.
The map-construction output is constrained by the displayed evaluation
on every affine and every simplex. It cannot return an unrelated map
called evaluation. No mapping-stack geometricity or transgression
nondegeneracy is assumed.

Reference: PTVV, arXiv:1111.3209v4, §2.1, evaluation in Theorem 2.5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

open CategoryTheory MonoidalCategory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

variable (k : Type u) [CommRing k]

variable {k}

/-- The augmentation viewed as its actual constant mapping simplex. -/
def affineAugmentationSimplex (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (n : SimplexCategoryᵒᵖ) : ((derivedSpecFunctor Q A).obj A).obj n :=
  Functor.HomObj.ofNatTrans (Q.augmentation.app A)

/-- The computed evaluation in a given affine simplicial degree. -/
def evaluateDegree (Q : AlgebraReplacementFunctor k) (X F : Prestack k)
    (R : FibrantReplacement F) (A : SAlg k) (n : SimplexCategoryᵒᵖ)
    (a : ((mappingPrestackFunctor k Q X F R).obj A).obj n)
    (x : (X.obj A).obj n) : (R.model.obj A).obj n :=
  ((a.app n (𝟙 n)).app A) (ULift.up (affineAugmentationSimplex Q A n), x)

/-- An actual evaluation map whose value is fixed on every mapping simplex. -/
structure EvaluationModel (Q : AlgebraReplacementFunctor k) (X F : Prestack k)
    (R : FibrantReplacement F) where
  map : mappingPrestackFunctor k Q X F R ⊗ X ⟶ R.model
  value : ∀ (A : SAlg k) (n : SimplexCategoryᵒᵖ)
    (a : ((mappingPrestackFunctor k Q X F R).obj A).obj n) (x : (X.obj A).obj n),
    (map.app A).app n (a, x) = evaluateDegree Q X F R A n a x

end MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
