/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-!
# Wanted native coherent DG-module families and affine normalization

These requests construct the actual scalar-extension/cocartesian family
models and their native categorical section law. Affine Perf is compared
by the actual family evaluation, using categorical weak equivalences.
No arc-descent theorem or Kan-space substitution is supplied as input.

References: Toën--Vezzosi HAG II Part2; Lurie HTT §3.3.3;
Bhatt--Mathew arXiv:1807.04725v4 §§5--6.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies

universe u

/-- Construct the actual normalized affine scalar-extension system. -/
def_wanted affine_dg_scalar_system (k : Type u) [CommRing k] (N : ShuffleAlgebraFunctor k) :
  AffineScalarSystem N

/-- Construct the cocartesian module family with every actual native transport fixed. -/
def_wanted affine_dg_module_fibration (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) : AffineModuleFibration N S

/-- Cocartesian sections form the actual categorical limit quasicategory. -/
theorem_wanted native_cocartesian_section_quasicategory (A B E : SSet.{u})
    [SSet.Quasicategory A] [SSet.Quasicategory B] [SSet.Quasicategory E]
    (p : E ⟶ B) (q : A ⟶ B) (P : CocartesianFibration p) :
  SSet.Quasicategory (sectionsOver p q)

/-- Affine Perf is the actual normalized perfect DG category by family evaluation. -/
def_wanted derived_affine_perfect_normalization (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (N : ShuffleAlgebraFunctor k)
    (S : AffineScalarSystem N) (M : AffineModuleFibration N S)
    (A : SAlg k) (F : AffineStackModel Q A) :
  AffinePerfNormalization M F.stack.functor
    (family F.stack.functor A (op (SimplexCategory.mk 0))
      ((F.augmentation.app A).app (op (SimplexCategory.mk 0))
        (ULift.up (MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation.affineAugmentationSimplex
          Q A (op (SimplexCategory.mk 0))))))
