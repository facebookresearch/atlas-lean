/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-!
# Wanted coherent affine DR and global closed-form realization

The affine functor, actual weighted product diagram and native global
limits are all normalized publicly. These requests assemble the sourced
models and prove the affine restriction comparison. They do not assume
mapping-stack geometricity or shifted symplectic nondegeneracy.

Reference: PTVV arXiv:1111.3209v4 §1.1, Definitions 1.7--1.8.
-/

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u v w

/-- Assemble the actual generator-normalized homotopy-invariant affine DR functor. -/
def_wanted derived_affine_deRham_system (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) : AffineDRSystem Q

/-- Assemble actual weighted NC complexes and maps into the normalized diagram. -/
def_wanted weighted_negative_cyclic_diagram (k : Type u) [CommRing k]
    (J : Type v) [Category.{w} J] (F : J ⥤ GradedMixed k) (p : ℤ) :
  NegativeCyclicDiagram F p

/-- Realize the two actual family diagrams by sized injective space replacements. -/
def_wanted global_closed_form_realization (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k) :
  GlobalFormModel D p n NC X

/-- The actual limit of the specified injectively fibrant space diagram is Kan. -/
theorem_wanted sized_space_homotopy_limit_kan (J : Type v) [Category.{w} J]
    (D : J ⥤ SSet.{max u v w}) (R : SpaceDiagramReplacement.{u, v, w} D) :
  SSet.KanComplex (Limits.limit R.diagram)

/-- An actual derived affine stack has the source NC closed-form realization.
The point x is the image of the algebra augmentation, not an arbitrary family. -/
def_wanted derived_affine_closed_form_normalization (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicDiagram D.functor (p : ℤ))
    (A : SAlg k) (S : AffineStackModel Q A)
    (M : GlobalFormModel D p n NC S.stack.functor) :
  AffineClosedFormNormalization D p n NC A S.stack.functor
    ((S.augmentation.app A).app (op (SimplexCategory.mk 0))
      (ULift.up (MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation.affineAugmentationSimplex
        Q A (op (SimplexCategory.mk 0))))) M
