/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Evaluation
public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Stabilization

/-!
# Actual native stabilization on the genuine enriched functor carrier

The literal free transpose uses the actual canonical successor map and
constructed free/evaluation adjunction. The general mates proof supplies
naturality. No legacy carrier or desired stabilization map is an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.SequentialSpectrum

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual native stabilization map is the original free-unit transpose. -/
def stabilizationMap (K : PointedCGWH.{u, v}) (n : ℕ) (A : PointedCGWH.{u, v}) :
    (freeAt K (n + 1)).obj (K ⊗ A) ⟶ (freeAt K n).obj A :=
  CategoryTheory.Spectra.Sequential.stabilizationMap K n A

/-- The complete adjunct retains the actual unit and canonical successor map. -/
theorem stabilizationMap_homEquiv
    (K : PointedCGWH.{u, v}) (n : ℕ) (A : PointedCGWH.{u, v}) :
    (freeAtEvaluationAdjunction K (n + 1)).homEquiv (K ⊗ A) ((freeAt K n).obj A)
        (stabilizationMap K n A) =
      (K ◁ (freeAtEvaluationAdjunction K n).unit.app A) ≫
        CategoryTheory.Spectra.Sequential.structureMap ((freeAt K n).obj A) n :=
  CategoryTheory.Spectra.Sequential.stabilizationMap_homEquiv K n A

/-- The actual stabilization maps are natural in their original base object. -/
theorem stabilizationMap_naturality (K : PointedCGWH.{u, v}) (n : ℕ)
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B) :
    (freeAt K (n + 1)).map (K ◁ f) ≫ stabilizationMap K n B =
      stabilizationMap K n A ≫ (freeAt K n).map f :=
  CategoryTheory.Spectra.Sequential.stabilizationMap_naturality K n f

/-- The literal native transposes form the actual canonical transformation. -/
def stabilizationTransformation (K : PointedCGWH.{u, v}) (n : ℕ) :
    tensorLeft K ⋙ freeAt K (n + 1) ⟶ freeAt K n :=
  CategoryTheory.Spectra.Sequential.stabilizationTransformation K n

end PointedCGWH.SequentialSpectrum
