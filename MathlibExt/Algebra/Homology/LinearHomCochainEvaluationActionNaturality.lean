/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
import MathlibExt.Algebra.Homology.ChainGradedPairingDegreeZeroActionNaturality

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomCochainEvaluationActionMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Naturality of the evaluation action for single complexes. -/
@[reassoc]
public theorem linearHomCochainEvaluationAction_naturality
    {M M' : ModuleCat.{u} R} (a : M ⟶ M') (q : ℕ) :
    chainGradedPairingDegreeZeroAction R
        (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)).hom
        q ≫ ((ChainComplex.single₀ (ModuleCat.{u} R)).map a).f q =
      (a ⊗ₘ 𝟙 _) ≫ chainGradedPairingDegreeZeroAction R
        (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')).hom
        q := by
  simpa only [HomologicalComplex.id_f] using
    chainGradedPairingDegreeZeroAction_naturality R M M'
      (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ))
      (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')
      (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)).hom
      (rightUnitor ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M')).hom
      a (𝟙 (tensorUnit (ModuleCat.{u} R) (ComplexShape.down ℕ)))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).map a)
      (MonoidalCategory.rightUnitor_naturality
        ((ChainComplex.single₀ (ModuleCat.{u} R)).map a)) q

end HomologicalComplex
