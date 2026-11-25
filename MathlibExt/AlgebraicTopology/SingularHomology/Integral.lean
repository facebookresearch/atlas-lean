/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicTopology

/-- Integral coefficients in the universe of the target abelian category. -/
abbrev singularIntegralCoefficients : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} ℤ)

noncomputable instance singularIntegralCoefficients_projective :
    CategoryTheory.Projective (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  change CategoryTheory.Projective
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj (ModuleCat.of ℤ (ULift.{u} ℤ)))
  infer_instance

/-- The universe-polymorphic integral singular chain-complex functor. -/
noncomputable abbrev singularIntegralChainFunctor :
    TopCat.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  (singularChainComplexFunctor AddCommGrpCat.{u}).obj singularIntegralCoefficients

/-- The universe-polymorphic integral singular homology functor in degree `n`. -/
noncomputable abbrev singularIntegralHomologyFunctor (n : ℕ) :
    TopCat.{u} ⥤ AddCommGrpCat.{u} :=
  (singularHomologyFunctor AddCommGrpCat.{u} n).obj singularIntegralCoefficients

/-- Universe-polymorphic integral singular homology. -/
noncomputable abbrev singularIntegralHomology (n : ℕ) (X : TopCat.{u}) :
    AddCommGrpCat.{u} :=
  (singularIntegralHomologyFunctor n).obj X

end AlgebraicTopology
