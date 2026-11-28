/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.SheafModuleGradedCohomology

/-!
# Tests for the cup product and the continuous coefficient classes

The unit is a nonzero class over a nonempty scheme, so cup product with it is not the zero map;
the degree-zero `Ext` classes of the coefficient maps recover those maps.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SheafModuleGradedCohomology
open MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

universe u v w e

section RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) [Abelian (Modules R)] [HasExt.{e} (Modules R)]

example {n : ℕ} (x : Cohomology R n) : cup R (one R) x (zero_add n) = x := one_cup R x

example {n : ℕ} (x : Cohomology R n) : cup R x (one R) (add_zero n) = x := cup_one R x

end RingedSite

section ContinuousCoefficients

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E] [Nontrivial E]
  (X : Scheme.{0}) [Nonempty X] [HasExt.{e} (CoefficientModules E X)]

/-- Over a nonempty scheme, the unit is nonzero. -/
example : one (coefficientRing E X) ≠ 0 := by
  intro h
  have h' : Adic.constantClass E X 1 = Adic.constantClass E X 0 := by
    rw [Adic.constantClass_one, Adic.constantClass_zero]
    exact h
  have hbad : (1 : E) = 0 := Adic.constantClass_injective E X h'
  exact one_ne_zero hbad

/-- Cup product with the unit is the identity, so it is not the zero map. -/
example {n : ℕ} (x : Adic.Cohomology E X n) (hx : x ≠ 0) :
    cup (coefficientRing E X) (Adic.constantClass E X 1) x (zero_add n) ≠ 0 := by
  simpa only [Adic.constantClass_one, one_cup] using hx

end ContinuousCoefficients

section UnitComparison

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  (X : Scheme.{0}) [HasExt.{e} (CoefficientSheaf X E)]

/-- The degree-zero class of the coefficient map is that map. -/
example :
    Abelian.Ext.homEquiv₀ (Adic.coefficientUnitClass E X) = unitCoefficientMap E X := by
  apply (Abelian.Ext.mk₀_bijective
    (MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality.constantUnit E X)
    (continuousModuleSheaf E (ULift.{1} E) X)).1
  simp [Adic.coefficientUnitClass]

/-- The degree-zero class of `unitUnderlyingIso` is that isomorphism. -/
example :
    Abelian.Ext.homEquiv₀ (Adic.underlyingUnitClass E X) = (unitUnderlyingIso E X).hom := by
  apply (Abelian.Ext.mk₀_bijective
    ((underlying E X).obj (ringUnit (coefficientRing E X)))
    (continuousModuleSheaf E (ULift.{1} E) X)).1
  simp [Adic.underlyingUnitClass]

end UnitComparison
