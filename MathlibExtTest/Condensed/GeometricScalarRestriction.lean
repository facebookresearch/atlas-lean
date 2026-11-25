/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.SolidAnalyticModules
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Tactic.NormNum

/-! The geometric coefficient ring retains a nonconstant section on a
compact two-point test. Sending the polynomial scalar T to2 multiplies
its values1 and3 to2 and6. No solid/DG reflection provider is assumed.
-/

open CategoryTheory Opposite
open MathlibExt.Condensed.TopologicalRings
open MathlibExt.Condensed.GeometricScalarRestriction
open MathlibExt.Condensed.SolidAnalyticModules

noncomputable section

private abbrev A := ULift.{1} ℤ
private instance : TopologicalSpace A := ⊥
private instance : TopologicalSpace (Fin 2) := ⊥
private instance : DiscreteTopology A := ⟨rfl⟩
private instance : DiscreteTopology (Fin 2) := ⟨rfl⟩

private abbrev test : CompHaus.{0} := CompHaus.of (Fin 2)
private def sectionValues : C(test, A) :=
  ⟨fun i ↦ ULift.up (if i = 0 then 1 else 3), continuous_of_discreteTopology⟩

private abbrev restrictedUnit := (restriction A IntegerPolynomial
  (polynomialScalars A (2 : A))).obj (SheafOfModules.unit (ringSheaf A))

private instance : Module IntegerPolynomial C(test, A) :=
  (restrictedUnit.obj.obj (op test)).isModule

example : ((ULift.up (Polynomial.X : Polynomial ℤ) : IntegerPolynomial) •
    (sectionValues : restrictedUnit.obj.obj (op test))) (0 : Fin 2) = (2 : A) := by
  change (constantScalars A IntegerPolynomial (polynomialScalars A 2) (op test)
    (ULift.up Polynomial.X) * sectionValues) 0 = _
  simp [constantScalars, polynomialScalars, sectionValues, ULift.ringEquiv]
  change (2 : A) * 1 = 2
  exact mul_one _

example : ((ULift.up (Polynomial.X : Polynomial ℤ) : IntegerPolynomial) •
    (sectionValues : restrictedUnit.obj.obj (op test))) (1 : Fin 2) = (6 : A) := by
  change (constantScalars A IntegerPolynomial (polynomialScalars A 2) (op test)
    (ULift.up Polynomial.X) * sectionValues) 1 = _
  simp [constantScalars, polynomialScalars, sectionValues, ULift.ringEquiv]
  change (2 : A) * 3 = 6
  decide
