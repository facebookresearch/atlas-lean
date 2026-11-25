/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.FrobeniusCoefficientUnit

/-!
# The compact Frobenius unit is tied to its geometric normalization

A compact unit bundles a geometric Frobenius normalization, and its arrow is normalized with that
normalization's derived extension and comparison isomorphism at the coefficient unit. Hence the
derived class of the arrow is determined by the normalization and the unit identification, and the
model is geometrically normalized.
-/

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.FrobeniusCoefficientUnit

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.Condensed
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels SolidWeakPerfectModels
open GeometricScalarRestriction SolidAnalyticModules GeometricTopologicalRestriction
open TopologicalRings FrobeniusModuleHomModels FrobeniusCoefficientUnit

attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {P : AffineUntilting p} {π : Pseudouniformizer p P}
  {h : π.element ∣ (p : P.pair.plus)} {M : TorsionModel p P π} {F : FrobeniusModel p P π h M}
  {U : UnitInductionModel p P π M}

/-- A geometric normalization witnesses geometric normalization. -/
example (N : GeometricNormalization p P π F) : IsGeometricallyNormalized p P π F := ⟨N⟩

/-- So does a compact unit, through its bundled normalization. -/
example (A : CompactUnit p P π h M F U) : IsGeometricallyNormalized p P π F :=
  A.source_normalization p P π h M F

/-- The coefficient representable is cofibrant with no further data, so the source of every
compact unit is that representable. -/
example (U : UnitInductionModel p P π M) :
    (unitSource p P π M U).obj = unitRepresentable p P π M U :=
  rfl

example (U : UnitInductionModel p P π M) :
    MathlibExt.CategoryTheory.DGQuasiFunctorModels.IsCofibrantModule
      (unitRepresentable p P π M U) :=
  unitRepresentable_cofibrant p P π M U

/-- The derived class of the unit arrow is determined by the bundled normalization (its derived
extension and its comparison at the coefficient unit) and the unit identification. -/
theorem cocycle_class_eq (A : CompactUnit p P π h M F U) :
    haveI := A.analytic_unit
    DerivedCategory.Q.map A.cocycle.homOf =
      (A.normalization.comparison U.val.unit).inv ≫
        ((A.normalization.extension.functor _ _ ⋙ M.analytic.functor).map A.unitIso.hom ≫
          M.analytic.functor.map (geometricUnitMap p P π h A.normalization.extension) ≫
            inv (M.analytic.unit.app (unitObject (TorsionRing p P π)))) ≫ A.unitIso.inv := by
  rw [Iso.eq_inv_comp, ← A.normalized]
  simp

end MathlibExtTest.FrobeniusCoefficientUnit
