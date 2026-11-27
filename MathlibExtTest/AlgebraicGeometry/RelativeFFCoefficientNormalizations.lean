/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
import MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RelativeFFCoefficientNormalizations

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
open MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
open MathlibExt.AlgebraicGeometry.RelativeWittFrobenius
open MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels
open MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels
open MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E) (S : Base p C)

/-- The relative q-Frobenius fixes the original ramified uniformizer, not merely p. -/
example : frobenius p C S (prime p C S) = prime p C S := by
  change ramifiedFrobenius p C (residueTest p C S)
    (prime p C S) = prime p C S
  exact ramifiedFrobenius_coefficient p C (residueTest p C S) C.uniformizer

/-- Every actual annular chart inverts both original period generators. -/
example (P : RationalPresentation p C S) :
    IsUnit (chartCoefficient p C S P (prime p C S)) ∧
      IsUnit (chartCoefficient p C S P (teichmuller p C S S.varpi)) :=
  chartPunctures_unit p C S P

/-- The displayed cocharacter point is in its exact positive double orbit. -/
example (T : Untilting p C S) (L : ScalarLift p C S T) (x : Parameter p C T L)
    (G : Over (Spec (.of E.field))) [GrpObj G] (μ : Cocharacter E.field G) :
    HasRelativePosition p C T L x G
      ((μ.app (genericTest p C T L x)).hom
        (MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels.parameterUnit p C T L x)) μ := by
  refine ⟨1, 1, ?_⟩
  simp [positiveMap]

end MathlibExtTest.AlgebraicGeometry.RelativeFFCoefficientNormalizations
