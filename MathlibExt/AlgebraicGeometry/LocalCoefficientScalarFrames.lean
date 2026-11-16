/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings

/-!
# Actual local-field scalar maps on doubly punctured FF charts

The local field is the native uniformizer localization of its actual
valuation ring. Every scalar map is the prescribed localization lift
of the original second Witt tensor factor. Annular denominators invert
both pi and [varpi]; the resulting field coefficients are fixed on
every original integral scalar.
Source: Fargues--Scholze, arXiv:2102.13459v4, Section I.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LocalCoefficientScalarFrames

open _root_.CategoryTheory _root_.Opposite
open LocalWittCoefficientFields RelativeFarguesFontaineRings

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)

/-- The dictionary fixes the actual integral embedding into the original local field. -/
structure IntegerPresentation where
  localization : Localization.Away C.uniformizer ≃+* E.field
  normalized : ∀ a : Integers p E,
    localization (algebraMap (Integers p E) (Localization.Away C.uniformizer) a) = (a : E.field)

variable (F : IntegerPresentation p C) (S : Base p C)

def chartIntegers (P : RationalPresentation p C S) : Integers p E →+* ChartRing p C S P := by
  letI := coefficientAlgebra p C
  exact (chartCoefficient p C S P).comp
    (RelativeWittLoopTests.coefficient p (Residue p E) (Integers p E) (residueTest p C S))

theorem chartIntegers_prime (P : RationalPresentation p C S) :
    IsUnit (chartIntegers p C S P C.uniformizer) :=
  (chartPunctures_unit p C S P).1

/-- The entire E action is the literal localization lift of the native integer factor. -/
def chartScalars (P : RationalPresentation p C S) : E.field →+* ChartRing p C S P :=
  (IsLocalization.Away.lift C.uniformizer (chartIntegers_prime p C S P)).comp
    F.localization.symm.toRingHom

theorem chartScalars_integral (P : RationalPresentation p C S) (a : Integers p E) :
    chartScalars p C F S P (a : E.field) = chartIntegers p C S P a := by
  change IsLocalization.Away.lift C.uniformizer (chartIntegers_prime p C S P)
    (F.localization.symm (a : E.field)) = _
  rw [← F.normalized a, F.localization.symm_apply_apply]
  exact IsLocalization.Away.lift_eq _ _ _

end MathlibExt.AlgebraicGeometry.LocalCoefficientScalarFrames
