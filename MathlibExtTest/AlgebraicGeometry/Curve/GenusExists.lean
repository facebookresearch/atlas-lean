/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.GenusExists
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncGenusExists
public import MathlibExt.AlgebraicGeometry.Curve.SeparatingTranscendental

/-! # Tests for the existence of the genus of a curve function field -/

@[expose] public section

namespace AlgebraicCurve

open IntermediateField

-- `exactSource` consumer with the original binders.
example {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_isCurveOver hC

-- The prerequisites, with their original binders.
example (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  RationalFunctionField.stichtenothGenusExists K F hC

example {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F :=
  IsCurveOver.exists_separating_transcendental

-- Consequences: such a field has a place, and `deg D - ℓ(D)` is bounded above.
example {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    Nonempty (Place K F) :=
  (stichtenothGenusExists_of_isCurveOver hC).1

example {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1 := by
  obtain ⟨-, -, γ, D₀, h⟩ := stichtenothGenusExists_of_isCurveOver hC
  exact ⟨γ, h.isMax⟩

-- Universe check: the base field and the function field may live in different universes.
universe u v in
example {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_isCurveOver hC

end AlgebraicCurve
