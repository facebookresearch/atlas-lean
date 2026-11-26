/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOverOfTranscendental
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.Kaehler.Basic
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors

/-! # Tests for curve function fields obtained from a transcendental element -/

@[expose] public section

namespace AlgebraicCurve

-- `exactSource` consumer with the original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.IsCurveOver K F :=
  isCurveOver_of_transcendental_of_perfectField htr hfd

-- The separable variant, with its original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F :=
  isCurveOver_of_transcendental htr hfd hsep

-- A finite separable extension of `RatFunc K` has principal divisors of degree zero.
example {K : Type*} [Field K] (E : Type*) [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E :=
  hasPrincipalDivisors_of_finiteDimensional_of_isSeparable K E

-- Boundary: transcendence matters. `K` is finite over `K⟮1⟯`, but its Kähler differentials over
-- `K` vanish, so `K` is not the function field of a curve over `K`.
example (K : Type*) [Field K] : ¬ IsCurveOver K K := by
  intro h
  have h1 := h.kaehler_free_rank_one.2
  have : Subsingleton Ω[K⁄K] :=
    KaehlerDifferential.subsingleton_of_surjective K K Function.surjective_id
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

-- Positive instance: the hypotheses hold for `x = X` in `RatFunc K`, since `K⟮X⟯ = ⊤`.
example (K : Type*) [Field K] : IsCurveOver K (RatFunc K) := by
  have htop : IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)) = ⊤ := RatFunc.adjoin_X
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Algebra.IsSeparable.of_equiv_equiv IntermediateField.topEquiv.symm.toRingEquiv
      (RingEquiv.refl (RatFunc K)) (RingHom.ext fun _ => rfl)
  exact isCurveOver_of_transcendental RatFunc.transcendental_X hfd hsep

-- Positive instance of the perfect-field version: no separability hypothesis is needed.
example (K : Type*) [Field K] [PerfectField K] : IsCurveOver K (RatFunc K) := by
  have htop : IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)) = ⊤ := RatFunc.adjoin_X
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    rw [htop]
    exact Module.finite_of_finrank_eq_succ IntermediateField.finrank_top
  exact isCurveOver_of_transcendental_of_perfectField RatFunc.transcendental_X hfd

-- Consumer of `Place.finite_residueField_restrict`: in any finite extension `E` of `RatFunc K`,
-- separable or not, every residue field is finite over `K`.
example {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra (RatFunc K) E]
    [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E] (w : Place K E) :
    Module.Finite K w.ResidueField := by
  have := RationalFunctionField.finite_residueField (w.restrict (RatFunc K))
  have := Place.finite_residueField_restrict (F := RatFunc K) w
  exact Module.Finite.trans (w.restrict (RatFunc K)).ResidueField w.ResidueField

-- Universe check: the base field and the function field may live in different universes.
universe u v in
example {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    IsCurveOver K F :=
  isCurveOver_of_transcendental_of_perfectField htr hfd

end AlgebraicCurve
