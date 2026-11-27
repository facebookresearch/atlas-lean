/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
public import MathlibExt.AlgebraicGeometry.Curve.SeparatingTranscendental

/-! # Tests for function fields of curves -/

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

-- A curve function field has principal divisors, finite residue fields and a rank-one module of
-- Kähler differentials.
example : HasPrincipalDivisors K F := inferInstance

example (v : Place K F) : Module.Finite K v.ResidueField := inferInstance

example (v : Place K F) : Module.Finite K v.ResidueField := IsCurveOver.finiteResidueField v

-- The finiteness instance feeds Mathlib's `Module.Finite` API directly.
example (v : Place K F) : 0 < Module.finrank K v.ResidueField := Module.finrank_pos

example (v : Place K F) : 1 ≤ v.deg := IsCurveOver.one_le_deg v

example : Module.Free F Ω[F⁄K] := inferInstance

example : Module.finrank F Ω[F⁄K] = 1 := IsCurveOver.finrank_kaehler

example : Nontrivial Ω[F⁄K] := inferInstance

-- Over an algebraically closed field every place has degree one.
example [IsAlgClosed K] (v : Place K F) : v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed v

-- Principal divisors have degree zero.
example {f : F} (hf : f ≠ 0) :
    ∃ D : Divisor K F, (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0 :=
  HasPrincipalDivisors.exists_divisor f hf

-- The rank-one Kähler condition alone rules out a separable algebraic extension.
example : ¬ Algebra.IsSeparable K F := IsCurveOver.not_isSeparable

-- Over a perfect field, instance search finds `Algebra.Transcendental K F`, which feeds Mathlib's
-- lemmas for transcendental extensions.
example [PerfectField K] : Algebra.Transcendental K F := inferInstance

example [PerfectField K] : 0 < Algebra.trdeg K F := trdeg_pos K F

end AlgebraicCurve

open IntermediateField KaehlerDifferential

-- `exactSource` consumer: the statement with the original binders.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧
      Algebra.IsSeparable K⟮t⟯ F :=
  AlgebraicCurve.IsCurveOver.exists_separating_transcendental

-- Higher-universe consumer.
example {K : Type 1} {F : Type 2} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧
      Algebra.IsSeparable K⟮t⟯ F :=
  AlgebraicCurve.IsCurveOver.exists_separating_transcendental

-- A curve function field over a perfect field, essentially of finite type, has transcendence
-- degree one.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] :
    Algebra.trdeg K F = 1 :=
  AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField

example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) :
    Module.Finite K v.ResidueField ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨inferInstance, AlgebraicCurve.IsCurveOver.finrank_kaehler⟩
