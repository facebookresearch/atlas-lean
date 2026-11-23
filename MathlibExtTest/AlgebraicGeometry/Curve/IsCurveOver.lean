/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver

@[expose] public section

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

-- The Kähler-rank hypothesis matters: for an algebraic extension the
-- conclusion would give a transcendental element, which cannot exist.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] :
    Algebra.trdeg K F = 1 :=
  AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField

example {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) :
    Module.Finite K v.ResidueField ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨AlgebraicCurve.IsCurveOver.finite_residueField v,
    AlgebraicCurve.IsCurveOver.finrank_kaehler⟩
