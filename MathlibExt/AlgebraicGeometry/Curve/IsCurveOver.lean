/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_IsCurveOver.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

/-!
# Function fields of curves

`IsCurveOver K F`, defined in `MathlibExt.AlgebraicGeometry.Curve.LPolynomial`, says that every
nonzero element of `F` has a degree-zero principal divisor, residue fields of places are finite
over `K`, and the Kähler differentials of `F / K` are free of rank one. This file derives the
instances `HasPrincipalDivisors K F`, `Module.Finite K v.ResidueField` and the Kähler instances from
it, and shows that every place has degree one over an algebraically closed field.
-/

@[expose] public section

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver

variable {K F}

instance (priority := 100) toHasPrincipalDivisors [IsCurveOver K F] :
    HasPrincipalDivisors K F :=
  ⟨IsCurveOver.exists_divisor⟩

theorem hasPrincipalDivisors [IsCurveOver K F] : HasPrincipalDivisors K F :=
  inferInstance

instance instFiniteResidueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  IsCurveOver.finiteResidue v

instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=
  h.kaehler_free_rank_one.1

theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=
  h.kaehler_free_rank_one.2

instance instNontrivialKaehler [IsCurveOver K F] : Nontrivial Ω[F⁄K] :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) finrank_kaehler

end IsCurveOver

namespace Place

variable {K F}

theorem deg_eq_one_of_isAlgClosed_of_finite [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  change Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace IsCurveOver

variable {K F}

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.deg = 1 :=
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  v.deg_eq_one_of_isAlgClosed_of_finite

theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :
    ∀ w : Place K F, w.deg = 1 :=
  deg_eq_one_of_isAlgClosed

end IsCurveOver

end AlgebraicCurve
