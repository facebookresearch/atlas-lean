/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PointDifference

@[expose] public section

namespace AlgebraicCurve.PointDifferenceTest

open AlgebraicCurve

-- The divisor `P - Q` is defined on any type of points; for distinct points it has coefficient
-- `1` at `P` and is nonzero, and it vanishes when the points coincide.
example {C : Type*} (P Q : C) (h : P ≠ Q) :
    CurveDivisor.coeff (CurveDivisor.pointDiff P Q) P = 1 ∧ CurveDivisor.pointDiff P Q ≠ 0 :=
  ⟨CurveDivisor.coeff_pointDiff_left P Q h, CurveDivisor.pointDiff_ne_zero P Q h⟩

example {C : Type 1} (P : C) : CurveDivisor.pointDiff P P = 0 :=
  CurveDivisor.pointDiff_self P

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- The degree of a place with a finite-dimensional residue field is that dimension, and it is
-- positive.
example (v : Place K F) [Module.Finite K v.ResidueField] :
    v.deg = Module.finrank K v.ResidueField ∧ 0 < v.deg :=
  ⟨rfl, v.deg_pos⟩

-- Every place of a curve has finite-dimensional residue field, so positive degree.
example [IsCurveOver K F] (v : Place K F) : 0 < v.deg := by
  have := IsCurveOver.finiteResidue v
  exact v.deg_pos

-- Boundary: a single place with finite-dimensional residue field has positive degree, so a
-- nonzero effective divisor supported there is not of degree zero.
example (v : Place K F) [Module.Finite K v.ResidueField] :
    Finsupp.single v 1 ∉ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, Divisor.degree_single, one_mul]
  exact_mod_cast v.deg_pos.ne'

-- The divisor `P - Q` of two places has degree `deg P - deg Q`, so it has degree zero exactly
-- when the two places have the same degree.
example (P Q : Place K F) :
    Divisor.degree (CurveDivisor.pointDiff P Q) = (P.deg : ℤ) - Q.deg ∧
      (CurveDivisor.pointDiff P Q ∈ Divisor.degZero (K := K) (F := F) ↔ P.deg = Q.deg) :=
  ⟨Divisor.degree_pointDiff P Q, Divisor.pointDiff_mem_degZero_iff P Q⟩

-- A divisor of degree zero has class zero exactly when it is the divisor of a nonzero element.
example (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (D : Divisor K F) v = v.ord f :=
  Pic0.mk_eq_zero_iff D

-- Two divisors of degree zero have the same class when they differ by a principal divisor.
example (D E : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((D : Divisor K F) - (E : Divisor K F))) : Pic0.mk D = Pic0.mk E :=
  sub_eq_zero.mp ((Pic0.mk_eq_zero_iff (D - E)).mpr h)

-- The zero divisor has class zero.
example : Pic0.mk (0 : Divisor.degZero (K := K) (F := F)) = 0 :=
  Pic0.mk_zero

-- The class of `P - Q` for two places of the same degree vanishes exactly when `P - Q` is the
-- divisor of a nonzero element.
example (P Q : Place K F) (h : P.deg = Q.deg) :
    Pic0.mk ⟨CurveDivisor.pointDiff P Q, (Divisor.pointDiff_mem_degZero_iff P Q).mpr h⟩ = 0 ↔
      ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, CurveDivisor.pointDiff P Q v = v.ord f :=
  Pic0.mk_eq_zero_iff _

-- A function whose divisor is `P - Q` makes the class of `P - Q` vanish.
example (P Q : Place K F) (h : P.deg = Q.deg) (f : F) (hf : f ≠ 0)
    (hdiv : ∀ v : Place K F, CurveDivisor.pointDiff P Q v = v.ord f) :
    Pic0.mk ⟨CurveDivisor.pointDiff P Q, (Divisor.pointDiff_mem_degZero_iff P Q).mpr h⟩ = 0 :=
  (Pic0.mk_eq_zero_iff _).mpr ⟨f, hf, hdiv⟩

-- Boundary: when the two places coincide, `P - P = 0` and its class vanishes.
example (P : Place K F) :
    Pic0.mk ⟨CurveDivisor.pointDiff P P, (Divisor.pointDiff_mem_degZero_iff P P).mpr rfl⟩ = 0 :=
  (Pic0.mk_eq_zero_iff _).mpr ⟨1, one_ne_zero, fun v => by simp [CurveDivisor.pointDiff_self]⟩

end AlgebraicCurve.PointDifferenceTest
