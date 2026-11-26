/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Basic.Real.Basic
import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

@[expose] public section

open Polynomial

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

-- `exactSource` consumer with the original binders.
example (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv hv x) = x :=
  v.algebraMap_residueInv hv x

example (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt hv f)
      = IsLocalRing.residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) :=
  v.algebraMap_evalAt hv hf

example (f : F) (D : CurveDivisor (Place K F)) (hD : ∀ w ∈ D.support, w.IsRational) :
    CurveDivisor.evalFun f D hD
      = ∏ w ∈ D.support.attach, (w : Place K F).evalAt (hD w w.2) f ^ D w :=
  CurveDivisor.evalFun_def f D hD

example (K F : Type*) [Field K] [Field F] [Algebra K F] :
    Prop :=
  WeilReciprocity K F

-- The statement applies to nonzero functions whose principal divisors have disjoint
-- supports of rational places.
example (h : WeilReciprocity K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    {Df Dg : CurveDivisor (Place K F)} (hDf : ∀ w : Place K F, Df w = w.ord f)
    (hDg : ∀ w : Place K F, Dg w = w.ord g)
    (hdisj : ∀ w : Place K F, w.ord f = 0 ∨ w.ord g = 0)
    (hrf : ∀ w ∈ Df.support, w.IsRational) (hrg : ∀ w ∈ Dg.support, w.IsRational) :
    CurveDivisor.evalFun f Dg hrg = CurveDivisor.evalFun g Df hrf :=
  h f g Df Dg hf hg hDf hDg hdisj hrf hrg

-- K-valued evaluation takes a rationality proof.
example (hv : v.IsRational) (f : F) : v.evalAt hv f = v.evalAt hv f := by
  fail_if_success have := v.evalAt f
  rfl

-- At a rational place the value is the element `a` of `K` with `f - a` in the
-- maximal ideal, so it involves no choice.
example (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt hv f) :=
  (v.hasValueAt_iff_residue hf _).mpr (v.algebraMap_evalAt hv hf).symm

example (hv : v.IsRational) {f : F} {a : K} (ha : v.HasValueAt f a) :
    v.evalAt hv f = a :=
  v.hasValueAt_unique ((v.hasValueAt_iff_residue (v.mem_of_hasValueAt ha) _).mpr
    (v.algebraMap_evalAt hv _).symm) ha

-- Constants evaluate to themselves.
example (hv : v.IsRational) (a : K) : v.evalAt hv (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem hv (v.algebraMap_mem a)]
  exact v.residueInv_algebraMap hv a

-- Boundary: evaluation at `1` is `1`, and an element outside the valuation
-- subring evaluates to `0` by definition.
example (hv : v.IsRational) : v.evalAt hv (1 : F) = 1 := v.evalAt_one hv

example (hv : v.IsRational) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.evalAt hv f = 0 := by
  rw [Place.evalAt, dite_eq_right hf]

-- Divisor evaluation: the empty divisor and a one-place divisor.
example (f : F) : CurveDivisor.evalFun f (0 : CurveDivisor (Place K F)) (by simp) = 1 := by
  simp

example (hv : v.IsRational) (f : F) (n : ℤ)
    (hD : ∀ w ∈ (Finsupp.single v n).support, w.IsRational) :
    CurveDivisor.evalFun f (Finsupp.single v n) hD = v.evalAt hv f ^ n :=
  CurveDivisor.evalFun_single f v hv n hD

example (hv : v.IsRational) (f : F)
    (hD : ∀ w ∈ (Finsupp.single v (-1 : ℤ)).support, w.IsRational) :
    CurveDivisor.evalFun f (Finsupp.single v (-1 : ℤ)) hD = (v.evalAt hv f)⁻¹ := by
  rw [CurveDivisor.evalFun_single f v hv, zpow_neg_one]

-- `evalFun f` is not multiplicative in the divisor at a place where `f` has the value `0`:
-- `[v]` and `-[v]` both give `0`, while their sum gives `1`.
example (hv : v.IsRational) {f : F} (hf0 : v.evalAt hv f = 0) :
    CurveDivisor.evalFun f (Finsupp.single v 1) (by simp [hv]) = 0 ∧
      CurveDivisor.evalFun f (Finsupp.single v (-1)) (by simp [hv]) = 0 ∧
      CurveDivisor.evalFun f (Finsupp.single v 1 + Finsupp.single v (-1))
        (by rw [← Finsupp.single_add]; simp) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [CurveDivisor.evalFun_single f v hv, hf0, zpow_one]
  · rw [CurveDivisor.evalFun_single f v hv, hf0, zpow_neg_one, inv_zero]
  · have h0 : ∀ (D : CurveDivisor (Place K F)) (hD : ∀ w ∈ D.support, w.IsRational),
        D = 0 → CurveDivisor.evalFun f D hD = 1 := by
      rintro D hD rfl
      exact CurveDivisor.evalFun_zero f hD
    exact h0 _ _ (by rw [← Finsupp.single_add]; simp)

-- At a rational place, `residueEquiv` is the map from `K` and `residueInv` its inverse.
example (hv : v.IsRational) (a : K) :
    v.residueEquiv hv a = algebraMap K v.ResidueField a := by
  simp

example (hv : v.IsRational) (x : v.ResidueField) :
    (v.residueEquiv hv).symm x = v.residueInv hv x :=
  rfl

-- On the valuation subring, evaluation is additive and multiplicative, so elements of `K`
-- factor out.
example (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt hv (f * g + f) = v.evalAt hv f * v.evalAt hv g + v.evalAt hv f := by
  rw [v.evalAt_add hv (mul_mem hf hg) hf, v.evalAt_mul hv hf hg]

example (hv : v.IsRational) (a : K) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt hv (algebraMap K F a * f) = a * v.evalAt hv f := by
  have ha : v.evalAt hv (algebraMap K F a) = a := by
    rw [v.evalAt_of_mem hv (v.algebraMap_mem a)]
    exact v.residueInv_algebraMap hv a
  rw [v.evalAt_mul hv (v.algebraMap_mem a) hf, ha]

-- Rational means degree one, so the degree-one results apply: every place of a curve over
-- an algebraically closed field is rational.
example [IsAlgClosed K] [IsCurveOver K F] : v.IsRational :=
  v.isRational_iff_deg_eq_one.mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

-- Concrete places of rational function fields: the place at a point is rational, while the
-- place of `ℝ(X)` at `X ^ 2 + 1` has degree two and is not.
example (a : K) : (RationalFunctionField.placeOfPoint K a).IsRational :=
  (Place.isRational_iff_deg_eq_one _).mpr (RationalFunctionField.deg_placeOfPoint K a)

private theorem natDegree_X_sq_add_one_real : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by
  compute_degree!

private theorem irreducible_X_sq_add_one_real : Irreducible (X ^ 2 + 1 : ℝ[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => ?_
  · rw [natDegree_X_sq_add_one_real, Finset.mem_Icc]
    omega
  · rw [IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at hx
    nlinarith [sq_nonneg x]

example : ¬ (RationalFunctionField.finitePlace ℝ irreducible_X_sq_add_one_real).IsRational := by
  rw [Place.isRational_iff_deg_eq_one, RationalFunctionField.deg_finitePlace,
    natDegree_X_sq_add_one_real]
  decide

end AlgebraicCurve
