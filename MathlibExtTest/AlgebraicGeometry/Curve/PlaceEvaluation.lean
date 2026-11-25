/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation

@[expose] public section

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

-- The statement applies to principal divisors whose supports are rational.
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

-- At a rational place the value is the constant `a` with `f - a` in the
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

end AlgebraicCurve
