/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.FunctionFieldPullback

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace FunctionFieldPullbackTest

/-- Consumer with the source binders for the translation-equivariance
nondegeneracy theorem: `g` has a simple zero at every affine point over `T`. -/
private theorem exactSource {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0)
      (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ),
      (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
        WithZero.exp (-(k : ℤ)) →
      (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n hgood h) ≤
        WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp (-1) else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → transEquiv W K S g = g) :
    T = 0 :=
  WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq W hnK hpull g hg hinv

/-- Consumer for the pole form: `g` has a simple pole at every affine point
over `T`. -/
private theorem exactSourcePole {F K : Type*} [Field F] [Field K] [Algebra F K]
    [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0)
      (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ),
      (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
        WithZero.exp (-(k : ℤ)) →
      (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n hgood h) ≤
        WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp 1 else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → transEquiv W K S g = g) :
    T = 0 :=
  WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq_of_pole W hnK hpull g hg hinv

/-- Boundary check: multiplication by `0` sends the generic point to `0`, so
`MulGood W K 0` fails and `mulPull W K 0` cannot be applied. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] : ¬ MulGood W K 0 :=
  fun h => h.1 (zero_zsmul _)

/-- For `n` nonzero in `K`, `zsmul_genericPoint_good` supplies the hypothesis
of `mulPull`, which sends the generic abscissa to the abscissa of
`n • genericPoint W K`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) :
    mulPull W K n (zsmul_genericPoint_good W K hn) (genericX W K) =
      (n • genericPoint W K).xc :=
  mulPull_genericX' W K _

end FunctionFieldPullbackTest

end
