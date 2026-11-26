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

/-- Translations compose on the generic abscissa: translating by `T` and then by `S` sends
`genericX W K` to the abscissa of `genericPoint W K + (S + T)`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] (S T : (W⁄K).Point) :
    transEquiv W K S (transEquiv W K T (genericX W K)) =
      (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (S + T)).xc := by
  rw [← AlgEquiv.trans_apply, ← transEquiv_add, transEquiv_genericX]

/-- Translation by `0` is the identity, so by `transEquiv_genericX` the abscissa of
`genericPoint W K + 0` is `genericX W K`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    (genericPoint W K + Point.baseChange K (W⁄K).FunctionField 0).xc = genericX W K := by
  rw [← transEquiv_genericX, transEquiv_zero, AlgEquiv.coe_refl, id_eq]

open Polynomial in
/-- The class of `X - x(P)` lies in the place of `P`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)
    (P : (W⁄K).Point) (hP : P ≠ 0) :
    CoordinateRing.mk (W⁄K) (C (X - C P.xc)) ∈ (placeOf W K P hP).asIdeal := by
  rw [mem_placeOf_iff, CoordinateRing.evalAt_mk, evalEval_C, eval_sub, eval_X, eval_C, sub_self]

open Polynomial in
/-- The class of `X - c` lies in the place of `P` only when `c` is the abscissa of `P`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)
    (P : (W⁄K).Point) (hP : P ≠ 0) (c : K)
    (hc : CoordinateRing.mk (W⁄K) (C (X - C c)) ∈ (placeOf W K P hP).asIdeal) : c = P.xc := by
  rw [mem_placeOf_iff, CoordinateRing.evalAt_mk, evalEval_C, eval_sub, eval_X, eval_C,
    sub_eq_zero] at hc
  exact hc.symm

/-- A place is a proper ideal: the unit `1` is not in it. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)
    (P : (W⁄K).Point) (hP : P ≠ 0) :
    (1 : (W⁄K).CoordinateRing) ∉ (placeOf W K P hP).asIdeal := by
  rw [mem_placeOf_iff, map_one]
  exact one_ne_zero

/-- Congruence is strict: for a valuation on a field, `1` is not congruent to `0`, since
`v (1 - 0) = 1`. A non-strict bound `≤ 1` would make them congruent. -/
example {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) :
    ¬ v.Cong 1 0 := by
  rw [Valuation.cong_iff, sub_zero, map_one]
  exact lt_irrefl 1

/-- Bounded multiplication of congruent elements: if `v t < 1`, then `1 + t` is congruent to `1`,
and so is `(1 + t) * (1 + t)`. -/
example {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) {t : L}
    (ht : v t < 1) : v.Cong ((1 + t) * (1 + t)) 1 := by
  have h : v.Cong (1 + t) 1 := by
    rw [Valuation.cong_iff, add_sub_cancel_left]
    exact ht
  simpa only [mul_one] using h.mul h (map_one v).le (map_one v).le

end FunctionFieldPullbackTest

end
