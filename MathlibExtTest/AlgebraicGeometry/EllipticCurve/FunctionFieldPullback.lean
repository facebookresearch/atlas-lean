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

/-- Consumer with the original binders for the translation-equivariance
nondegeneracy theorem. -/
theorem exactSource {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0)
      (h : (W⁄K).FunctionField) (k : ℕ),
      (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
        WithZero.exp (-(k : ℤ)) →
      (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n h) ≤
        WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp (-1) else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → transEquiv W K S g = g) :
    T = 0 :=
  WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq W hnK hpull g hg hinv

/-- Consumer with the original binders for the torsion cardinality theorem. -/
theorem exactSourceCard {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed W hn

/-- Boundary check: the `n = 1` torsion subgroup has cardinality `1`, so the
exponent in the cardinality formula is genuinely quadratic. -/
example {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] (hn : (1 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 1) = 1 := by
  have h := WeierstrassCurve.card_torsion_of_isAlgClosed W (n := 1)
    (by exact_mod_cast hn)
  simpa using h

end FunctionFieldPullbackTest

end
