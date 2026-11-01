/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinSequence
import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/

@[expose] public section

open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

private def cubic (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

private lemma cubic_ne_zero (W : WeierstrassCurve F) : cubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff 3) h
  simp [cubic] at hcoeff

private lemma cubic_monic (W : WeierstrassCurve F) : (cubic W).Monic := by
  unfold cubic
  monicity <;> norm_num

private lemma cubic_natDegree (W : WeierstrassCurve F) : (cubic W).natDegree = 3 := by
  unfold cubic
  compute_degree <;> norm_num

private lemma cubic_degree (W : WeierstrassCurve F) : (cubic W).degree = 3 := by
  rw [degree_eq_natDegree (cubic_ne_zero W), cubic_natDegree]
  norm_num

private lemma cubic_discr (W : WeierstrassCurve F) :
    (cubic W).discr =
      W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ -
        27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three (cubic_degree W)]
  norm_num [cubic]

private def duplicationNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 - C (2 * W.a₄) * X ^ 2 - C (8 * W.a₆) * X +
    C (W.a₄ ^ 2 - 4 * W.a₂ * W.a₆)

private lemma duplicationNumerator_eq (W : WeierstrassCurve F) :
    duplicationNumerator W =
      (cubic W).derivative ^ 2 -
        C 4 * (C W.a₂ + C 2 * X) * cubic W := by
  simp only [duplicationNumerator, cubic, derivative_add, derivative_pow,
    derivative_X, derivative_C, derivative_mul, map_ofNat]
  simp only [C_eq_natCast, C_ofNat, map_mul, map_sub, map_pow]
  ring

private lemma delta_eq_sixteen_mul_cubic_discr
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    W.Δ = 16 * (cubic W).discr := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, cubic_discr]
  ring

private lemma cubic_discr_ne_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).discr ≠ 0 := by
  intro h
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  apply hΔ
  rw [delta_eq_sixteen_mul_cubic_discr, h, mul_zero]

private lemma cubic_separable (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).Separable := by
  rw [Polynomial.separable_def]
  have hdegDeriv : (cubic W).derivative.natDegree ≤ 2 := by
    simpa [cubic_natDegree] using Polynomial.natDegree_derivative_le (cubic W)
  have hres :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 =
        -(cubic W).discr := by
    have h := Polynomial.resultant_deriv (f := cubic W) (by
      rw [cubic_degree]
      norm_num)
    rw [cubic_natDegree] at h
    norm_num [cubic_monic W] at h
    exact h
  have hresne :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 ≠ 0 := by
    rw [hres]
    exact neg_ne_zero.mpr (cubic_discr_ne_zero W)
  obtain ⟨p, q, _, _, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (cubic W) (cubic W).derivative (m := 3) (n := 2)
        (cubic_natDegree W).le hdegDeriv (by omega)
  refine ⟨C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p,
    C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q, ?_⟩
  calc
    (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p) *
          cubic W +
        (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q) *
          (cubic W).derivative =
        C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ *
          (cubic W * p + (cubic W).derivative * q) := by ring
    _ = 1 := by rw [hpq, ← map_mul, inv_mul_cancel₀ hresne, map_one]

private lemma isCoprime_cubic_duplicationNumerator
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    IsCoprime (cubic W) (duplicationNumerator W) := by
  have hc : IsCoprime (cubic W) ((cubic W).derivative ^ 2) :=
    ((Polynomial.separable_def (cubic W)).mp (cubic_separable W)).pow_right
  obtain ⟨u, v, huv⟩ := hc
  let k : F[X] := C 4 * (C W.a₂ + C 2 * X)
  refine ⟨u + v * k, v, ?_⟩
  rw [duplicationNumerator_eq]
  change (u + v * k) * cubic W +
    v * ((cubic W).derivative ^ 2 - k * cubic W) = 1
  calc
    (u + v * k) * cubic W +
        v * ((cubic W).derivative ^ 2 - k * cubic W) =
      u * cubic W + v * (cubic W).derivative ^ 2 := by ring
    _ = 1 := huv

private lemma product_formula {R : Type*} [CommRing R]
    (a b c t f g : R) :
    let cubicAtT := t ^ 3 + a * t ^ 2 + b * t + c
    let common :=
      (t * g + f) * (b * g + t * f) + 2 * g * (a * t * f + c * g)
    common ^ 2 -
        4 * cubicAtT * g * (f ^ 3 + a * f ^ 2 * g + b * f * g ^ 2 + c * g ^ 3) =
      (t * g - f) ^ 2 *
        ((t * f - b * g) ^ 2 - 4 * c * g * ((t + a) * g + f)) := by
  dsimp only
  ring

private def cubicRat (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (cubic W)

private lemma cubicRat_ne_zero (W : WeierstrassCurve F) : cubicRat W ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (cubic_ne_zero W)

private lemma cubicRat_eq (W : WeierstrassCurve F) :
    cubicRat W = RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆ := by
  simp [cubicRat, cubic, RatFunc.algebraMap_X]

private lemma intDegree_cubicRat (W : WeierstrassCurve F) :
    (cubicRat W).intDegree = 3 := by
  rw [cubicRat, RatFunc.intDegree_polynomial, cubic_natDegree]
  norm_num

private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
    (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

private lemma intDegree_add_sub_le_of_le {x y z : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m)
    (hz : z.intDegree ≤ m) : (x + y - z).intDegree ≤ m := by
  rw [sub_eq_add_neg]
  apply intDegree_add_le_of_le (x := x + y) (y := -z) hm
  · exact intDegree_add_le_of_le (x := x) (y := y) hm hx hy
  · rw [RatFunc.intDegree_neg]
    exact hz

private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
    (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
    (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

private def twist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, RatFunc.C W.a₂ * cubicRat W, 0, RatFunc.C W.a₄ * cubicRat W ^ 2,
    RatFunc.C W.a₆ * cubicRat W ^ 3⟩

private instance (W : WeierstrassCurve F) : (twist W).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

private lemma twist_discriminant (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).Δ = cubicRat W ^ 6 * RatFunc.C W.Δ := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF,
    WeierstrassCurve.Δ_of_isCharNeTwoNF]
  simp only [twist, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

private instance (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, twist_discriminant, isUnit_iff_ne_zero]
  apply mul_ne_zero (pow_ne_zero 6 (cubicRat_ne_zero W))
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  simpa using RatFunc.C_injective.ne hΔ

private lemma q_equation (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist]
  rw [cubicRat_eq]
  ring

private def Q (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (q_equation W)

private lemma card_odd [Finite F] (hchar : ringChar F ≠ 2) : Odd (Nat.card F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  obtain ⟨p, hpF, n, hp, hcard⟩ := @FiniteField.card' F _ fintypeF
  let _ : CharP F p := hpF
  have hpne : p ≠ 2 := by
    intro h
    apply hchar
    rw [ringChar.eq F p, h]
  rw [hcard]
  exact hp.odd_of_ne_two hpne |>.pow

private lemma twice_half_card_add_three [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 3) / 2) = Nat.card F + 3 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma aeval_cubic_X_pow_card [Finite F] (W : WeierstrassCurve F) :
    aeval (RatFunc.X ^ Nat.card F) (cubic W) = cubicRat W ^ Nat.card F := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  calc
    aeval (RatFunc.X ^ Fintype.card F) (cubic W) =
        aeval RatFunc.X (Polynomial.expand F (Fintype.card F) (cubic W)) := by
      rw [Polynomial.expand_aeval]
    _ = aeval RatFunc.X (cubic W ^ Fintype.card F) := by
      rw [FiniteField.Polynomial.expand_card]
    _ = cubicRat W ^ Fintype.card F := by
      simp [cubicRat, RatFunc.aeval_X_left_eq_algebraMap]

private def pZeroX [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W * RatFunc.X ^ Nat.card F

private def pZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W ^ ((Nat.card F + 3) / 2)

private lemma pZero_equation [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation (pZeroX W) (pZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist, pZeroX, pZeroY]
  have hcubic := aeval_cubic_X_pow_card W
  simp only [cubic, map_add, map_mul, map_pow, aeval_X, aeval_C] at hcubic
  rw [← pow_mul]
  rw [show (Nat.card F + 3) / 2 * 2 = Nat.card F + 3 by
    rw [mul_comm, twice_half_card_add_three hchar]]
  simp only [zero_mul, add_zero]
  calc
    cubicRat W ^ (Nat.card F + 3) =
        cubicRat W ^ 3 * cubicRat W ^ Nat.card F := by
      rw [pow_add]
      ring
    _ = cubicRat W ^ 3 *
        ((RatFunc.X ^ Nat.card F) ^ 3 +
          algebraMap F (RatFunc F) W.a₂ * (RatFunc.X ^ Nat.card F) ^ 2 +
          algebraMap F (RatFunc F) W.a₄ * RatFunc.X ^ Nat.card F +
          algebraMap F (RatFunc F) W.a₆) := by
      rw [← hcubic]
    _ = _ := by
      simp only [RatFunc.algebraMap_eq_C]
      ring

private def P₀ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (pZero_equation hchar W)

private local instance : DecidableEq F := Classical.decEq F

private def point [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    (twist W).toAffine.Point :=
  P₀ hchar W + n • Q W

private def paperX (W : WeierstrassCurve F) (x : RatFunc F) : RatFunc F :=
  x / cubicRat W

private def paperY (W : WeierstrassCurve F) (y : RatFunc F) : RatFunc F :=
  y / cubicRat W ^ 2

private def badAtInfinity (W : WeierstrassCurve F) :
    (twist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (paperX W x).intDegree ≤ 0

private lemma paper_coordinates_equation (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y) :
    cubicRat W * paperY W y ^ 2 =
      paperX W x ^ 3 + RatFunc.C W.a₂ * paperX W x ^ 2 +
        RatFunc.C W.a₄ * paperX W x + RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [twist] at heq
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W]
  linear_combination heq

private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0) (n : ℕ) :
    (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

private lemma intDegree_cubic_paperX_le_zero (W : WeierstrassCurve F)
    {x : RatFunc F} (hx : x.intDegree ≤ 0) :
    (x ^ 3 + RatFunc.C W.a₂ * x ^ 2 + RatFunc.C W.a₄ * x +
      RatFunc.C W.a₆).intDegree ≤ 0 := by
  have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hx2 : (x ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have ha2 : (RatFunc.C W.a₂ * x ^ 2).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₂) (y := x ^ 2)
      (m := 0) (n := 0) (by norm_num) (by simp) hx2
  have ha4 : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
      (m := 0) (n := 0) (by norm_num) (by simp) hx
  have h₁ := intDegree_add_le_of_le (m := 0) (by norm_num) hx3 ha2
  have h₂ := intDegree_add_le_of_le (m := 0) (by norm_num) h₁ ha4
  exact intDegree_add_le_of_le (m := 0) (by norm_num) h₂ (by simp)

private lemma intDegree_cubicRat_mul_paperY_le_one
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : (paperX W x).intDegree ≤ 0) :
    (cubicRat W * paperY W y).intDegree ≤ 1 := by
  let r := paperX W x
  let s := paperY W y
  change (cubicRat W * s).intDegree ≤ 1
  by_cases hs0 : s = 0
  · simp [s, hs0]
  have hA : cubicRat W ≠ 0 := cubicRat_ne_zero W
  have hAs : cubicRat W * s ≠ 0 := mul_ne_zero hA hs0
  have heq := paper_coordinates_equation W hxy
  change cubicRat W * s ^ 2 =
    r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r + RatFunc.C W.a₆ at heq
  have hr : r.intDegree ≤ 0 := hx
  have hcubic := intDegree_cubic_paperX_le_zero W hr
  have hproduct :
      (cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆)).intDegree ≤ 3 := by
    have := intDegree_mul_le_of_le (x := cubicRat W)
      (y := r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) (m := 3) (n := 0) (by norm_num)
      (by rw [intDegree_cubicRat]) hcubic
    norm_num at this ⊢
    exact this
  have hsquare : (cubicRat W * s) ^ 2 =
      cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  rw [← hsquare, intDegree_pow hAs] at hproduct
  norm_num at hproduct ⊢
  omega

private lemma paperX_Q_coordinate (W : WeierstrassCurve F) :
    paperX W (cubicRat W * RatFunc.X) = RatFunc.X := by
  unfold paperX
  field_simp [cubicRat_ne_zero W]

private lemma paperX_addX_Q_eq (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      cubicRat W *
          ((paperY W y - 1) / (paperX W x - RatFunc.X)) ^ 2 -
        RatFunc.C W.a₂ - paperX W x - RatFunc.X := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, twist]
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W, hx]
  ring

private lemma paperX_addX_Q_canceled (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      ((RatFunc.X + paperX W x) *
          (RatFunc.C W.a₄ + RatFunc.X * paperX W x) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * paperX W x + RatFunc.C W.a₆) -
        2 * cubicRat W * paperY W y) /
      (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_eq W hx]
  have heq := paper_coordinates_equation W hxy
  have hden : paperX W x - RatFunc.X ≠ 0 := by
    intro h
    apply hx
    have hpaper : paperX W x = RatFunc.X := sub_eq_zero.mp h
    unfold paperX at hpaper
    calc
      x = RatFunc.X * cubicRat W := (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
      _ = cubicRat W * RatFunc.X := mul_comm _ _
  rw [cubicRat_eq W] at heq ⊢
  field_simp [hden, sub_ne_zero.mpr (Ne.symm <| sub_ne_zero.mp hden)]
  linear_combination (paperX W x - RatFunc.X) ^ 2 * heq

set_option maxHeartbeats 500000 in
-- The expanded three-term rational-function bound needs extra elaboration budget.
private lemma intDegree_canceled_numerator_le_two
    (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
    (hAs : (A * s).intDegree ≤ 1) :
    ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) -
      2 * A * s).intDegree ≤ 2 := by
  have hXr : (RatFunc.X * r).intDegree ≤ 1 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) (by simp) hr
  have hXadd : (RatFunc.X + r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) (hr.trans (by norm_num))
  have hbXr : (RatFunc.C b + RatFunc.X * r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) hXr
  have hfirst :
      ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r)).intDegree ≤ 2 := by
    simpa using intDegree_mul_le_of_le
      (x := RatFunc.X + r) (y := RatFunc.C b + RatFunc.X * r)
      (m := 1) (n := 1) (by norm_num) hXadd hbXr
  have haXr : (RatFunc.C a * RatFunc.X * r).intDegree ≤ 1 := by
    have haX : (RatFunc.C a * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C a) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    simpa [mul_assoc] using intDegree_mul_le_of_le
      (x := RatFunc.C a * RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) haX hr
  have hmiddleInside :
      (RatFunc.C a * RatFunc.X * r + RatFunc.C c).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) haXr (by simp)
  have hmiddle :
      (2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c)).intDegree ≤ 1 := by
    rw [show 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) =
      (RatFunc.C a * RatFunc.X * r + RatFunc.C c) +
        (RatFunc.C a * RatFunc.X * r + RatFunc.C c) by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hmiddleInside hmiddleInside
  have hlast : (2 * A * s).intDegree ≤ 1 := by
    rw [show 2 * A * s = A * s + A * s by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hAs hAs
  exact intDegree_add_sub_le_of_le
    (x := (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r))
    (y := 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c))
    (z := 2 * A * s) (m := 2) (by norm_num) hfirst
      (hmiddle.trans (by norm_num)) (hlast.trans (by norm_num))

private lemma intDegree_X_sub_eq_one {r : RatFunc F} (hr : r.intDegree ≤ 0) :
    (RatFunc.X - r).intDegree = 1 := by
  have hneg : (-r).intDegree ≤ 1 := by
    rw [RatFunc.intDegree_neg]
    exact hr.trans (by norm_num)
  have hdiffLe : (RatFunc.X - r).intDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    exact intDegree_add_le_of_le (x := RatFunc.X) (y := -r)
      (m := 1) (by norm_num) (by simp) hneg
  have hdiffNotLe : ¬(RatFunc.X - r).intDegree ≤ 0 := by
    intro hdiff
    have hbad : (RatFunc.X : RatFunc F).intDegree ≤ 0 := by
      rw [show (RatFunc.X : RatFunc F) = (RatFunc.X - r) + r by ring]
      exact intDegree_add_le_of_le (x := RatFunc.X - r) (y := r)
        (m := 0) (by norm_num) hdiff hr
    norm_num at hbad
  omega

private lemma intDegree_canceled_expression_le_zero
    (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
    (hAs : (A * s).intDegree ≤ 1) :
    (((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s) /
      (RatFunc.X - r) ^ 2).intDegree ≤ 0 := by
  let numerator :=
    (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s
  have hnumerator : numerator.intDegree ≤ 2 := by
    dsimp only [numerator]
    exact intDegree_canceled_numerator_le_two A r s a b c hr hAs
  have hdiffDegree : (RatFunc.X - r).intDegree = 1 := intDegree_X_sub_eq_one hr
  have hdiffNe : RatFunc.X - r ≠ 0 := by
    intro h
    rw [h] at hdiffDegree
    simp at hdiffDegree
  have hdenDegree : ((RatFunc.X - r) ^ 2).intDegree = 2 := by
    rw [intDegree_pow hdiffNe, hdiffDegree]
    norm_num
  change (numerator / (RatFunc.X - r) ^ 2).intDegree ≤ 0
  by_cases hn0 : numerator = 0
  · simp [hn0]
  rw [RatFunc.intDegree_div hn0 (pow_ne_zero 2 hdiffNe), hdenDegree]
  omega

private lemma intDegree_paperX_addX_Q_le_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X)
    (hdegree : (paperX W x).intDegree ≤ 0) :
    (paperX W
      ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
        ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
          (cubicRat W ^ 2)))).intDegree ≤ 0 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  exact intDegree_canceled_expression_le_zero
    (cubicRat W) (paperX W x) (paperY W y) W.a₂ W.a₄ W.a₆ hdegree
      (intDegree_cubicRat_mul_paperY_le_one W hxy hdegree)

private lemma badAtInfinity_neg (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (-P) ↔ badAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      rfl

private lemma badAtInfinity_add_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P + Q W) := by
  cases P with
  | zero => simp [badAtInfinity] at hP
  | some x y hxy =>
      change (paperX W x).intDegree ≤ 0 at hP
      have hx : x ≠ cubicRat W * RatFunc.X := by
        intro hx
        have hpaper : paperX W x = RatFunc.X := by
          rw [hx, paperX_Q_coordinate]
        rw [hpaper] at hP
        norm_num at hP
      have hvertical :
          ¬(x = cubicRat W * RatFunc.X ∧
            y = (twist W).toAffine.negY (cubicRat W * RatFunc.X)
              (cubicRat W ^ 2)) := fun h ↦ hx h.1
      rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) _ from rfl]
      rw [WeierstrassCurve.Affine.Point.add_some hvertical]
      exact intDegree_paperX_addX_Q_le_zero W hxy hx hP

private lemma badAtInfinity_sub_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P - Q W) := by
  have hnegP : badAtInfinity W (-P) := (badAtInfinity_neg W P).mpr hP
  have hadd := badAtInfinity_add_Q W hnegP
  rw [show P - Q W = -(-P + Q W) by abel]
  exact (badAtInfinity_neg W (-P + Q W)).mpr hadd

private lemma badAtInfinity_add_Q_iff (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (P + Q W) ↔ badAtInfinity W P := by
  refine ⟨fun h ↦ ?_, badAtInfinity_add_Q W⟩
  have hsub := badAtInfinity_sub_Q W h
  simpa using hsub

private lemma point_add_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    point hchar W (n + 1) = point hchar W n + Q W := by
  rw [point, point, add_one_zsmul]
  abel

private lemma paperX_pZeroX [Finite F] (W : WeierstrassCurve F) :
    paperX W (pZeroX W) = RatFunc.X ^ Nat.card F := by
  unfold paperX pZeroX
  field_simp [cubicRat_ne_zero W]

private lemma pZero_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ¬badAtInfinity W (P₀ hchar W) := by
  intro hbad
  change (paperX W (pZeroX W)).intDegree ≤ 0 at hbad
  rw [paperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

private lemma point_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    ¬badAtInfinity W (point hchar W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [point] using pZero_not_badAtInfinity hchar W
  · intro k _ hk hbad
    apply hk
    apply (badAtInfinity_add_Q_iff W (point hchar W k)).mp
    rw [← point_add_one hchar W k]
    exact hbad
  · intro k _ hk hbad
    apply hk
    have hstep := point_add_one hchar W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (badAtInfinity_add_Q_iff W (point hchar W (k - 1))).mpr hbad

private lemma Q_ne_zero (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    Q W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

private def d [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) : ℕ :=
  match point hchar W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (x / cubicRat W)).natDegree

private lemma num_natDegree_gt_denom_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    (hn : point hchar W n = .some x y hxy) :
    (RatFunc.denom (x / cubicRat W)).natDegree <
      (RatFunc.num (x / cubicRat W)).natDegree := by
  have hnotBad := point_not_badAtInfinity hchar W n
  have hnotLe : ¬(paperX W x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (paperX W x).intDegree := lt_of_not_ge hnotLe
  unfold paperX RatFunc.intDegree at hpos
  omega

private lemma d_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    d hchar W 0 = Nat.card F := by
  rw [d, point]
  simp only [zero_zsmul, add_zero, P₀, WeierstrassCurve.Affine.Point.mk]
  have hx : pZeroX W / cubicRat W = RatFunc.X ^ Nat.card F := by
    rw [div_eq_iff (cubicRat_ne_zero W)]
    simp only [pZeroX]
    ring
  rw [hx]
  change
    (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
      Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma d_eq_zero_iff_point_eq_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W n = 0 ↔ point hchar W n = 0 := by
  cases hp : point hchar W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [d, hp]
  | some x y hxy =>
      have hdeg := num_natDegree_gt_denom_natDegree hchar W hp
      constructor
      · intro hd
        simp only [d, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma noAdjacentZeros [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∀ n, d hchar W n = 0 → d hchar W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (d_eq_zero_iff_point_eq_zero hchar W n).mp hn
  have hp1 := (d_eq_zero_iff_point_eq_zero hchar W (n + 1)).mp hn1
  apply Q_ne_zero W
  have hs := point_add_one hchar W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private def frobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private def eulerPolynomial [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W ^ ((Nat.card F - 1) / 2)

private def minusOneNumerator [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W * (eulerPolynomial W + 1) ^ 2 -
    (C W.a₂ + X ^ Nat.card F + X) * frobeniusPolynomial ^ 2

private lemma card_gt_three [Finite F] (hchar : ringChar F ≠ 2)
    (hcard : Nat.card F ≠ 3) : 3 < Nat.card F := by
  obtain ⟨k, hk⟩ := card_odd hchar
  have hlarge := Finite.one_lt_card (α := F)
  omega

private lemma twice_half_card_sub_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma twice_half_card_add_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 1) / 2) = Nat.card F + 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma cubic_pow_card [Finite F] (W : WeierstrassCurve F) :
    cubic W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) +
        C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  rw [← FiniteField.Polynomial.expand_card]
  simp only [cubic, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma minusOneNumerator_eq [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    minusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
        C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        C W.a₄ * X ^ Nat.card F +
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) + C W.a₄ * X +
        C (2 * W.a₆) := by
  have heven := twice_half_card_sub_one (F := F) hchar
  have hpower :
      cubic W * eulerPolynomial W ^ 2 = cubic W ^ Nat.card F := by
    rw [eulerPolynomial, ← pow_mul]
    rw [show (Nat.card F - 1) / 2 * 2 = Nat.card F - 1 by
      rw [mul_comm, heven]]
    calc
      cubic W * cubic W ^ (Nat.card F - 1) =
          cubic W ^ (Nat.card F - 1 + 1) := (pow_succ' _ _).symm
      _ = cubic W ^ Nat.card F := by
        congr
        have hpos := Nat.card_pos (α := F)
        omega
  have hmiddle :
      cubic W * (C 2 * eulerPolynomial W) =
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) := by
    rw [eulerPolynomial]
    have hadd : (Nat.card F - 1) / 2 + 1 = (Nat.card F + 1) / 2 := by
      obtain ⟨k, hk⟩ := card_odd hchar
      omega
    rw [show cubic W * (C 2 * cubic W ^ ((Nat.card F - 1) / 2)) =
      C 2 * cubic W ^ ((Nat.card F - 1) / 2 + 1) by ring]
    rw [hadd]
  unfold minusOneNumerator
  rw [show (eulerPolynomial W + 1) ^ 2 =
    eulerPolynomial W ^ 2 + C 2 * eulerPolynomial W + 1 by
      rw [Polynomial.C_ofNat]
      ring]
  rw [mul_add, mul_add, hpower, hmiddle, mul_one, cubic_pow_card]
  unfold frobeniusPolynomial
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma natDegree_add_le_of_le {p q : F[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (Polynomial.natDegree_add_le p q).trans (max_le hp hq)

private lemma minusOneNumerator_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  have hq := card_gt_three (F := F) hchar hcard
  have hhalf := twice_half_card_add_one (F := F) hchar
  let remainder : F[X] :=
    X ^ (Nat.card F + 2) +
      (C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        (C W.a₄ * X ^ Nat.card F +
          (C 2 * cubic W ^ ((Nat.card F + 1) / 2) +
            (C W.a₄ * X + C (2 * W.a₆)))))
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    apply natDegree_add_le_of_le
    · rw [Polynomial.natDegree_X_pow]
      omega
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · calc
        (C 2 * cubic W ^ ((Nat.card F + 1) / 2)).natDegree ≤
            (cubic W ^ ((Nat.card F + 1) / 2)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ = (Nat.card F + 1) / 2 * 3 := by
          rw [Polynomial.natDegree_pow, cubic_natDegree]
        _ ≤ 2 * Nat.card F := by omega
    apply natDegree_add_le_of_le
    · simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le W.a₄ 1).trans (by omega)
    · rw [Polynomial.natDegree_C]
      omega
  have heq :
      minusOneNumerator W = X ^ (2 * Nat.card F + 1) + remainder := by
    rw [minusOneNumerator_eq hchar]
    dsimp only [remainder]
    ring
  rw [heq]
  have hlt :
      remainder.natDegree < (X ^ (2 * Nat.card F + 1) : F[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    omega
  calc
    (X ^ (2 * Nat.card F + 1) + remainder).natDegree =
        (X ^ (2 * Nat.card F + 1) : F[X]).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
    _ = 2 * Nat.card F + 1 := Polynomial.natDegree_X_pow _

private lemma pZeroX_ne_qX [Finite F] (W : WeierstrassCurve F) :
    pZeroX W ≠ cubicRat W * RatFunc.X := by
  intro h
  have hpow : RatFunc.X ^ Nat.card F = RatFunc.X :=
    mul_left_cancel₀ (cubicRat_ne_zero W) h
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at hdegree
  simp only [mul_one] at hdegree
  have hcard := Finite.one_lt_card (α := F)
  omega

private lemma paperY_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W (pZeroY W) = cubicRat W ^ ((Nat.card F - 1) / 2) := by
  have hexponent :
      (Nat.card F + 3) / 2 = (Nat.card F - 1) / 2 + 2 := by
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  unfold paperY pZeroY
  rw [hexponent, pow_add]
  field_simp [cubicRat_ne_zero W]

private lemma cubic_mul_eulerPolynomial [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    cubic W * eulerPolynomial W = cubic W ^ ((Nat.card F + 1) / 2) := by
  unfold eulerPolynomial
  rw [show cubic W * cubic W ^ ((Nat.card F - 1) / 2) =
    cubic W ^ ((Nat.card F - 1) / 2 + 1) by
      exact (pow_succ' _ _).symm]
  congr 1
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma minusOneNumerator_canceled_eq [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    minusOneNumerator W =
      (X + X ^ Nat.card F) * (C W.a₄ + X * X ^ Nat.card F) +
        C 2 * (C W.a₂ * X * X ^ Nat.card F + C W.a₆) +
        C 2 * cubic W * eulerPolynomial W := by
  rw [minusOneNumerator_eq hchar]
  rw [show C 2 * cubic W * eulerPolynomial W =
    C 2 * (cubic W * eulerPolynomial W) by ring]
  rw [cubic_mul_eulerPolynomial hchar]
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma paperY_neg_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) =
      -(cubicRat W ^ ((Nat.card F - 1) / 2)) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  rw [show paperY W (-pZeroY W) = -paperY W (pZeroY W) by
    unfold paperY
    exact neg_div _ _]
  rw [paperY_pZeroY hchar W]

private lemma algebraMap_frobeniusPolynomial [Finite F] :
    algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) =
      RatFunc.X ^ Nat.card F - RatFunc.X := by
  simp [frobeniusPolynomial, RatFunc.algebraMap_X]

private lemma algebraMap_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    algebraMap F[X] (RatFunc F) (minusOneNumerator W) =
      (RatFunc.X + RatFunc.X ^ Nat.card F) *
          (RatFunc.C W.a₄ + RatFunc.X * RatFunc.X ^ Nat.card F) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * RatFunc.X ^ Nat.card F +
          RatFunc.C W.a₆) +
        2 * cubicRat W * cubicRat W ^ ((Nat.card F - 1) / 2) := by
  rw [minusOneNumerator_canceled_eq hchar]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, cubicRat, eulerPolynomial]

private lemma paperX_negPZero_add_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2 := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  rw [paperX_addX_Q_canceled W hneg (pZeroX_ne_qX W)]
  rw [paperX_pZeroX, paperY_neg_pZeroY hchar W]
  rw [algebraMap_minusOneNumerator hchar, algebraMap_frobeniusPolynomial]
  ring

private lemma point_neg_one_eq_some [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∃ y hxy, point hchar W (-1) =
      .some
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) y hxy := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -P₀ hchar W = .some (pZeroX W)
        ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) hneg := by
    rw [show P₀ hchar W = .some (pZeroX W) (pZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) (pZeroX_ne_qX W)
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W))
  rw [← hnegP, ← show Q W = .some (cubicRat W * RatFunc.X)
    (cubicRat W ^ 2) _ from rfl] at hadd
  have hpoint : point hchar W (-1) = -(-P₀ hchar W + Q W) := by
    unfold point
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private def squareFiber (W : WeierstrassCurve F) (x : F) :=
  {y : F // y ^ 2 = (cubic W).eval x}

private instance squareFiberFinite [Finite F] (W : WeierstrassCurve F)
    (x : F) : Finite (squareFiber W x) := by
  unfold squareFiber
  infer_instance

private lemma two_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
    (2 : F) ≠ 0 := by
  let _ : CharP F (ringChar F) := ringChar.charP F
  intro htwo
  have hdvd : ringChar F ∣ 2 :=
    (CharP.cast_eq_zero_iff F (ringChar F) 2).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwoChar
  · have hcast : ((1 : ℕ) : F) = 0 :=
      (CharP.cast_eq_zero_iff F (ringChar F) 1).mpr (by simp [hone])
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa only [Nat.cast_one] using hcast)
  · exact hchar htwoChar

private lemma squareFiber_natCard_eq_one [Finite F] (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Nat.card (squareFiber W x) = 1 := by
  let _ : Nonempty (squareFiber W x) :=
    ⟨⟨0, by simp [hzero]⟩⟩
  let _ : Subsingleton (squareFiber W x) := ⟨by
    intro y z
    apply Subtype.ext
    have hy : y.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using y.2)
    have hz : z.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using z.2)
    rw [hy, hz]⟩
  exact Nat.card_unique

private lemma squareFiber_natCard_eq_two [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Nat.card (squareFiber W x) = 2 := by
  classical
  rcases hsquare with ⟨r, hr⟩
  have hrpow : r ^ 2 = (cubic W).eval x := by
    simpa [pow_two] using hr.symm
  have hrzero : r ≠ 0 := by
    intro hr0
    apply hzero
    rw [← hrpow, hr0]
    simp
  have hneg : -r ≠ r := by
    intro h
    have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
    have hadd : r + r = 0 := by
      calc
        r + r = -r + r := congrArg (fun z : F ↦ z + r) h.symm
        _ = 0 := neg_add_cancel r
    have hproduct : (2 : F) * r = 0 := by
      rw [two_mul]
      exact hadd
    exact hrzero ((mul_eq_zero.mp hproduct).resolve_left htwo)
  let e : squareFiber W x ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun b ↦ match b with
        | true => ⟨r, hrpow⟩
        | false => ⟨-r, by simpa using hrpow⟩
      left_inv := by
        intro y
        have hy : y.1 = r ∨ y.1 = -r :=
          (sq_eq_sq_iff_eq_or_eq_neg).mp (y.2.trans hrpow.symm)
        apply Subtype.ext
        rcases hy with hy | hy
        · simp [hy]
        · simp [hy, hneg]
      right_inv := by
        intro b
        cases b <;> simp [hneg] }
  simpa using Nat.card_congr e

private lemma squareFiber_natCard_eq_zero [Finite F]
    (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    Nat.card (squareFiber W x) = 0 := by
  let _ : IsEmpty (squareFiber W x) := ⟨fun y ↦ hsquare ⟨y.1, by
    simpa [pow_two] using y.2.symm⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private lemma eval_eulerPolynomial [Fintype F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) (x : F) :
    (eulerPolynomial W).eval x =
      ((quadraticChar F) ((cubic W).eval x) : F) := by
  have hhalf :
      Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  have hcriterion :=
    quadraticChar_eq_pow_of_char_ne_two' hchar ((cubic W).eval x)
  rw [hhalf] at hcriterion
  unfold eulerPolynomial
  rw [eval_pow, Nat.card_eq_fintype_card]
  exact hcriterion.symm

private lemma eval_eulerPolynomial_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (eulerPolynomial W).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar, hzero]
  simp

private lemma eval_eulerPolynomial_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [(quadraticChar_one_iff_isSquare hzero).mpr hsquare]
  simp

private lemma eval_eulerPolynomial_eq_neg_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = -1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsquare]
  simp

private lemma eval_frobeniusPolynomial [Finite F] (x : F) :
    (frobeniusPolynomial : F[X]).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, Nat.card_eq_fintype_card,
    FiniteField.pow_card, sub_self]

private lemma eval_minusOneNumerator [Finite F]
    (W : WeierstrassCurve F) (x : F) :
    (minusOneNumerator W).eval x =
      (cubic W).eval x * ((eulerPolynomial W).eval x + 1) ^ 2 := by
  unfold minusOneNumerator
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_one]
  rw [eval_frobeniusPolynomial]
  ring

private lemma eval_derivative_minusOneNumerator_of_cubic_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (minusOneNumerator W).derivative.eval x = (cubic W).derivative.eval x := by
  have heuler := eval_eulerPolynomial_eq_zero hchar W x hzero
  have hfrobenius := eval_frobeniusPolynomial (F := F) x
  unfold minusOneNumerator
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add,
    derivative_one, eval_sub, eval_add, eval_mul, eval_pow, eval_one]
  rw [hzero, heuler, hfrobenius]
  ring

private lemma eval_derivative_cubic_ne_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (x : F) (hzero : (cubic W).eval x = 0) :
    (cubic W).derivative.eval x ≠ 0 := by
  intro hderivative
  obtain ⟨u, v, huv⟩ :=
    (Polynomial.separable_def (cubic W)).mp (cubic_separable W)
  have heval := congrArg (Polynomial.eval x) huv
  simp only [eval_add, eval_mul, eval_one] at heval
  rw [hzero, hderivative] at heval
  simp at heval

private lemma eval_derivative_eq_zero_of_sq_dvd {p : F[X]} {x : F}
    (hdiv : (X - C x) ^ 2 ∣ p) : p.derivative.eval x = 0 := by
  rcases hdiv with ⟨q, rfl⟩
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X,
    derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  ring

private lemma minusOneNumerator_ne_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) : minusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := minusOneNumerator_natDegree hchar W hcard
  rw [hzero] at hdegree
  simp at hdegree

private lemma rootMultiplicity_minusOneNumerator_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hroot : (minusOneNumerator W).IsRoot x := by
    change (minusOneNumerator W).eval x = 0
    rw [eval_minusOneNumerator, hzero]
    ring
  have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneNumerator W) := by
    rw [Polynomial.le_rootMultiplicity_iff hB]
    simpa using (Polynomial.dvd_iff_isRoot.mpr hroot)
  have hupper : Polynomial.rootMultiplicity x (minusOneNumerator W) ≤ 1 := by
    rw [Polynomial.rootMultiplicity_le_iff hB]
    intro hsquare
    have hderivative := eval_derivative_eq_zero_of_sq_dvd hsquare
    rw [eval_derivative_minusOneNumerator_of_cubic_eq_zero hchar W x hzero]
      at hderivative
    exact eval_derivative_cubic_ne_zero W x hzero hderivative
  omega

private lemma rootMultiplicity_minusOneNumerator_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heuler := eval_eulerPolynomial_eq_one hchar W x hzero hsquare
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hsum : (1 + 1 : F) ≠ 0 := by
    intro h
    apply htwo
    norm_num at h ⊢
    exact h
  have heval : (minusOneNumerator W).eval x ≠ 0 := by
    rw [eval_minusOneNumerator, heuler]
    exact mul_ne_zero hzero (pow_ne_zero 2 hsum)
  exact heval hroot

private lemma sq_X_sub_C_dvd_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (X - C x) ^ 2 ∣ minusOneNumerator W := by
  have heuler := eval_eulerPolynomial_eq_neg_one hchar W x hsquare
  have heulerRoot : (eulerPolynomial W + 1).IsRoot x := by
    simp only [IsRoot, eval_add, eval_one, heuler]
    ring
  have hfrobeniusRoot : (frobeniusPolynomial : F[X]).IsRoot x :=
    eval_frobeniusPolynomial x
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr heulerRoot
  obtain ⟨v, hv⟩ := Polynomial.dvd_iff_isRoot.mpr hfrobeniusRoot
  refine ⟨cubic W * u ^ 2 - (C W.a₂ + X ^ Nat.card F + X) * v ^ 2, ?_⟩
  unfold minusOneNumerator
  rw [hu, hv]
  ring

private lemma count_roots_frobeniusPolynomial [Finite F] (x : F) :
    Multiset.count x (frobeniusPolynomial : F[X]).roots = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X]
  simp

private lemma count_roots_frobeniusPolynomial_sq [Finite F] (x : F) :
    Multiset.count x ((frobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_frobeniusPolynomial]

private lemma frobeniusPolynomial_ne_zero [Finite F] :
    (frobeniusPolynomial : F[X]) ≠ 0 := by
  intro hzero
  have hcount := count_roots_frobeniusPolynomial (F := F) 0
  rw [hzero] at hcount
  simp at hcount

private def minusOneGCD [Finite F] (W : WeierstrassCurve F) : F[X] :=
  gcd (minusOneNumerator W) (frobeniusPolynomial ^ 2)

private lemma count_roots_minusOneGCD [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) :
    Multiset.count x (minusOneGCD W).roots =
      2 - Nat.card (squareFiber W x) := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (frobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_frobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣ (frobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hzero : (cubic W).eval x = 0
  · have hlinearB : X - C x ∣ minusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (minusOneNumerator W).eval x = 0
      rw [eval_minusOneNumerator, hzero]
      ring
    have hlinearL' : X - C x ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
      exact hlinearL.trans ⟨frobeniusPolynomial, by ring⟩
    have hcommon : X - C x ∣ minusOneGCD W := by
      unfold minusOneGCD
      exact dvd_gcd hlinearB hlinearL'
    have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity x (minusOneGCD W) ≤
            Polynomial.rootMultiplicity x (minusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
        _ = 1 := rootMultiplicity_minusOneNumerator_eq_one
          hchar W hcard x hzero
    have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      squareFiber_natCard_eq_one W x hzero]
  · by_cases hsquare : IsSquare ((cubic W).eval x)
    · have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x (minusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
          _ = 0 := rootMultiplicity_minusOneNumerator_eq_zero
            hchar W x hzero hsquare
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_two hchar W x hzero hsquare]
    · have hcommon : (X - C x) ^ 2 ∣ minusOneGCD W := by
        unfold minusOneGCD
        exact dvd_gcd
          (sq_X_sub_C_dvd_minusOneNumerator hchar W x hsquare) hlinearLsq
      have hlower : 2 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL :
          Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_frobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 2 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_zero W x hsquare]

private lemma squareFiber_natCard_le_two [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F) :
    Nat.card (squareFiber W x) ≤ 2 := by
  by_cases hzero : (cubic W).eval x = 0
  · rw [squareFiber_natCard_eq_one W x hzero]
    omega
  by_cases hsquare : IsSquare ((cubic W).eval x)
  · rw [squareFiber_natCard_eq_two hchar W x hzero hsquare]
  · rw [squareFiber_natCard_eq_zero W x hsquare]
    omega

private lemma frobeniusPolynomial_splits [Finite F] :
    (frobeniusPolynomial : F[X]).Splits := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

private lemma minusOneGCD_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (minusOneGCD W).Splits :=
    (frobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (minusOneGCD W).roots) =
        (minusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (minusOneGCD W).roots) (by simp))
  calc
    (minusOneGCD W).natDegree = (minusOneGCD W).roots.card :=
      hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (minusOneGCD W).roots := hsum.symm
    _ = ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_minusOneGCD hchar W hcard x

private lemma minusOneGCD_natDegree_add_fiber_sum [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree + ∑ x : F, Nat.card (squareFiber W x) =
      2 * Nat.card F := by
  rw [minusOneGCD_natDegree hchar W hcard]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (squareFiber W x) +
        Nat.card (squareFiber W x))) = ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (squareFiber_natCard_le_two hchar W x)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma equation_iff_square (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = (cubic W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₃_of_isCharNeTwoNF, zero_mul]
  simp only [cubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  simp

private def affineSolutionsEquivSquareFibers (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, squareFiber W x where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (equation_iff_square W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (equation_iff_square W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma pointCount_eq_fiber_sum [Fintype F]
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSquareFibers W), Nat.card_sigma]

private lemma natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)).natDegree =
      (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul :
      gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

private lemma minusOneQuotient_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W / minusOneGCD W).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hmulB :
      minusOneGCD W * (minusOneNumerator W / minusOneGCD W) =
        minusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivB
  have hquotB : minusOneNumerator W / minusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulB
    exact hB hmulB.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotB
  rw [hmulB, minusOneNumerator_natDegree hchar W hcard] at hdegreeProduct
  have hdegreeG := minusOneGCD_natDegree_add_fiber_sum hchar W hcard
  omega

private lemma num_natDegree_minusOneRat [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2)).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (frobeniusPolynomial : F[X]) 2]
  rw [natDegree_num_div _ _ (pow_ne_zero 2 frobeniusPolynomial_ne_zero)]
  exact minusOneQuotient_natDegree hchar W hcard

private lemma d_neg_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (hcard : Nat.card F ≠ 3) :
    d hchar W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := point_neg_one_eq_some hchar W
  unfold d
  rw [hpoint]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))))).natDegree = _
  rw [paperX_negPZero_add_Q hchar W]
  rw [num_natDegree_minusOneRat hchar W hcard]
  exact (pointCount_eq_fiber_sum W).symm

private def symmetricInput (f g : F[X]) : Fin 3 → F[X] :=
  ![X * f, X * g + f, g]

private def symmetricOutput (W : WeierstrassCurve F) (f g : F[X]) :
    Fin 3 → F[X] :=
  fun i ↦ MvPolynomial.eval (symmetricInput f g) ((W.map C).addSubMap i)

private lemma symmetricOutput_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (f g : F[X]) :
    symmetricOutput W f g 0 =
      (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
        C (4 * W.a₆) * (X * g + f) * g -
          C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

private lemma symmetricOutput_one (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (f g : F[X]) :
    symmetricOutput W f g 1 =
      C 2 * (X * g + f) * (X * f) +
        C (4 * W.a₂) * (X * f) * g +
          C (2 * W.a₄) * (X * g + f) * g + C (4 * W.a₆) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

private lemma symmetricOutput_two (W : WeierstrassCurve F)
    (f g : F[X]) :
    symmetricOutput W f g 2 = (X * g - f) ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap]
  ring

private lemma primitive_symmetricOutput (W : WeierstrassCurve F)
    [W.IsElliptic] {f g : F[X]} (hfg : IsCoprime f g)
    (hh : X * g - f ≠ 0) :
    PrimitiveTriple (symmetricOutput W f g 0)
      (symmetricOutput W f g 1) (symmetricOutput W f g 2) := by
  apply primitiveTriple_of_no_common_irreducible
  · rw [symmetricOutput_two]
    exact pow_ne_zero 2 hh
  · intro p hp hp0 hp1 hp2
    have hout : ∀ i : Fin 3, p ∣ symmetricOutput W f g i := by
      intro i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    have hinPow (i : Fin 3) : p ∣ symmetricInput f g i ^ 4 := by
      rw [← (W.map C).addSubMapCoeff_condition (symmetricInput f g) i]
      apply Finset.dvd_sum
      intro j _
      exact (hout j).mul_left _
    have hin (i : Fin 3) : p ∣ symmetricInput f g i :=
      hp.prime.dvd_of_dvd_pow (hinPow i)
    have hpg : p ∣ g := by simpa [symmetricInput] using hin 2
    have hpf : p ∣ f := by
      have hdiff := (hin 1).sub (hpg.mul_left X)
      simpa [symmetricInput] using hdiff
    exact hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)

private lemma symmetricOutput_zero_natDegree (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (symmetricOutput W f g 0).natDegree = 2 * f.natDegree + 2 := by
  let t₁ := C (2 * W.a₄) * (X * f) * g
  let t₂ := C (4 * W.a₆) * (X * g + f) * g
  let t₃ := C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2
  let remainder := t₁ + t₂ + t₃
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hXgAdd : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le (X * g) f).trans (max_le hXg le_rfl)
  have ht₁ : t₁.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₁]
    calc
      (C (2 * W.a₄) * (X * f) * g).natDegree ≤
          (C (2 * W.a₄) * (X * f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (2 * W.a₄) (X * f)) g.natDegree
      _ ≤ 2 * f.natDegree := by rw [hXf]; omega
  have ht₂ : t₂.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₂]
    calc
      (C (4 * W.a₆) * (X * g + f) * g).natDegree ≤
          (C (4 * W.a₆) * (X * g + f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * g + f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (4 * W.a₆) (X * g + f)) g.natDegree
      _ ≤ 2 * f.natDegree := by omega
  have ht₃ : t₃.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₃]
    calc
      (C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2).natDegree ≤
          (g ^ 2).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ ≤ 2 * f.natDegree := by omega
  have hremainder : remainder.natDegree ≤ 2 * f.natDegree := by
    dsimp only [remainder]
    exact (Polynomial.natDegree_add_le (t₁ + t₂) t₃).trans
      (max_le
        ((Polynomial.natDegree_add_le t₁ t₂).trans (max_le ht₁ ht₂)) ht₃)
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  rw [symmetricOutput_zero]
  have heq :
      (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
          C (4 * W.a₆) * (X * g + f) * g -
            C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 =
        (X * f) ^ 2 - remainder := by
    dsimp only [remainder, t₁, t₂, t₃]
    ring
  rw [heq]
  calc
    ((X * f) ^ 2 - remainder).natDegree = ((X * f) ^ 2).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [hmain]
      omega
    _ = 2 * f.natDegree + 2 := hmain

private def additionCommon (W : WeierstrassCurve F) (r : RatFunc F) : RatFunc F :=
  (RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
    2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)

private def symmetricFirstRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  (RatFunc.X * r - RatFunc.C W.a₄) ^ 2 -
    4 * RatFunc.C W.a₆ * (RatFunc.X + RatFunc.C W.a₂ + r)

private def symmetricSecondRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  2 * additionCommon W r

private def symmetricDenominatorRat (r : RatFunc F) : RatFunc F :=
  (RatFunc.X - r) ^ 2

private lemma addition_product_identity (W : WeierstrassCurve F)
    {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) :
    (additionCommon W r - 2 * cubicRat W * s) *
        (additionCommon W r + 2 * cubicRat W * s) =
      symmetricDenominatorRat r * symmetricFirstRat W r := by
  have hsquare :
      (cubicRat W * s) ^ 2 =
        cubicRat W *
          (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 +
            RatFunc.C W.a₄ * r + RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  have hproduct := product_formula
    (RatFunc.C W.a₂) (RatFunc.C W.a₄) (RatFunc.C W.a₆)
      RatFunc.X r 1
  rw [cubicRat_eq] at hsquare
  dsimp only at hproduct
  unfold additionCommon symmetricDenominatorRat symmetricFirstRat
  rw [cubicRat_eq W]
  calc
    _ = ((RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
          2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)) ^ 2 -
        4 * ((RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
          RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * s) ^ 2 := by ring
    _ = _ := by
      rw [hsquare]
      linear_combination hproduct

private lemma algebraMap_symmetricOutput_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 0) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricFirstRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_zero]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricFirstRat
  ring

private lemma algebraMap_symmetricOutput_one (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 1) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricSecondRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_one]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricSecondRat additionCommon
  ring

private lemma algebraMap_symmetricOutput_two (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 2) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricDenominatorRat r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_two]
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_X]
  rw [hr]
  unfold symmetricDenominatorRat
  ring

private lemma symmetricOutput_zero_ratio (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      symmetricFirstRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_zero, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

private lemma symmetricOutput_one_ratio (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      symmetricSecondRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_one, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

private lemma symmetricOutput_pair_product (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 *
        ((additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2) := by
  rw [symmetricOutput_zero_ratio]
  unfold symmetricDenominatorRat
  have hproduct := addition_product_identity W heq
  unfold symmetricDenominatorRat at hproduct
  field_simp [hdiff]
  linear_combination -hproduct

private lemma symmetricOutput_pair_sum (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r s : RatFunc F) (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 +
        (additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 := by
  rw [symmetricOutput_one_ratio]
  unfold symmetricSecondRat symmetricDenominatorRat
  field_simp [hdiff]
  unfold additionCommon
  ring

private lemma paperY_negY (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) :
    paperY W ((twist W).toAffine.negY x y) = -paperY W y := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  unfold paperY
  ring

private lemma paperX_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) -
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  rfl

private lemma paperX_neg_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY x y) (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) +
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  rw [paperX_addX_Q_common W hneg hx]
  rw [paperY_negY]
  ring

private def addQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
      (cubicRat W ^ 2))

private def subQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
      ((twist W).toAffine.negY x y) (cubicRat W ^ 2))

private lemma X_sub_paperX_ne_zero (W : WeierstrassCurve F)
    {x : RatFunc F} (hx : x ≠ cubicRat W * RatFunc.X) :
    RatFunc.X - paperX W x ≠ 0 := by
  intro hzero
  apply hx
  have hpaper : paperX W x = RatFunc.X := by
    exact (sub_eq_zero.mp hzero).symm
  unfold paperX at hpaper
  calc
    x = RatFunc.X * cubicRat W :=
      (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
    _ = cubicRat W * RatFunc.X := by ring

private lemma X_mul_denom_sub_num_ne_zero {r : RatFunc F}
    (h : RatFunc.X - r ≠ 0) : X * r.denom - r.num ≠ 0 := by
  intro hzero
  apply h
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_sub, map_mul, map_zero, RatFunc.algebraMap_X] at hmap
  rw [hnum] at hmap
  apply (mul_eq_zero.mp ?_).resolve_right hden
  linear_combination hmap

private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
    (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

private lemma four_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
    (4 : F) ≠ 0 := by
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  intro hfour
  have hmul : (2 : F) * 2 = 0 := by
    calc
      (2 : F) * 2 = 4 := by norm_num
      _ = 0 := hfour
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact htwo hzero
  · exact htwo hzero

private lemma Q_y_ne_negY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    cubicRat W ^ 2 ≠
      (twist W).toAffine.negY (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  intro hneg
  have htwoF := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have htwo : (2 : RatFunc F) ≠ 0 := by
    intro hzero
    apply htwoF
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  have hsum : (2 : RatFunc F) * cubicRat W ^ 2 = 0 := by
    linear_combination hneg
  rcases mul_eq_zero.mp hsum with htwoZero | hcubicZero
  · exact htwo htwoZero
  · exact cubicRat_ne_zero W (sq_eq_zero_iff.mp hcubicZero)

private lemma paperX_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2) (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W) := by
  have hnum :
      (cubicRat W * RatFunc.X) ^ 4 -
          (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) ^ 2 -
          2 * (twist W).toAffine.b₆ * (cubicRat W * RatFunc.X) -
          (twist W).toAffine.b₈ =
        cubicRat W ^ 4 *
          algebraMap F[X] (RatFunc F) (duplicationNumerator W) := by
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, twist]
    simp only [duplicationNumerator, map_add, map_sub, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    ring
  have hden :
      4 * (cubicRat W * RatFunc.X) ^ 3 +
          (twist W).toAffine.b₂ * (cubicRat W * RatFunc.X) ^ 2 +
          2 * (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) +
          (twist W).toAffine.b₆ =
        4 * cubicRat W ^ 4 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, twist]
    rw [cubicRat_eq W]
    ring
  have hfourRat : (4 : RatFunc F) ≠ 0 := by
    intro hzero
    apply four_ne_zero_of_ringChar_ne_two (F := F) hchar
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  rw [(twist W).toAffine.addX_self_of_Y_ne (q_equation W)
    (Q_y_ne_negY hchar W)]
  rw [hnum, hden]
  unfold paperX
  field_simp [cubicRat_ne_zero W, hfourRat]

private lemma duplicationNumerator_natDegree (W : WeierstrassCurve F) :
    (duplicationNumerator W).natDegree = 4 := by
  unfold duplicationNumerator
  compute_degree <;> norm_num

private lemma natDegree_num_div_of_isCoprime (p q : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rw [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree
  exact hdegree.symm

private lemma num_natDegree_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W))).natDegree = 4 := by
  have hfour := four_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hCfour : C (4 : F) ≠ 0 := Polynomial.C_ne_zero.mpr hfour
  have hden : C (4 : F) * cubic W ≠ 0 :=
    mul_ne_zero hCfour (cubic_ne_zero W)
  have hcopFour : IsCoprime (duplicationNumerator W) (C (4 : F)) := by
    refine ⟨0, C (4 : F)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hfour, C_1]
  have hcop :
      IsCoprime (duplicationNumerator W) (C (4 : F) * cubic W) :=
    hcopFour.mul_right (isCoprime_cubic_duplicationNumerator W).symm
  have hmapDen :
      (4 : RatFunc F) * cubicRat W =
        algebraMap F[X] (RatFunc F) (C (4 : F) * cubic W) := by
    rw [map_mul, RatFunc.algebraMap_C]
    change (4 : RatFunc F) * cubicRat W = RatFunc.C (4 : F) * cubicRat W
    congr 1
    simp only [map_ofNat]
  rw [hmapDen]
  rw [natDegree_num_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := duplicationNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    hden hcop]
  exact duplicationNumerator_natDegree W

private lemma d_eq_one_of_point_eq_Q [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_one_of_point_eq_neg_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_four_of_point_eq_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W + Q W) : d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma d_eq_four_of_point_eq_neg_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -(Q W + Q W)) :
    d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma point_sub_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    point hchar W (n - 1) = point hchar W n - Q W := by
  have hstep := point_add_one hchar W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma generic_neighbor_degree_identity (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    {hMinus : (twist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (twist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ cubicRat W * RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (twist W).toAffine.Point) + Q W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (twist W).toAffine.Point) - Q W)
    (hdegree : (paperX W x).denom.natDegree <
      (paperX W x).num.natDegree)
    (hdegreeMinus : (paperX W xMinus).denom.natDegree <
      (paperX W xMinus).num.natDegree)
    (hdegreePlus : (paperX W xPlus).denom.natDegree <
      (paperX W xPlus).num.natDegree) :
    (paperX W xMinus).num.natDegree +
        (paperX W xPlus).num.natDegree =
      2 * (paperX W x).num.natDegree + 2 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus = addQX W x y := by
    exact hplusEq.1
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (twist W).toAffine.Point) - Q W =
    -(-(.some x y hxy : (twist W).toAffine.Point) + Q W) by abel] at hminusEq
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
    at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus = subQX W x y := by
    exact hminusEq.1
  have hrPlus :
      paperX W xPlus =
        (additionCommon W (paperX W x) -
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxPlus]
    exact paperX_addX_Q_common W hxy hxQ
  have hrMinus :
      paperX W xMinus =
        (additionCommon W (paperX W x) +
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxMinus]
    exact paperX_neg_addX_Q_common W hxy hxQ
  have heq := paper_coordinates_equation W hxy
  have hdiff := X_sub_paperX_ne_zero W hxQ
  have hprod := symmetricOutput_pair_product W heq hdiff
  have hsum := symmetricOutput_pair_sum W (paperX W x) (paperY W y) hdiff
  rw [← hrPlus, ← hrMinus] at hprod hsum
  have hprod' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 0) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus * paperX W xPlus := by
    simpa only [mul_comm] using hprod
  have hsum' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 1) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus + paperX W xPlus := by
    simpa only [add_comm] using hsum
  have hpoly : X * (paperX W x).denom - (paperX W x).num ≠ 0 :=
    X_mul_denom_sub_num_ne_zero hdiff
  have hprimitive := primitive_symmetricOutput W
    (RatFunc.isCoprime_num_denom (paperX W x)) hpoly
  have hout2 :
      symmetricOutput W (paperX W x).num (paperX W x).denom 2 ≠ 0 := by
    rw [symmetricOutput_two]
    exact pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout2
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod' hsum'
  have hcenter := symmetricOutput_zero_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma d_recurrence [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W (n - 1) + d hchar W (n + 1) = 2 * d hchar W n + 2 := by
  cases hn : point hchar W n with
  | zero =>
      have hplus := point_add_one hchar W n
      have hminus := point_sub_one hchar W n
      rw [hn] at hplus hminus
      have hplusQ : point hchar W (n + 1) = Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : point hchar W (n - 1) = -Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := d_eq_one_of_point_eq_Q hchar W hplusQ
      have hdMinus := d_eq_one_of_point_eq_neg_Q hchar W hminusQ
      have hd : d hchar W n = 0 := by simp [d, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : point hchar W (n - 1) with
      | zero =>
          have hsub := point_sub_one hchar W n
          rw [hn, hminusPoint] at hsub
          have hnQ : point hchar W n = Q W := by
            have hxyQ :
                (.some x y hxy : (twist W).toAffine.Point) = Q W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := point_add_one hchar W n
          rw [hnQ] at hplus
          have hd := d_eq_one_of_point_eq_Q hchar W hnQ
          have hdPlus := d_eq_four_of_point_eq_two_Q hchar W hplus
          have hdMinus : d hchar W (n - 1) = 0 := by
            simp [d, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : point hchar W (n + 1) with
          | zero =>
              have hadd := point_add_one hchar W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : point hchar W n = -Q W := by
                have htranslated := congrArg
                  (fun P : (twist W).toAffine.Point ↦ P - Q W) hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (twist W).toAffine.Point) = -Q W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := point_sub_one hchar W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  point hchar W (n - 1) = -(Q W + Q W) := by
                calc
                  point hchar W (n - 1) = -Q W - Q W := hminus
                  _ = -(Q W + Q W) := by abel
              have hd := d_eq_one_of_point_eq_neg_Q hchar W hnNegQ
              have hdMinus :=
                d_eq_four_of_point_eq_neg_two_Q hchar W hminusNegTwo
              have hdPlus : d hchar W (n + 1) = 0 := by
                simp [d, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := point_add_one hchar W n
              have hminus := point_sub_one hchar W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ Q W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ -Q W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (twist W).toAffine.Nonsingular
                  (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (q_equation W)
              have hxQ : x ≠ cubicRat W * RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
              have hdegree :=
                num_natDegree_gt_denom_natDegree hchar W hn
              have hdegreeMinus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hminusPoint
              have hdegreePlus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hplusPoint
              have hgeneric := generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [d, hn, hminusPoint, hplusPoint, paperX] using hgeneric

private lemma ringChar_ne_two (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : ringChar F ≠ 2 := by
  intro hchar
  let _ : CharP F 2 := ringChar.of_eq hchar
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h16 : (16 : F) = 0 := by
    calc
      (16 : F) = (2 : F) * 8 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h64 : (64 : F) = 0 := by
    calc
      (64 : F) = (2 : F) * 32 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h288 : (288 : F) = 0 := by
    calc
      (288 : F) = (2 : F) * 144 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h432 : (432 : F) = 0 := by
    calc
      (432 : F) = (2 : F) * 216 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have hdelta : W.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, h16, h64, h288, h432]
    ring
  rw [← W.coe_Δ'] at hdelta
  exact Units.ne_zero W.Δ' hdelta

private lemma degreeDataAtThree_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 7) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 3 N) := by
  let a : ℤ := 4 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 7 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 9 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic
    3 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn _
    norm_num at hn
    nlinarith [sq_nonneg (2 * n + a)]

/-- **Manin degree data over the field with three elements.** Let $F$ be a field with exactly
three elements, let $W$ be any Weierstrass curve over $F$, and let $N$ be the number of
nonsingular points of $W$ over $F$, including the point at infinity. Then there is Manin degree
data for $(3, N)$: a function $d : \mathbb{Z} \to \mathbb{N}$ with $d(0) = 3$, $d(-1) = N$,
$d(n - 1) + d(n + 1) = 2 d(n) + 2$ for every integer $n$, and no integer $n$ with
$d(n) = d(n + 1) = 0$.

The proof needs only the elementary bound $N \le 2 \cdot 3 + 1$. -/
public theorem manin_degree_data_of_card_eq_three [Finite F] (hF : Nat.card F = 3)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtThree_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

/-- **Manin degree data for the odd-characteristic normal form.** Let $F$ be a finite field with
$q$ elements, let $W$ be a Weierstrass curve $y^2 = x^3 + a_2 x^2 + a_4 x + a_6$ over $F$ (that
is, $a_1 = a_3 = 0$) with nonzero discriminant, and let $N$ be the number of points of $W$ over
$F$, including the point at infinity. Then there is Manin degree data for $(q, N)$: a function
$d : \mathbb{Z} \to \mathbb{N}$ with $d(0) = q$, $d(-1) = N$,
$d(n - 1) + d(n + 1) = 2 d(n) + 2$ for every integer $n$, and no integer $n$ with
$d(n) = d(n + 1) = 0$. -/
public theorem manin_degree_data_of_isCharNeTwoNF [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 3
  · exact manin_degree_data_of_card_eq_three hF W
  · exact ⟨{
      d := d (ringChar_ne_two W) W
      zero := d_zero (ringChar_ne_two W) W
      negOne := d_neg_one (ringChar_ne_two W) W hF
      recurrence := d_recurrence (ringChar_ne_two W) W
      noAdjacentZeros := noAdjacentZeros (ringChar_ne_two W) W }⟩

/-- **Hasse bound for the odd-characteristic normal form.** Let $F$ be a finite field with $q$
elements and let $W$ be a Weierstrass curve $y^2 = x^3 + a_2 x^2 + a_4 x + a_6$ over $F$ (that
is, $a_1 = a_3 = 0$) with nonzero discriminant. If $N$ is the number of points of $W$ over $F$,
including the point at infinity, then $(q + 1 - N)^2 \le 4q$. -/
public theorem hasse_bound_of_isCharNeTwoNF [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) :=
  (Classical.choice (manin_degree_data_of_isCharNeTwoNF W)).hasse_bound

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
