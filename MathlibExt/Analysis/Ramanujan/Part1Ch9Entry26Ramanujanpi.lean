/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry24Dougall
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This module proves Entry 26, Ramanujan's Landen-type dilogarithm identity.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry26Ramanujanpi

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9BoundaryLog (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log x

def chapter9DilogCosTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.cos ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def chapter9DilogSinTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.sin ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

/-- **The Entry 26 boundary logarithm is the real logarithm.** Let $\log$ be the real logarithm,
extended to all of $\mathbb{R}$ by $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$. For every
real $x$, the boundary logarithm of $x$, defined as $0$ if $x = 0$ and as $\log x$ otherwise,
equals $\log x$. -/
theorem chapter9BoundaryLog_eq_log (x : ℝ) : chapter9BoundaryLog x = Real.log x := by
  by_cases hx : x = 0
  · subst x
    simp only [chapter9BoundaryLog, ite_true]
    exact Real.log_zero.symm
  · simp only [chapter9BoundaryLog, hx, ite_false]

/-- **The Entry 26 and Entry 24 dilogarithm cosine terms agree.** For all real $\rho$ and
$\alpha$ and every natural number $j$, the $j$-th term $\rho^{j+1} \cos((j+1)\alpha) / (j+1)^2$ of
the dilogarithm cosine series defined for Entry 26 equals the $j$-th term of the cosine series
defined for Entry 24, which is given by the same formula. -/
theorem chapter9DilogCosTerm_eq_entry24 (rho angle : ℝ) (j : ℕ) :
    chapter9DilogCosTerm rho angle j =
      Entry24Dougall.chapter9DilogCosTerm rho angle j := rfl

/-- **The Entry 26 and Entry 24 dilogarithm sine terms agree.** For all real $\rho$ and
$\alpha$ and every natural number $j$, the $j$-th term $\rho^{j+1} \sin((j+1)\alpha) / (j+1)^2$ of
the dilogarithm sine series defined for Entry 26 equals the $j$-th term of the sine series
defined for Entry 24, which is given by the same formula. -/
theorem chapter9DilogSinTerm_eq_entry24 (rho angle : ℝ) (j : ℕ) :
    chapter9DilogSinTerm rho angle j =
      Entry24Dougall.chapter9DilogSinTerm rho angle j := rfl

private lemma chapter9DilogInvSqSummable :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (2 : ℕ))) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

private lemma chapter9OddInvSqSummable :
    Summable (fun j : ℕ => (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    have h2 : 2 * a + 1 = 2 * b + 1 := h
    omega
  have h := chapter9DilogInvSqSummable.comp_injective hinj
  simpa [Function.comp_def] using h

private lemma chapter9DilogCosNormBound (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (j : ℕ) :
    ‖chapter9DilogCosTerm rho angle (2 * j)‖ ≤
      (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hpos : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ)) := by
    have h2 : 0 < 2 * j + 1 := by omega
    exact_mod_cast h2
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have h1 : |rho| ^ (2 * j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  have h2 : |Real.cos ((((2 * j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hpos2 : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := pow_pos hpos 2
  have hnum : |rho| ^ (2 * j + 1) *
      |Real.cos ((((2 * j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := by
    calc |rho| ^ (2 * j + 1) * |Real.cos ((((2 * j + 1 : ℕ) : ℝ)) * angle)|
        ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [Real.norm_eq_abs]
  simp only [chapter9DilogCosTerm]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos2, div_eq_mul_inv]
  calc |rho| ^ (2 * j + 1) * |Real.cos (↑(2 * j + 1) * angle)| * (↑(2 * j + 1) ^ 2)⁻¹
      ≤ 1 * (↑(2 * j + 1) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hpos2))
    _ = 1 / ↑(2 * j + 1) ^ 2 := by rw [one_div, one_mul]

private lemma chapter9DilogSinNormBound (rho angle : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (j : ℕ) :
    ‖chapter9DilogSinTerm rho angle (2 * j)‖ ≤
      (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hpos : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ)) := by
    have h2 : 0 < 2 * j + 1 := by omega
    exact_mod_cast h2
  have habs : |rho| ≤ 1 := abs_le.mpr ⟨by linarith, hrho1⟩
  have h1 : |rho| ^ (2 * j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  have h2 : |Real.sin ((((2 * j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hpos2 : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := pow_pos hpos 2
  have hnum : |rho| ^ (2 * j + 1) *
      |Real.sin ((((2 * j + 1 : ℕ) : ℝ)) * angle)| ≤ 1 := by
    calc |rho| ^ (2 * j + 1) * |Real.sin ((((2 * j + 1 : ℕ) : ℝ)) * angle)|
        ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  rw [Real.norm_eq_abs]
  simp only [chapter9DilogSinTerm]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hpos2, div_eq_mul_inv]
  calc |rho| ^ (2 * j + 1) * |Real.sin (↑(2 * j + 1) * angle)| * (↑(2 * j + 1) ^ 2)⁻¹
      ≤ 1 * (↑(2 * j + 1) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hpos2))
    _ = 1 / ↑(2 * j + 1) ^ 2 := by rw [one_div, one_mul]

private lemma chapter9DilogCosOddSummable (rho angle : ℝ) (hrho0 : 0 ≤ rho)
    (hrho1 : rho ≤ 1) :
    Summable (fun j : ℕ => chapter9DilogCosTerm rho angle (2 * j)) :=
  Summable.of_norm_bounded chapter9OddInvSqSummable
    (chapter9DilogCosNormBound rho angle hrho0 hrho1)

private lemma chapter9DilogSinOddSummable (rho angle : ℝ) (hrho0 : 0 ≤ rho)
    (hrho1 : rho ≤ 1) :
    Summable (fun j : ℕ => chapter9DilogSinTerm rho angle (2 * j)) :=
  Summable.of_norm_bounded chapter9OddInvSqSummable
    (chapter9DilogSinNormBound rho angle hrho0 hrho1)

private lemma chapter9EvenInvSqSummable :
    Summable (fun k : ℕ => (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ (2 : ℕ))) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    have h2 : 2 * a = 2 * b := h
    omega
  have h := chapter9DilogInvSqSummable.comp_injective hinj
  simpa only [Function.comp_def] using h

private lemma chapter9EvenTsumEq :
    (∑' k : ℕ, (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ (2 : ℕ))) =
      (1 / 4 : ℝ) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) := by
  have hterm : ∀ k : ℕ,
      (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ (2 : ℕ)) =
        (1 / 4 : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      norm_num
    · have hkpos : (0 : ℝ) < (k : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have h2k : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by
        push_cast
        ring
      rw [h2k]
      field_simp
      ring
  simp only [hterm]
  rw [tsum_mul_left]

private lemma chapter9OddZetaTwo :
    (∑' j : ℕ, (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
      Real.pi ^ 2 / 8 := by
  have hz_eq : (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  have hsplit :
      (∑' k : ℕ, (1 : ℝ) / (((2 * k : ℕ) : ℝ) ^ (2 : ℕ))) +
        (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
        ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
    have h := tsum_even_add_odd
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
      chapter9EvenInvSqSummable chapter9OddInvSqSummable
    simpa only using h
  have heven := chapter9EvenTsumEq
  rw [hz_eq] at hsplit
  rw [heven, hz_eq] at hsplit
  linarith [Real.pi_pos]

private lemma chapter9UnitExpImpOne (y phi : ℝ) (hy0 : 0 ≤ y)
    (hY : (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) = 1) : y = 1 := by
  have hnorm : ‖(y : ℂ) * Complex.exp (Complex.I * (phi : ℂ))‖ = 1 := by
    rw [hY, norm_one]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0,
    Complex.norm_exp_I_mul_ofReal, mul_one] at hnorm
  exact hnorm

private lemma chapter9ExpEqOneImpAngleZero (phi : ℝ)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hExp : Complex.exp (Complex.I * (phi : ℂ)) = 1) : phi = 0 := by
  have hre : (Complex.exp (Complex.I * (phi : ℂ))).re = (1 : ℂ).re :=
    congrArg Complex.re hExp
  have hcomm : Complex.I * (phi : ℂ) = (phi : ℂ) * Complex.I :=
    mul_comm _ _
  rw [hcomm, Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
  have h1 : -(2 * Real.pi) < phi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have h2 : phi < 2 * Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  exact (Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hre

private lemma chapter9CosTermZero (theta : ℝ) (j : ℕ) :
    chapter9DilogCosTerm 0 theta (2 * j) = 0 := by
  simp only [chapter9DilogCosTerm]
  have hk : 2 * j + 1 ≠ 0 := by omega
  rw [zero_pow hk, zero_mul, zero_div]

private lemma chapter9SinTermZero (theta : ℝ) (j : ℕ) :
    chapter9DilogSinTerm 0 theta (2 * j) = 0 := by
  simp only [chapter9DilogSinTerm]
  have hk : 2 * j + 1 ≠ 0 := by omega
  rw [zero_pow hk, zero_mul, zero_div]

private lemma chapter9CosTermOneZero (j : ℕ) :
    chapter9DilogCosTerm 1 0 (2 * j) =
      (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  simp only [chapter9DilogCosTerm]
  have hcos : Real.cos ((((2 * j + 1 : ℕ) : ℝ)) * 0) = 1 := by
    rw [mul_zero, Real.cos_zero]
  rw [hcos, one_pow, one_mul]

private lemma chapter9SinTermOneZero (j : ℕ) :
    chapter9DilogSinTerm 1 0 (2 * j) = 0 := by
  simp only [chapter9DilogSinTerm]
  have hsin : Real.sin ((((2 * j + 1 : ℕ) : ℝ)) * 0) = 0 := by
    rw [mul_zero, Real.sin_zero]
  rw [hsin, mul_zero, zero_div]

private lemma chapter9CosTsumZero (theta : ℝ) :
    (∑' j : ℕ, chapter9DilogCosTerm 0 theta (2 * j)) = 0 := by
  have h : ∀ j : ℕ, chapter9DilogCosTerm 0 theta (2 * j) = 0 :=
    fun j => chapter9CosTermZero theta j
  rw [tsum_congr h, tsum_zero]

private lemma chapter9SinTsumZero (theta : ℝ) :
    (∑' j : ℕ, chapter9DilogSinTerm 0 theta (2 * j)) = 0 := by
  have h : ∀ j : ℕ, chapter9DilogSinTerm 0 theta (2 * j) = 0 :=
    fun j => chapter9SinTermZero theta j
  rw [tsum_congr h, tsum_zero]

private lemma chapter9CosTsumOneZero :
    (∑' j : ℕ, chapter9DilogCosTerm 1 0 (2 * j)) = Real.pi ^ 2 / 8 := by
  have h : ∀ j : ℕ, chapter9DilogCosTerm 1 0 (2 * j) =
      (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
    fun j => chapter9CosTermOneZero j
  rw [tsum_congr h]
  exact chapter9OddZetaTwo

private lemma chapter9SinTsumOneZero :
    (∑' j : ℕ, chapter9DilogSinTerm 1 0 (2 * j)) = 0 := by
  have h : ∀ j : ℕ, chapter9DilogSinTerm 1 0 (2 * j) = 0 :=
    fun j => chapter9SinTermOneZero j
  rw [tsum_congr h, tsum_zero]

private lemma chapter9BoundaryLogZero : chapter9BoundaryLog 0 = 0 := by
  simp only [chapter9BoundaryLog, ite_true]

private lemma chapter9BoundaryLogOne : chapter9BoundaryLog 1 = 0 := by
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  simp only [chapter9BoundaryLog, h1, ite_false, Real.log_one]

private lemma chapter9CosEqZeroLeft (x y theta phi : ℝ) (hy0 : 0 ≤ y)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hx : x = 0) :
    (∑' j : ℕ, chapter9DilogCosTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogCosTerm y phi (2 * j)) =
      Real.pi ^ 2 / 8 -
        (1 / 2 : ℝ) * chapter9BoundaryLog x * chapter9BoundaryLog y +
        (1 / 2 : ℝ) * theta * phi := by
  subst hx
  simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero] at hrelation
  have hy1 : y = 1 := chapter9UnitExpImpOne y phi hy0 hrelation
  subst hy1
  have hExp : Complex.exp (Complex.I * (phi : ℂ)) = 1 := by
    simpa only [Complex.ofReal_one, one_mul] using hrelation
  have hphi : phi = 0 := chapter9ExpEqOneImpAngleZero phi hphi0 hphi1 hExp
  subst hphi
  rw [chapter9CosTsumZero, chapter9CosTsumOneZero, chapter9BoundaryLogZero,
    chapter9BoundaryLogOne]
  ring

private lemma chapter9SinEqZeroLeft (x y theta phi : ℝ) (hy0 : 0 ≤ y)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hx : x = 0) :
    (∑' j : ℕ, chapter9DilogSinTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogSinTerm y phi (2 * j)) =
      -(1 / 2 : ℝ) * phi * chapter9BoundaryLog x -
        (1 / 2 : ℝ) * theta * chapter9BoundaryLog y := by
  subst hx
  simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero] at hrelation
  have hy1 : y = 1 := chapter9UnitExpImpOne y phi hy0 hrelation
  subst hy1
  have hExp : Complex.exp (Complex.I * (phi : ℂ)) = 1 := by
    simpa only [Complex.ofReal_one, one_mul] using hrelation
  have hphi : phi = 0 := chapter9ExpEqOneImpAngleZero phi hphi0 hphi1 hExp
  subst hphi
  rw [chapter9SinTsumZero, chapter9SinTsumOneZero, chapter9BoundaryLogZero,
    chapter9BoundaryLogOne]
  ring

private lemma chapter9CosEqZeroRight (x y theta phi : ℝ) (hx0 : 0 ≤ x)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hy : y = 0) :
    (∑' j : ℕ, chapter9DilogCosTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogCosTerm y phi (2 * j)) =
      Real.pi ^ 2 / 8 -
        (1 / 2 : ℝ) * chapter9BoundaryLog x * chapter9BoundaryLog y +
        (1 / 2 : ℝ) * theta * phi := by
  subst hy
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero] at hrelation
  have hx1 : x = 1 := chapter9UnitExpImpOne x theta hx0 hrelation
  subst hx1
  have hExp : Complex.exp (Complex.I * (theta : ℂ)) = 1 := by
    simpa only [Complex.ofReal_one, one_mul] using hrelation
  have htheta : theta = 0 :=
    chapter9ExpEqOneImpAngleZero theta htheta0 htheta1 hExp
  subst htheta
  rw [chapter9CosTsumOneZero, chapter9CosTsumZero, chapter9BoundaryLogOne,
    chapter9BoundaryLogZero]
  ring

private lemma chapter9SinEqZeroRight (x y theta phi : ℝ) (hx0 : 0 ≤ x)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hy : y = 0) :
    (∑' j : ℕ, chapter9DilogSinTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogSinTerm y phi (2 * j)) =
      -(1 / 2 : ℝ) * phi * chapter9BoundaryLog x -
        (1 / 2 : ℝ) * theta * chapter9BoundaryLog y := by
  subst hy
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero] at hrelation
  have hx1 : x = 1 := chapter9UnitExpImpOne x theta hx0 hrelation
  subst hx1
  have hExp : Complex.exp (Complex.I * (theta : ℂ)) = 1 := by
    simpa only [Complex.ofReal_one, one_mul] using hrelation
  have htheta : theta = 0 :=
    chapter9ExpEqOneImpAngleZero theta htheta0 htheta1 hExp
  subst htheta
  rw [chapter9SinTsumOneZero, chapter9SinTsumZero, chapter9BoundaryLogOne,
    chapter9BoundaryLogZero]
  ring

private def chapter9ComplexOddDilogTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ) ^ 2)

private def chapter9ComplexOddDilog (z : ℂ) : ℂ :=
  ∑' j : ℕ, chapter9ComplexOddDilogTerm z j

private lemma chapter9ComplexOddDilogNormBound (z : ℂ) (hz : ‖z‖ ≤ 1)
    (j : ℕ) :
    ‖chapter9ComplexOddDilogTerm z j‖ ≤
      (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by
    have h2 : 0 < 2 * j + 1 := by omega
    exact_mod_cast h2
  have hnorm : ‖z ^ (2 * j + 1)‖ ≤ 1 := by
    calc ‖z ^ (2 * j + 1)‖ = ‖z‖ ^ (2 * j + 1) := norm_pow _ _
      _ ≤ 1 ^ (2 * j + 1) := by
        apply pow_le_pow_left₀ (norm_nonneg _) hz
      _ = 1 := one_pow _
  have hden : ‖((((2 * j + 1 : ℕ)) : ℂ) ^ 2)‖ = (((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
    rw [norm_pow]
    congr 1
    rw [Complex.norm_natCast]
  rw [chapter9ComplexOddDilogTerm, norm_div, hden]
  have hdenpos : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ) ^ 2) := by positivity
  calc ‖z ^ (2 * j + 1)‖ / (((2 * j + 1 : ℕ) : ℝ) ^ 2)
      ≤ 1 / (((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right hnorm (le_of_lt hdenpos)
    _ = 1 / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by norm_num

private lemma chapter9ComplexOddDilogSummable (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (chapter9ComplexOddDilogTerm z) :=
  Summable.of_norm_bounded chapter9OddInvSqSummable
    (chapter9ComplexOddDilogNormBound z hz)

private lemma chapter9ComplexOddDilogTermContinuous (j : ℕ) :
    Continuous (fun z : ℂ => chapter9ComplexOddDilogTerm z j) := by
  simp only [chapter9ComplexOddDilogTerm]
  have hne : ((((2 * j + 1 : ℕ)) : ℂ) ^ 2) ≠ 0 := by
    apply pow_ne_zero 2
    exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  exact continuous_pow _ |>.div_const _

private lemma chapter9ComplexOddDilogContinuousOn :
    ContinuousOn chapter9ComplexOddDilog (Metric.closedBall 0 1) := by
  have hcont : ∀ j : ℕ,
      ContinuousOn (fun z : ℂ => chapter9ComplexOddDilogTerm z j)
        (Metric.closedBall 0 1) :=
    fun j => (chapter9ComplexOddDilogTermContinuous j).continuousOn
  have hbound : ∀ j : ℕ, ∀ z : ℂ, z ∈ Metric.closedBall 0 1 →
      ‖chapter9ComplexOddDilogTerm z j‖ ≤
        (1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    intro j z hz
    have hnorm : ‖z‖ ≤ 1 := by
      have hdist : dist z 0 ≤ 1 := Metric.mem_closedBall.mp hz
      rwa [dist_zero_right] at hdist
    exact chapter9ComplexOddDilogNormBound z hnorm j
  exact continuousOn_tsum hcont chapter9OddInvSqSummable hbound

private lemma chapter9ComplexOddDilogZero : chapter9ComplexOddDilog 0 = 0 := by
  have h : ∀ j : ℕ, chapter9ComplexOddDilogTerm 0 j = 0 := by
    intro j
    simp only [chapter9ComplexOddDilogTerm]
    have hk : 2 * j + 1 ≠ 0 := by omega
    rw [zero_pow hk, zero_div]
  simp only [chapter9ComplexOddDilog, h, tsum_zero]

private lemma chapter9ComplexOddDilogOne :
    chapter9ComplexOddDilog 1 = ((Real.pi ^ 2 / 8 : ℝ) : ℂ) := by
  have hterm : ∀ j : ℕ, chapter9ComplexOddDilogTerm 1 j =
      ((((1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) := by
    intro j
    simp only [chapter9ComplexOddDilogTerm, one_pow]
    push_cast
    ring_nf
  have htsum : (∑' j : ℕ, chapter9ComplexOddDilogTerm 1 j) =
      ∑' j : ℕ, ((((1 : ℝ) / (((2 * j + 1 : ℕ) : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) :=
    tsum_congr hterm
  rw [chapter9ComplexOddDilog, htsum, ← Complex.ofReal_tsum, chapter9OddZetaTwo]

private def chapter9ComplexLogTerm (z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) / (((n + 1 : ℕ)) : ℂ)

private def chapter9ComplexLogSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, chapter9ComplexLogTerm z n

private lemma chapter9ComplexLogSeriesSummable (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (chapter9ComplexLogTerm z) := by
  have hgeom : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) := by
    have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    have h1 := summable_geometric_of_lt_one h0 hz
    have hshift : (fun n : ℕ => ‖z‖ ^ (n + 1)) = fun n : ℕ => ‖z‖ * (‖z‖ ^ n) := by
      funext n
      rw [pow_succ']
    rw [hshift]
    exact h1.mul_left _
  apply Summable.of_norm_bounded hgeom
  intro n
  simp only [chapter9ComplexLogTerm]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    have h2 : 0 < n + 1 := by omega
    exact_mod_cast h2
  have hden : ‖((((n + 1 : ℕ)) : ℂ))‖ = ((n + 1 : ℕ) : ℝ) := Complex.norm_natCast _
  rw [norm_div, norm_pow, hden]
  have hle : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have h3 : 1 ≤ n + 1 := by omega
      exact_mod_cast h3
    exact h2
  calc ‖z‖ ^ (n + 1) / ((n + 1 : ℕ) : ℝ)
      = ‖z‖ ^ (n + 1) * (1 / ((n + 1 : ℕ) : ℝ)) := by rw [div_eq_mul_one_div]
    _ ≤ ‖z‖ ^ (n + 1) * 1 := by
        apply mul_le_mul_of_nonneg_left hle (pow_nonneg (norm_nonneg _) _)
    _ = ‖z‖ ^ (n + 1) := mul_one _

private lemma chapter9LogTermHasDerivAt (n : ℕ) (y : ℂ) :
    HasDerivAt (fun z : ℂ => chapter9ComplexLogTerm z n) (y ^ n) y := by
  have hne : ((((n + 1 : ℕ)) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hpow : HasDerivAt (fun z : ℂ => z ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * y ^ n) y :=
    hasDerivAt_pow (n + 1) y
  have hdiv := hpow.div_const ((((n + 1 : ℕ)) : ℂ))
  have heq : (((n + 1 : ℕ) : ℂ) * y ^ n) / (((n + 1 : ℕ)) : ℂ) = y ^ n := by
    field_simp
  rw [heq] at hdiv
  simpa only [chapter9ComplexLogTerm, div_eq_mul_inv] using hdiv

private lemma chapter9LogSeriesHasDerivAt (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) :
    HasDerivAt chapter9ComplexLogSeries ((1 - z₀)⁻¹) z₀ := by
  set R : ℝ := (‖z₀‖ + 1) / 2 with hR
  have hRlt : R < 1 := by
    simp only [hR]
    linarith
  have hzR : ‖z₀‖ < R := by
    simp only [hR]
    linarith
  have hRnonneg : (0 : ℝ) ≤ R := by
    have h0 : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg _
    simp only [hR]
    linarith
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt (norm_nonneg _) hzR
  have hu : Summable (fun n : ℕ => R ^ n) :=
    summable_geometric_of_lt_one hRnonneg hRlt
  have ht : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have h't : IsPreconnected (Metric.ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).isPreconnected
  have hg : ∀ n : ℕ, ∀ y : ℂ, y ∈ Metric.ball (0 : ℂ) R →
      HasDerivAt (fun z : ℂ => chapter9ComplexLogTerm z n) (y ^ n) y :=
    fun n y _ => chapter9LogTermHasDerivAt n y
  have hg' : ∀ n : ℕ, ∀ y : ℂ, y ∈ Metric.ball (0 : ℂ) R → ‖y ^ n‖ ≤ R ^ n := by
    intro n y hy
    have hynorm : ‖y‖ < R := by
      have hdist : dist y 0 < R := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at hdist
    calc ‖y ^ n‖ = ‖y‖ ^ n := norm_pow _ _
      _ ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hynorm) n
  have hy₀ : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hRpos
  have hg0 : Summable (fun n : ℕ => chapter9ComplexLogTerm 0 n) := by
    have h0 : ∀ n : ℕ, chapter9ComplexLogTerm 0 n = 0 := by
      intro n
      simp only [chapter9ComplexLogTerm]
      have hk : n + 1 ≠ 0 := by omega
      rw [zero_pow hk, zero_div]
    have heq : (fun n : ℕ => chapter9ComplexLogTerm 0 n) = fun _ => 0 :=
      funext h0
    rw [heq]
    exact summable_zero
  have hy : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzR
  have hderiv := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => R ^ n)
    hu ht h't hg hg' hy₀ hg0 hy
  have hgeom : (∑' n : ℕ, z₀ ^ n) = (1 - z₀)⁻¹ :=
    (hasSum_geometric_of_norm_lt_one hz₀).tsum_eq
  rw [hgeom] at hderiv
  exact hderiv

private lemma chapter9OneSubMemSlitPlane (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hre : (1 - z).re = 1 - z.re := by
    simp only [Complex.sub_re, Complex.one_re]
  rw [hre]
  have hle : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

private lemma chapter9NegLogOneSubHasDerivAt (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) :
    HasDerivAt (fun z : ℂ => -Complex.log (1 - z)) ((1 - z₀)⁻¹) z₀ := by
  have hmem : (1 - z₀) ∈ Complex.slitPlane :=
    chapter9OneSubMemSlitPlane z₀ hz₀
  have h1 : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) z₀ :=
    (hasDerivAt_id' z₀).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => Complex.log (1 - z)) ((-1) / (1 - z₀)) z₀ :=
    h1.clog hmem
  have h3 : HasDerivAt (fun z : ℂ => -Complex.log (1 - z)) (-((-1) / (1 - z₀))) z₀ :=
    h2.neg
  have heq : -((-1) / (1 - z₀)) = (1 - z₀)⁻¹ := by
    simp only [neg_div, neg_neg, one_div]
  rw [heq] at h3
  exact h3

private lemma chapter9LogSeriesEqNegLog (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1) :
    chapter9ComplexLogSeries z₀ = -Complex.log (1 - z₀) := by
  have hs : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hs' : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).isPreconnected
  have hmem : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) 1 ↔ ‖z‖ < 1 := by
    intro z
    rw [Metric.mem_ball, dist_zero_right]
  have hf : DifferentiableOn ℂ chapter9ComplexLogSeries (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hznorm : ‖z‖ < 1 := (hmem z).mp hz
    exact (chapter9LogSeriesHasDerivAt z hznorm).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z : ℂ => -Complex.log (1 - z))
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hznorm : ‖z‖ < 1 := (hmem z).mp hz
    exact (chapter9NegLogOneSubHasDerivAt z hznorm).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv chapter9ComplexLogSeries)
      (deriv (fun z : ℂ => -Complex.log (1 - z))) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hznorm : ‖z‖ < 1 := (hmem z).mp hz
    have h1 := (chapter9LogSeriesHasDerivAt z hznorm).deriv
    have h2 := (chapter9NegLogOneSubHasDerivAt z hznorm).deriv
    rw [h1, h2]
  have hx0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
  have hfg0 : chapter9ComplexLogSeries 0 = -Complex.log (1 - (0 : ℂ)) := by
    have hT0 : chapter9ComplexLogSeries 0 = 0 := by
      have h0 : ∀ n : ℕ, chapter9ComplexLogTerm 0 n = 0 := by
        intro n
        simp only [chapter9ComplexLogTerm]
        have hk : n + 1 ≠ 0 := by omega
        rw [zero_pow hk, zero_div]
      simp only [chapter9ComplexLogSeries, h0, tsum_zero]
    rw [hT0]
    simp only [sub_zero, Complex.log_one, neg_zero]
  have heq := IsOpen.eqOn_of_deriv_eq hs hs' hf hg hderiv hx0 hfg0
  have hzmem : z₀ ∈ Metric.ball (0 : ℂ) 1 := (hmem z₀).mpr hz₀
  exact heq hzmem

private def chapter9ComplexOddLogTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ))

private def chapter9ComplexOddLogSeries (z : ℂ) : ℂ :=
  ∑' j : ℕ, chapter9ComplexOddLogTerm z j

private lemma chapter9OddLogSeriesEq (z : ℂ) (hz : ‖z‖ < 1) :
    chapter9ComplexOddLogSeries z =
      (chapter9ComplexLogSeries z - chapter9ComplexLogSeries (-z)) / 2 := by
  have hneg : ‖-z‖ < 1 := by rwa [norm_neg]
  have hTz := chapter9ComplexLogSeriesSummable z hz
  have hTnz := chapter9ComplexLogSeriesSummable (-z) hneg
  have hsub : Summable (fun n : ℕ =>
      chapter9ComplexLogTerm z n - chapter9ComplexLogTerm (-z) n) :=
    hTz.sub hTnz
  have htsum : (∑' n : ℕ, (chapter9ComplexLogTerm z n -
      chapter9ComplexLogTerm (-z) n)) =
      chapter9ComplexLogSeries z - chapter9ComplexLogSeries (-z) := by
    simp only [chapter9ComplexLogSeries]
    exact hTz.tsum_sub hTnz
  have hinj_even : Function.Injective (fun j : ℕ => 2 * j) := by
    intro a b h
    have h2 : 2 * a = 2 * b := h
    omega
  have hinj_odd : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    have h2 : 2 * a + 1 = 2 * b + 1 := h
    omega
  have heven : Summable (fun j : ℕ => (chapter9ComplexLogTerm z (2 * j) -
      chapter9ComplexLogTerm (-z) (2 * j))) :=
    hsub.comp_injective hinj_even
  have hodd : Summable (fun j : ℕ => (chapter9ComplexLogTerm z (2 * j + 1) -
      chapter9ComplexLogTerm (-z) (2 * j + 1))) :=
    hsub.comp_injective hinj_odd
  have hsplit := tsum_even_add_odd (f := fun n : ℕ =>
      chapter9ComplexLogTerm z n - chapter9ComplexLogTerm (-z) n) heven hodd
  have hodd_zero : (∑' j : ℕ, (chapter9ComplexLogTerm z (2 * j + 1) -
      chapter9ComplexLogTerm (-z) (2 * j + 1))) = 0 := by
    have h0 : ∀ j : ℕ, (chapter9ComplexLogTerm z (2 * j + 1) -
        chapter9ComplexLogTerm (-z) (2 * j + 1)) = 0 := by
      intro j
      simp only [chapter9ComplexLogTerm]
      have hev : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
      have hpow : (-z) ^ (2 * j + 1 + 1) = z ^ (2 * j + 1 + 1) :=
        hev.neg_pow z
      rw [hpow, sub_self]
    rw [tsum_congr h0, tsum_zero]
  have heven_eq : (∑' j : ℕ, (chapter9ComplexLogTerm z (2 * j) -
      chapter9ComplexLogTerm (-z) (2 * j))) =
      2 * chapter9ComplexOddLogSeries z := by
    have hterm : ∀ j : ℕ, (chapter9ComplexLogTerm z (2 * j) -
        chapter9ComplexLogTerm (-z) (2 * j)) =
        2 * chapter9ComplexOddLogTerm z j := by
      intro j
      simp only [chapter9ComplexLogTerm, chapter9ComplexOddLogTerm]
      have hodd_pow : Odd (2 * j + 1) := ⟨j, rfl⟩
      have hpow : (-z) ^ (2 * j + 1) = -(z ^ (2 * j + 1)) :=
        hodd_pow.neg_pow z
      calc z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ)) -
            (-z) ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ))
          = z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ)) -
            (-(z ^ (2 * j + 1))) / ((((2 * j + 1 : ℕ)) : ℂ)) := by rw [hpow]
        _ = 2 * (z ^ (2 * j + 1) / ((((2 * j + 1 : ℕ)) : ℂ))) := by
            field_simp
            ring
    rw [tsum_congr hterm, tsum_mul_left]
    simp only [chapter9ComplexOddLogSeries]
  rw [hodd_zero, heven_eq, add_zero] at hsplit
  rw [htsum] at hsplit
  calc chapter9ComplexOddLogSeries z
      = (2 * chapter9ComplexOddLogSeries z) / 2 := by field_simp
    _ = (chapter9ComplexLogSeries z - chapter9ComplexLogSeries (-z)) / 2 := by
        rw [← hsplit]

private lemma chapter9OddLogSeriesEqLog (z : ℂ) (hz : ‖z‖ < 1) :
    chapter9ComplexOddLogSeries z =
      (Complex.log (1 + z) - Complex.log (1 - z)) / 2 := by
  have hneg : ‖-z‖ < 1 := by rwa [norm_neg]
  have hTz := chapter9LogSeriesEqNegLog z hz
  have hTnz := chapter9LogSeriesEqNegLog (-z) hneg
  have hO := chapter9OddLogSeriesEq z hz
  have h1 : (1 : ℂ) - (-z) = 1 + z := by ring
  rw [hTz, hTnz, h1] at hO
  calc chapter9ComplexOddLogSeries z
      = (-Complex.log (1 - z) - -Complex.log (1 + z)) / 2 := hO
    _ = (Complex.log (1 + z) - Complex.log (1 - z)) / 2 := by ring

private lemma chapter9DilogTermHasDerivAt (j : ℕ) (y : ℂ) :
    HasDerivAt (fun z : ℂ => chapter9ComplexOddDilogTerm z j)
      (y ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) y := by
  have hne : ((((2 * j + 1 : ℕ)) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  have hne2 : ((((2 * j + 1 : ℕ)) : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 hne
  have hpow : HasDerivAt (fun z : ℂ => z ^ (2 * j + 1))
      ((((2 * j + 1 : ℕ)) : ℂ) * y ^ (2 * j)) y := by
    have h := hasDerivAt_pow (2 * j + 1) y
    have heq : (2 * j + 1 - 1) = 2 * j := by omega
    rw [heq] at h
    exact h
  have hdiv := hpow.div_const ((((2 * j + 1 : ℕ)) : ℂ) ^ 2)
  have heq : ((((2 * j + 1 : ℕ)) : ℂ) * y ^ (2 * j)) /
      ((((2 * j + 1 : ℕ)) : ℂ) ^ 2) =
      y ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ)) := by
    field_simp
  rw [heq] at hdiv
  simpa only [chapter9ComplexOddDilogTerm, div_eq_mul_inv] using hdiv

private lemma chapter9DilogHasDerivAt (z₀ : ℂ) (hz₀ : ‖z₀‖ < 1)
    (hzne : z₀ ≠ 0) :
    HasDerivAt chapter9ComplexOddDilog
      (chapter9ComplexOddLogSeries z₀ / z₀) z₀ := by
  set R : ℝ := (‖z₀‖ + 1) / 2 with hR
  have hRlt : R < 1 := by
    simp only [hR]
    linarith
  have hzR : ‖z₀‖ < R := by
    simp only [hR]
    linarith
  have hRnonneg : (0 : ℝ) ≤ R := by
    have h0 : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg _
    simp only [hR]
    linarith
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt (norm_nonneg _) hzR
  have hsq : R ^ 2 < 1 := by
    nlinarith [sq_nonneg (R - 1), sq_nonneg R, hRnonneg, hRlt]
  have hsq0 : (0 : ℝ) ≤ R ^ 2 := pow_nonneg hRnonneg 2
  have hgeom : Summable (fun j : ℕ => (R ^ 2) ^ j) :=
    summable_geometric_of_lt_one hsq0 hsq
  have hu : Summable (fun j : ℕ => R ^ (2 * j)) := by
    have heq : (fun j : ℕ => R ^ (2 * j)) = fun j : ℕ => (R ^ 2) ^ j := by
      funext j
      rw [pow_mul]
    rw [heq]
    exact hgeom
  have ht : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have h't : IsPreconnected (Metric.ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).isPreconnected
  have hg : ∀ j : ℕ, ∀ y : ℂ, y ∈ Metric.ball (0 : ℂ) R →
      HasDerivAt (fun z : ℂ => chapter9ComplexOddDilogTerm z j)
        (y ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) y :=
    fun j y _ => chapter9DilogTermHasDerivAt j y
  have hg' : ∀ j : ℕ, ∀ y : ℂ, y ∈ Metric.ball (0 : ℂ) R →
      ‖y ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))‖ ≤ R ^ (2 * j) := by
    intro j y hy
    have hynorm : ‖y‖ < R := by
      have hdist : dist y 0 < R := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at hdist
    have hle_pow : ‖y‖ ^ (2 * j) ≤ R ^ (2 * j) :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hynorm) _
    have hpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by
      have h2 : 0 < 2 * j + 1 := by omega
      exact_mod_cast h2
    have hden : ‖((((2 * j + 1 : ℕ)) : ℂ))‖ = ((2 * j + 1 : ℕ) : ℝ) :=
      Complex.norm_natCast _
    have hle_one : (1 : ℝ) / ((2 * j + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpos]
      have h2 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
        have h3 : 1 ≤ 2 * j + 1 := by omega
        exact_mod_cast h3
      exact h2
    calc ‖y ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))‖
        = ‖y‖ ^ (2 * j) / ((2 * j + 1 : ℕ) : ℝ) := by
          rw [norm_div, norm_pow, hden]
      _ = ‖y‖ ^ (2 * j) * (1 / ((2 * j + 1 : ℕ) : ℝ)) := by
          rw [div_eq_mul_one_div]
      _ ≤ ‖y‖ ^ (2 * j) * 1 := by
          apply mul_le_mul_of_nonneg_left hle_one (pow_nonneg (norm_nonneg _) _)
      _ = ‖y‖ ^ (2 * j) := mul_one _
      _ ≤ R ^ (2 * j) := hle_pow
  have hy₀ : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hRpos
  have hg0 : Summable (fun j : ℕ => chapter9ComplexOddDilogTerm 0 j) := by
    have h0 : ∀ j : ℕ, chapter9ComplexOddDilogTerm 0 j = 0 := by
      intro j
      simp only [chapter9ComplexOddDilogTerm]
      have hk : 2 * j + 1 ≠ 0 := by omega
      rw [zero_pow hk, zero_div]
    have heq : (fun j : ℕ => chapter9ComplexOddDilogTerm 0 j) = fun _ => 0 :=
      funext h0
    rw [heq]
    exact summable_zero
  have hy : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hzR
  have hderiv := hasDerivAt_tsum_of_isPreconnected (u := fun j : ℕ => R ^ (2 * j))
    hu ht h't hg hg' hy₀ hg0 hy
  have hO : chapter9ComplexOddLogSeries z₀ =
      z₀ * (∑' j : ℕ, z₀ ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) := by
    have hterm : ∀ j : ℕ, chapter9ComplexOddLogTerm z₀ j =
        z₀ * (z₀ ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) := by
      intro j
      simp only [chapter9ComplexOddLogTerm]
      have hpow : z₀ ^ (2 * j + 1) = z₀ * z₀ ^ (2 * j) :=
        pow_succ' _ _
      rw [hpow, mul_div_assoc]
    calc chapter9ComplexOddLogSeries z₀
        = ∑' j : ℕ, z₀ * (z₀ ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) := by
          simp only [chapter9ComplexOddLogSeries, hterm]
      _ = z₀ * (∑' j : ℕ, z₀ ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) := by
          rw [tsum_mul_left]
  have hD : (∑' j : ℕ, z₀ ^ (2 * j) / ((((2 * j + 1 : ℕ)) : ℂ))) =
      chapter9ComplexOddLogSeries z₀ / z₀ := by
    rw [hO]
    field_simp
  rw [hD] at hderiv
  exact hderiv

private def chapter9MobiusW (z : ℂ) : ℂ := (1 - z) / (1 + z)

private lemma chapter9OneAddNeZero (z : ℂ) (hre : 0 < z.re) :
    (1 + z) ≠ 0 := by
  intro h
  have hre1 : (1 + z).re = 0 := by rw [h, Complex.zero_re]
  simp only [Complex.add_re, Complex.one_re] at hre1
  linarith

private lemma chapter9OneSubNeZero (z : ℂ) (hnorm : ‖z‖ < 1) :
    (1 - z) ≠ 0 := by
  have hmem := chapter9OneSubMemSlitPlane z hnorm
  exact Complex.slitPlane_ne_zero hmem

private lemma chapter9OneAddRePos (z : ℂ) (hre : 0 < z.re) :
    0 < (1 + z).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith

private lemma chapter9OneSubRePos (z : ℂ) (hz : ‖z‖ < 1) :
    0 < (1 - z).re := by
  have hre1 : (1 - z).re = 1 - z.re := by
    simp only [Complex.sub_re, Complex.one_re]
  have hle : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hlt : z.re < 1 := lt_of_le_of_lt hle hz
  rw [hre1]
  linarith

private lemma chapter9WNormLtOne (z : ℂ) (hre : 0 < z.re) :
    ‖chapter9MobiusW z‖ < 1 := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  simp only [chapter9MobiusW, norm_div]
  have hpos : (0 : ℝ) < ‖1 + z‖ := norm_pos_iff.mpr h1z
  rw [div_lt_one hpos]
  have hsq : ‖1 - z‖ < ‖1 + z‖ ↔
      Complex.normSq (1 - z) < Complex.normSq (1 + z) := by
    have h1 : ‖1 - z‖ ^ 2 = Complex.normSq (1 - z) := Complex.sq_norm _
    have h2 : ‖1 + z‖ ^ 2 = Complex.normSq (1 + z) := Complex.sq_norm _
    rw [← h1, ← h2]
    exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).symm
  rw [hsq]
  have hdiff : Complex.normSq (1 + z) - Complex.normSq (1 - z) = 4 * z.re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.add_im, Complex.sub_im, Complex.one_im]
    ring
  have hpos4 : (0 : ℝ) < 4 * z.re := by linarith
  linarith

private lemma chapter9WRePos (z : ℂ) (hz : ‖z‖ < 1) (hre : 0 < z.re) :
    0 < (chapter9MobiusW z).re := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  have hdenpos : (0 : ℝ) < Complex.normSq (1 + z) :=
    Complex.normSq_pos.mpr h1z
  have hnum : (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im =
      1 - Complex.normSq z := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im, Complex.normSq_apply]
    ring
  have hsq_lt : Complex.normSq z < 1 := by
    have h1 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
    rw [h1]
    have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    calc ‖z‖ ^ 2 < 1 ^ 2 := by
            exact pow_lt_pow_left₀ hz h0 (by norm_num : 2 ≠ 0)
      _ = 1 := one_pow 2
  have hnumpos : (0 : ℝ) < (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im := by
    rw [hnum]
    linarith
  have hre_eq : (chapter9MobiusW z).re =
      ((1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im) /
        Complex.normSq (1 + z) := by
    simp only [chapter9MobiusW, Complex.div_re, add_div]
  rw [hre_eq]
  exact div_pos hnumpos hdenpos

private lemma chapter9WNeZero (z : ℂ) (hz : ‖z‖ < 1) (hre : 0 < z.re) :
    chapter9MobiusW z ≠ 0 := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  have hnum : (1 - z) ≠ 0 := chapter9OneSubNeZero z hz
  simp only [chapter9MobiusW]
  exact div_ne_zero hnum h1z

private lemma chapter9OneAddW (z : ℂ) (hre : 0 < z.re) :
    1 + chapter9MobiusW z = 2 / (1 + z) := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  simp only [chapter9MobiusW]
  field_simp
  ring

private lemma chapter9OneSubW (z : ℂ) (hre : 0 < z.re) :
    1 - chapter9MobiusW z = 2 * z / (1 + z) := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  simp only [chapter9MobiusW]
  field_simp
  ring

private lemma chapter9ArgNePiOfRePos (z : ℂ) (hre : 0 < z.re) :
    z.arg ≠ Real.pi := by
  have habs : |z.arg| < Real.pi / 2 := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    exact h
  have hlt : z.arg < Real.pi := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have h1 : z.arg < Real.pi / 2 := (abs_lt.mp habs).2
    linarith
  exact ne_of_lt hlt

private lemma chapter9LogMulOfRePos (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hx
    exact lt_irrefl _ hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hy
    exact lt_irrefl _ hy
  have habsx : |x.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have habsy : |y.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxlo : -(Real.pi / 2) < x.arg := (abs_lt.mp habsx).1
  have hxhi : x.arg < Real.pi / 2 := (abs_lt.mp habsx).2
  have hylo : -(Real.pi / 2) < y.arg := (abs_lt.mp habsy).1
  have hyhi : y.arg < Real.pi / 2 := (abs_lt.mp habsy).2
  have hmem : x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith
    · linarith
  exact (Complex.log_mul_eq_add_log_iff hx0 hy0).mpr hmem

private lemma chapter9LogInvOfRePos (x : ℂ) (hx : 0 < x.re) :
    Complex.log x⁻¹ = -Complex.log x :=
  Complex.log_inv x (chapter9ArgNePiOfRePos x hx)

private lemma chapter9LogDivOfRePos (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x / y) = Complex.log x - Complex.log y := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hy
    exact lt_irrefl _ hy
  have hargy : y.arg ≠ Real.pi := chapter9ArgNePiOfRePos y hy
  have hinv_arg : (y⁻¹).arg = -y.arg := by
    rw [Complex.arg_inv, ite_eq_right hargy]
  have habsx : |x.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have habsy : |y.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxlo : -(Real.pi / 2) < x.arg := (abs_lt.mp habsx).1
  have hxhi : x.arg < Real.pi / 2 := (abs_lt.mp habsx).2
  have hylo : -(Real.pi / 2) < y.arg := (abs_lt.mp habsy).1
  have hyhi : y.arg < Real.pi / 2 := (abs_lt.mp habsy).2
  have hmem : x.arg + (y⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hinv_arg]
    constructor <;> linarith
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hx
    exact lt_irrefl _ hx
  have hinv0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hmul := (Complex.log_mul_eq_add_log_iff hx0 hinv0).mpr hmem
  have hinv := chapter9LogInvOfRePos y hy
  calc Complex.log (x / y)
      = Complex.log (x * y⁻¹) := by rw [div_eq_mul_inv]
    _ = Complex.log x + Complex.log y⁻¹ := hmul
    _ = Complex.log x - Complex.log y := by rw [hinv, sub_eq_add_neg]

private lemma chapter9TwoRePos : (0 : ℝ) < (2 : ℂ).re := by
  simp only [Complex.re_ofNat]
  norm_num

private lemma chapter9TwoMulRePos (z : ℂ) (hre : 0 < z.re) :
    (0 : ℝ) < (2 * z).re := by
  have heq : (2 * z).re = 2 * z.re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
  rw [heq]
  linarith

private lemma chapter9LogW (z : ℂ) (hz : ‖z‖ < 1) (hre : 0 < z.re) :
    Complex.log (chapter9MobiusW z) =
      Complex.log (1 - z) - Complex.log (1 + z) := by
  have h1m : (0 : ℝ) < (1 - z).re := chapter9OneSubRePos z hz
  have h1p : (0 : ℝ) < (1 + z).re := chapter9OneAddRePos z hre
  simp only [chapter9MobiusW]
  exact chapter9LogDivOfRePos _ _ h1m h1p

private lemma chapter9LogOneAddW (z : ℂ) (hre : 0 < z.re) :
    Complex.log (1 + chapter9MobiusW z) =
      Complex.log 2 - Complex.log (1 + z) := by
  have h2 : (0 : ℝ) < (2 : ℂ).re := chapter9TwoRePos
  have h1p : (0 : ℝ) < (1 + z).re := chapter9OneAddRePos z hre
  have hEq := chapter9OneAddW z hre
  rw [hEq]
  exact chapter9LogDivOfRePos _ _ h2 h1p

private lemma chapter9LogOneSubW (z : ℂ) (hre : 0 < z.re) :
    Complex.log (1 - chapter9MobiusW z) =
      Complex.log 2 + Complex.log z - Complex.log (1 + z) := by
  have h2 : (0 : ℝ) < (2 : ℂ).re := chapter9TwoRePos
  have h2z : (0 : ℝ) < (2 * z).re := chapter9TwoMulRePos z hre
  have h1p : (0 : ℝ) < (1 + z).re := chapter9OneAddRePos z hre
  have hEq := chapter9OneSubW z hre
  rw [hEq, chapter9LogDivOfRePos _ _ h2z h1p,
    chapter9LogMulOfRePos _ _ h2 hre]

private def chapter9F (z : ℂ) : ℂ :=
  chapter9ComplexOddDilog z + chapter9ComplexOddDilog (chapter9MobiusW z) +
    (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z)

private lemma chapter9WHasDerivAt (z : ℂ) (hre : 0 < z.re) :
    HasDerivAt chapter9MobiusW (-2 / (1 + z) ^ 2) z := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  have h1 : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) z :=
    (hasDerivAt_id' z).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => (1 : ℂ) + z) 1 z := by
    have h := (hasDerivAt_id' z).const_add 1
    simpa only [add_comm] using h
  have hdiv := h1.div h2 h1z
  have heq : (-1 * (1 + z) - (1 - z) * 1) / (1 + z) ^ 2 = -2 / (1 + z) ^ 2 := by
    field_simp
    ring
  rw [heq] at hdiv
  exact hdiv

private lemma chapter9MemSlitOfRePos (z : ℂ) (hre : 0 < z.re) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl hre

private def chapter9Domain : Set ℂ := {z | 0 < z.re ∧ ‖z‖ < 1}

private lemma chapter9DomainIsOpen : IsOpen chapter9Domain := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have heq : chapter9Domain = {z : ℂ | 0 < z.re} ∩ Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [chapter9Domain, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball,
      dist_zero_right]
  rw [heq]
  exact h1.inter h2

private lemma chapter9DomainConvex : Convex ℝ chapter9Domain := by
  have h1 : Convex ℝ {c : ℂ | (0 : ℝ) < c.re} := convex_halfSpace_re_gt 0
  have h2 : Convex ℝ (Metric.ball (0 : ℂ) 1) := convex_ball (0 : ℂ) 1
  have heq : chapter9Domain = {c : ℂ | (0 : ℝ) < c.re} ∩ Metric.ball (0 : ℂ) 1 := by
    ext z
    simp only [chapter9Domain, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_ball,
      dist_zero_right]
  rw [heq]
  exact h1.inter h2

private lemma chapter9DomainPreconnected : IsPreconnected chapter9Domain :=
  chapter9DomainConvex.isPreconnected

private lemma chapter9FHasDerivAtZero (z : ℂ) (hre : 0 < z.re) (hz : ‖z‖ < 1) :
    HasDerivAt chapter9F 0 z := by
  have h1z : (1 + z) ≠ 0 := chapter9OneAddNeZero z hre
  have h1m : (1 - z) ≠ 0 := chapter9OneSubNeZero z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl _ hre
  have hWnorm : ‖chapter9MobiusW z‖ < 1 := chapter9WNormLtOne z hre
  have hWne : chapter9MobiusW z ≠ 0 := chapter9WNeZero z hz hre
  have hzmem : z ∈ Complex.slitPlane := chapter9MemSlitOfRePos z hre
  have hWmem : chapter9MobiusW z ∈ Complex.slitPlane := by
    have hWre : 0 < (chapter9MobiusW z).re := chapter9WRePos z hz hre
    exact chapter9MemSlitOfRePos _ hWre
  have hD : HasDerivAt chapter9ComplexOddDilog
      (chapter9ComplexOddLogSeries z / z) z :=
    chapter9DilogHasDerivAt z hz hz0
  have hW : HasDerivAt chapter9MobiusW (-2 / (1 + z) ^ 2) z :=
    chapter9WHasDerivAt z hre
  have hDWouter : HasDerivAt chapter9ComplexOddDilog
      (chapter9ComplexOddLogSeries (chapter9MobiusW z) / chapter9MobiusW z)
      (chapter9MobiusW z) :=
    chapter9DilogHasDerivAt _ hWnorm hWne
  have hDW : HasDerivAt (chapter9ComplexOddDilog ∘ chapter9MobiusW)
      ((chapter9ComplexOddLogSeries (chapter9MobiusW z) / chapter9MobiusW z) *
        (-2 / (1 + z) ^ 2)) z :=
    hDWouter.comp z hW
  have hDW' : HasDerivAt (fun t => chapter9ComplexOddDilog (chapter9MobiusW t))
      ((chapter9ComplexOddLogSeries (chapter9MobiusW z) / chapter9MobiusW z) *
        (-2 / (1 + z) ^ 2)) z := by
    simpa only [Function.comp_def] using hDW
  have hlogz : HasDerivAt Complex.log z⁻¹ z := hasDerivAt_log hzmem
  have hlogW : HasDerivAt (fun t => Complex.log (chapter9MobiusW t))
      ((-2 / (1 + z) ^ 2) / chapter9MobiusW z) z :=
    hW.clog hWmem
  have hprod : HasDerivAt (fun t => Complex.log t * Complex.log (chapter9MobiusW t))
      (z⁻¹ * Complex.log (chapter9MobiusW z) +
        Complex.log z * ((-2 / (1 + z) ^ 2) / chapter9MobiusW z)) z :=
    hlogz.mul hlogW
  have hhalf : HasDerivAt (fun t => (1 / 2 : ℂ) * (Complex.log t * Complex.log (chapter9MobiusW t)))
      ((1 / 2 : ℂ) * (z⁻¹ * Complex.log (chapter9MobiusW z) +
        Complex.log z * ((-2 / (1 + z) ^ 2) / chapter9MobiusW z))) z :=
    HasDerivAt.const_mul (1 / 2 : ℂ) hprod
  have hhalf' : HasDerivAt (fun t => (1 / 2 : ℂ) * Complex.log t * Complex.log (chapter9MobiusW t))
      ((1 / 2 : ℂ) * (z⁻¹ * Complex.log (chapter9MobiusW z) +
        Complex.log z * ((-2 / (1 + z) ^ 2) / chapter9MobiusW z))) z := by
    simpa only [mul_assoc] using hhalf
  have h12 := hD.add hDW'
  have h123 := h12.add hhalf'
  have hsum : HasDerivAt chapter9F
      ((chapter9ComplexOddLogSeries z / z +
        (chapter9ComplexOddLogSeries (chapter9MobiusW z) / chapter9MobiusW z) *
          (-2 / (1 + z) ^ 2)) +
        (1 / 2 : ℂ) * (z⁻¹ * Complex.log (chapter9MobiusW z) +
          Complex.log z * ((-2 / (1 + z) ^ 2) / chapter9MobiusW z))) z :=
    h123
  have hOz := chapter9OddLogSeriesEqLog z hz
  have hOw := chapter9OddLogSeriesEqLog (chapter9MobiusW z) hWnorm
  have h1add := chapter9LogOneAddW z hre
  have h1sub := chapter9LogOneSubW z hre
  have hLw := chapter9LogW z hz hre
  have hderiv_zero : (chapter9ComplexOddLogSeries z / z +
        (chapter9ComplexOddLogSeries (chapter9MobiusW z) / chapter9MobiusW z) *
          (-2 / (1 + z) ^ 2)) +
        (1 / 2 : ℂ) * (z⁻¹ * Complex.log (chapter9MobiusW z) +
          Complex.log z * ((-2 / (1 + z) ^ 2) / chapter9MobiusW z)) = 0 := by
    rw [hOz, hOw, h1add, h1sub, hLw]
    simp only [chapter9MobiusW]
    field_simp
    ring
  rw [hderiv_zero] at hsum
  exact hsum

private lemma chapter9FDifferentiableOn :
    DifferentiableOn ℂ chapter9F chapter9Domain := by
  intro z hz
  simp only [chapter9Domain, Set.mem_ofPred_eq] at hz
  exact (chapter9FHasDerivAtZero z hz.1 hz.2).differentiableAt.differentiableWithinAt

private lemma chapter9FDerivEqZeroOn :
    Set.EqOn (deriv chapter9F) 0 chapter9Domain := by
  intro z hz
  simp only [chapter9Domain, Set.mem_ofPred_eq] at hz
  exact (chapter9FHasDerivAtZero z hz.1 hz.2).deriv

private lemma chapter9FConstOnDomain :
    ∃ c, ∀ z ∈ chapter9Domain, chapter9F z = c :=
  chapter9DomainIsOpen.exists_is_const_of_deriv_eq_zero
    chapter9DomainPreconnected chapter9FDifferentiableOn chapter9FDerivEqZeroOn

private lemma e26_real_log_mobius_mul_log_tendsto :
    Tendsto (fun t : ℝ => Real.log ((1 - t) / (1 + t)) * Real.log t)
      (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℝ := fun t => Real.log ((1 - t) / (1 + t))
  have hnum : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add 1
  have hquot : HasDerivAt (fun t : ℝ => (1 - t) / (1 + t)) (-2) 0 := by
    convert hnum.div hden (by norm_num) using 1
    all_goals norm_num
  have hf : HasDerivAt f (-2) 0 := by
    convert hquot.log (by norm_num) using 1
    all_goals norm_num [f]
  have hslope : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 (-2)) := by
    convert hf.tendsto_slope_zero_right using 1
    funext t
    simp [f, div_eq_mul_inv, mul_comm]
  have hmul : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using
      Real.continuous_mul_log.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      f t * Real.log t = (f t / t) * (t * Real.log t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  have hprod : Tendsto (fun t : ℝ => (f t / t) * (t * Real.log t))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hslope.mul hmul
  simpa only [f] using (tendsto_congr' heq).mpr hprod

private lemma e26_odd_dilog_tendsto {α : Type*} {l : Filter α} {f : α → ℂ} {z : ℂ}
    (hf : Tendsto f l (𝓝 z)) (hz : ‖z‖ ≤ 1) (hunit : ∀ᶠ a in l, ‖f a‖ ≤ 1) :
    Tendsto (fun a => chapter9ComplexOddDilog (f a)) l
      (𝓝 (chapter9ComplexOddDilog z)) := by
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hwithin : Tendsto f l (𝓝[Metric.closedBall (0 : ℂ) 1] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf <| by
      filter_upwards [hunit] with a ha
      simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  exact (chapter9ComplexOddDilogContinuousOn z hzmem).tendsto.comp hwithin

private lemma e26_mobius_involutive (z : ℂ) (h : 1 + z ≠ 0) :
    chapter9MobiusW (chapter9MobiusW z) = z := by
  simp only [chapter9MobiusW]
  field_simp
  ring

private def e26_endpointParam (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private def e26_endpointPoint (n : ℕ) : ℂ :=
  chapter9MobiusW (e26_endpointParam n)

private lemma e26_endpointParam_pos (n : ℕ) : 0 < e26_endpointParam n := by
  simp only [e26_endpointParam]
  positivity

private lemma e26_endpointParam_le_one (n : ℕ) : e26_endpointParam n ≤ 1 := by
  rw [e26_endpointParam, div_le_one (by positivity)]
  norm_num

private lemma e26_endpointParam_lt_one {n : ℕ} (hn : 0 < n) :
    e26_endpointParam n < 1 := by
  rw [e26_endpointParam, div_lt_one (by positivity)]
  exact_mod_cast (by omega : 1 < n + 1)

private lemma e26_endpointParam_tendsto :
    Tendsto e26_endpointParam atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private lemma e26_mobius_endpointPoint (n : ℕ) :
    chapter9MobiusW (e26_endpointPoint n) = (e26_endpointParam n : ℂ) := by
  rw [e26_endpointPoint]
  apply e26_mobius_involutive
  have ha : 0 < e26_endpointParam n := e26_endpointParam_pos n
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hre
  linarith

private lemma e26_endpointPoint_mem_domain {n : ℕ} (hn : 0 < n) :
    e26_endpointPoint n ∈ chapter9Domain := by
  have ha : 0 < e26_endpointParam n := e26_endpointParam_pos n
  have ha1 : e26_endpointParam n < 1 := e26_endpointParam_lt_one hn
  have hanorm : ‖(e26_endpointParam n : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    exact ha1
  have hare : 0 < ((e26_endpointParam n : ℝ) : ℂ).re := by
    simpa only [Complex.ofReal_re] using ha
  simp only [chapter9Domain, Set.mem_ofPred_eq]
  rw [e26_endpointPoint]
  exact ⟨chapter9WRePos _ hanorm hare, chapter9WNormLtOne _ hare⟩

private lemma e26_endpointPoint_tendsto :
    Tendsto e26_endpointPoint atTop (𝓝 1) := by
  change Tendsto (fun n => ((1 : ℂ) - e26_endpointParam n) /
    (1 + e26_endpointParam n)) atTop (𝓝 1)
  have ha : Tendsto (fun n => (e26_endpointParam n : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp e26_endpointParam_tendsto
  have hnum : Tendsto (fun n => (1 : ℂ) - e26_endpointParam n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub ha
  have hden : Tendsto (fun n => (1 : ℂ) + e26_endpointParam n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add ha
  have h := hnum.div hden (by norm_num : (1 : ℂ) + 0 ≠ 0)
  have h' : Tendsto (fun n => ((1 : ℂ) - e26_endpointParam n) /
      (1 + e26_endpointParam n)) atTop (𝓝 ((1 - 0) / (1 + 0))) := by
    apply h.congr'
    exact Filter.Eventually.of_forall fun _ => rfl
  simpa only [sub_zero, add_zero, div_one] using h'

private lemma e26_endpointParam_tendsto_right :
    Tendsto e26_endpointParam atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    e26_endpointParam_tendsto <|
      Filter.Eventually.of_forall fun n => e26_endpointParam_pos n

private lemma e26_endpointPoint_norm_le_one (n : ℕ) : ‖e26_endpointPoint n‖ ≤ 1 := by
  have hre : 0 < ((e26_endpointParam n : ℝ) : ℂ).re := by
    simpa only [Complex.ofReal_re] using e26_endpointParam_pos n
  rw [e26_endpointPoint]
  exact le_of_lt (chapter9WNormLtOne _ hre)

private lemma e26_endpointParam_norm_le_one (n : ℕ) :
    ‖((e26_endpointParam n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (e26_endpointParam_pos n)]
  exact e26_endpointParam_le_one n

private lemma e26_endpointPoint_ofReal (n : ℕ) :
    e26_endpointPoint n =
      (((1 - e26_endpointParam n) / (1 + e26_endpointParam n) : ℝ) : ℂ) := by
  rw [e26_endpointPoint, chapter9MobiusW]
  push_cast
  rfl

private lemma e26_endpoint_log_product_tendsto :
    Tendsto (fun n => Complex.log (e26_endpointPoint n) *
      Complex.log (chapter9MobiusW (e26_endpointPoint n))) atTop (𝓝 0) := by
  have hreal := e26_real_log_mobius_mul_log_tendsto.comp
    e26_endpointParam_tendsto_right
  have hcomplex : Tendsto (fun n => ((Real.log ((1 - e26_endpointParam n) /
      (1 + e26_endpointParam n)) * Real.log (e26_endpointParam n) : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have hc' : Tendsto (fun n => ((Real.log ((1 - e26_endpointParam n) /
        (1 + e26_endpointParam n)) * Real.log (e26_endpointParam n) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
      apply hc.congr'
      exact Filter.Eventually.of_forall fun _ => rfl
    exact hc'
  have heq : ∀ᶠ n : ℕ in atTop,
      Complex.log (e26_endpointPoint n) *
          Complex.log (chapter9MobiusW (e26_endpointPoint n)) =
        ((Real.log ((1 - e26_endpointParam n) / (1 + e26_endpointParam n)) *
          Real.log (e26_endpointParam n) : ℝ) : ℂ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have ha : 0 < e26_endpointParam n := e26_endpointParam_pos n
    have ha1 : e26_endpointParam n < 1 := e26_endpointParam_lt_one hn0
    have hr : 0 < (1 - e26_endpointParam n) / (1 + e26_endpointParam n) :=
      div_pos (sub_pos.mpr ha1) (by linarith)
    rw [e26_mobius_endpointPoint, e26_endpointPoint_ofReal,
      ← Complex.ofReal_log hr.le, ← Complex.ofReal_log ha.le]
    push_cast
    rfl
  exact (tendsto_congr' heq).mpr hcomplex

private lemma e26_endpoint_F_tendsto :
    Tendsto (fun n => chapter9F (e26_endpointPoint n)) atTop
      (𝓝 ((Real.pi ^ 2 / 8 : ℝ) : ℂ)) := by
  have hchi1 := e26_odd_dilog_tendsto e26_endpointPoint_tendsto
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) <|
      Filter.Eventually.of_forall e26_endpointPoint_norm_le_one
  have hparam : Tendsto (fun n => (e26_endpointParam n : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp e26_endpointParam_tendsto
  have hchi0 := e26_odd_dilog_tendsto hparam (by norm_num : ‖(0 : ℂ)‖ ≤ 1) <|
    Filter.Eventually.of_forall e26_endpointParam_norm_le_one
  have hchiW : Tendsto (fun n =>
      chapter9ComplexOddDilog (chapter9MobiusW (e26_endpointPoint n))) atTop
      (𝓝 (chapter9ComplexOddDilog 0)) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        chapter9ComplexOddDilog (chapter9MobiusW (e26_endpointPoint n)) =
          chapter9ComplexOddDilog (e26_endpointParam n) :=
      Filter.Eventually.of_forall fun n => congrArg chapter9ComplexOddDilog
        (e26_mobius_endpointPoint n)
    exact (tendsto_congr' heq).mpr hchi0
  have hhalfRaw : Tendsto (fun n => (1 / 2 : ℂ) *
      (Complex.log (e26_endpointPoint n) *
        Complex.log (chapter9MobiusW (e26_endpointPoint n)))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℂ)) atTop (𝓝 (1 / 2 : ℂ)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hc.mul e26_endpoint_log_product_tendsto
  have hhalf : Tendsto (fun n =>
      ((1 / 2 : ℂ) * Complex.log (e26_endpointPoint n)) *
        Complex.log (chapter9MobiusW (e26_endpointPoint n))) atTop (𝓝 0) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        ((1 / 2 : ℂ) * Complex.log (e26_endpointPoint n)) *
            Complex.log (chapter9MobiusW (e26_endpointPoint n)) =
          (1 / 2 : ℂ) * (Complex.log (e26_endpointPoint n) *
            Complex.log (chapter9MobiusW (e26_endpointPoint n))) :=
      Filter.Eventually.of_forall fun n => mul_assoc _ _ _
    exact (tendsto_congr' heq).mpr hhalfRaw
  have hsum := (hchi1.add hchiW).add hhalf
  have hsum' : Tendsto (fun n => chapter9F (e26_endpointPoint n)) atTop
      (𝓝 (chapter9ComplexOddDilog 1 + chapter9ComplexOddDilog 0 + 0)) := by
    apply hsum.congr'
    exact Filter.Eventually.of_forall fun _ => rfl
  simpa only [chapter9ComplexOddDilogOne, chapter9ComplexOddDilogZero, add_zero]
    using hsum'

private lemma e26_F_eq_pi_sq_div_eight_on_domain (z : ℂ) (hz : z ∈ chapter9Domain) :
    chapter9F z = ((Real.pi ^ 2 / 8 : ℝ) : ℂ) := by
  obtain ⟨c, hc⟩ := chapter9FConstOnDomain
  have heq : ∀ᶠ n : ℕ in atTop, chapter9F (e26_endpointPoint n) = c := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hc _ (e26_endpointPoint_mem_domain (by omega))
  have hcseq : Tendsto (fun n => chapter9F (e26_endpointPoint n)) atTop (𝓝 c) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  have hvalue : ((Real.pi ^ 2 / 8 : ℝ) : ℂ) = c :=
    tendsto_nhds_unique e26_endpoint_F_tendsto hcseq
  calc chapter9F z = c := hc z hz
    _ = ((Real.pi ^ 2 / 8 : ℝ) : ℂ) := hvalue.symm

private lemma e26_landen_open (z : ℂ) (hre : 0 < z.re) (hz : ‖z‖ < 1) :
    chapter9ComplexOddDilog z + chapter9ComplexOddDilog (chapter9MobiusW z) =
      ((Real.pi ^ 2 / 8 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z) := by
  have hF := e26_F_eq_pi_sq_div_eight_on_domain z <| by
    exact ⟨hre, hz⟩
  change chapter9ComplexOddDilog z + chapter9ComplexOddDilog (chapter9MobiusW z) +
    (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z) =
      ((Real.pi ^ 2 / 8 : ℝ) : ℂ) at hF
  linear_combination hF

private lemma e26_mem_slitPlane_of_re_nonneg (z : ℂ) (hre : 0 ≤ z.re) (hz : z ≠ 0) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hpos : 0 < z.re
  · exact Or.inl hpos
  · right
    have hzre : z.re = 0 := le_antisymm (le_of_not_gt hpos) hre
    intro hzim
    apply hz
    apply Complex.ext <;> simp_all only [Complex.zero_re, Complex.zero_im]

private lemma e26_one_add_ne_zero_of_re_nonneg (z : ℂ) (hre : 0 ≤ z.re) :
    1 + z ≠ 0 := by
  intro h
  have hreal := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hreal
  linarith

private def e26_approxPoint (z : ℂ) (n : ℕ) : ℂ :=
  ((1 - e26_endpointParam n : ℝ) : ℂ) * z + (e26_endpointParam n / 2 : ℝ)

private lemma e26_approxPoint_re_pos (z : ℂ) (hre : 0 ≤ z.re) (n : ℕ) :
    0 < (e26_approxPoint z n).re := by
  change 0 < (((1 - e26_endpointParam n : ℝ) : ℂ) * z +
    (e26_endpointParam n / 2 : ℝ)).re
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hfirst : 0 ≤ (1 - e26_endpointParam n) * z.re :=
    mul_nonneg (sub_nonneg.mpr (e26_endpointParam_le_one n)) hre
  have hsecond : 0 < e26_endpointParam n / 2 := by
    exact div_pos (e26_endpointParam_pos n) (by norm_num)
  linarith

private lemma e26_approxPoint_norm_lt_one (z : ℂ) (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖e26_approxPoint z n‖ < 1 := by
  change ‖((1 - e26_endpointParam n : ℝ) : ℂ) * z +
    (e26_endpointParam n / 2 : ℝ)‖ < 1
  have hc : 0 ≤ 1 - e26_endpointParam n :=
    sub_nonneg.mpr (e26_endpointParam_le_one n)
  have hd : 0 ≤ e26_endpointParam n / 2 :=
    div_nonneg (e26_endpointParam_pos n).le (by norm_num)
  calc
    ‖((1 - e26_endpointParam n : ℝ) : ℂ) * z +
        (e26_endpointParam n / 2 : ℝ)‖
        ≤ ‖((1 - e26_endpointParam n : ℝ) : ℂ) * z‖ +
          ‖((e26_endpointParam n / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = (1 - e26_endpointParam n) * ‖z‖ + e26_endpointParam n / 2 := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ (1 - e26_endpointParam n) * 1 + e26_endpointParam n / 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hz hc) le_rfl
    _ < 1 := by
      have ha := e26_endpointParam_pos n
      linarith

private lemma e26_approxPoint_tendsto (z : ℂ) :
    Tendsto (e26_approxPoint z) atTop (𝓝 z) := by
  have ha : Tendsto (fun n => (e26_endpointParam n : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp e26_endpointParam_tendsto
  have hleft : Tendsto (fun n => ((1 : ℂ) - e26_endpointParam n) * z) atTop
      (𝓝 (((1 : ℂ) - 0) * z)) :=
    (tendsto_const_nhds.sub ha).mul_const z
  have hright : Tendsto (fun n => (e26_endpointParam n : ℂ) / 2) atTop
      (𝓝 ((0 : ℂ) / 2)) := ha.div_const 2
  have hsum := hleft.add hright
  have hsum' : Tendsto (fun n => e26_approxPoint z n) atTop
      (𝓝 ((((1 : ℂ) - 0) * z) + (0 : ℂ) / 2)) := by
    apply hsum.congr'
    filter_upwards [] with n
    change ((1 : ℂ) - e26_endpointParam n) * z + (e26_endpointParam n : ℂ) / 2 =
      ((1 - e26_endpointParam n : ℝ) : ℂ) * z +
        (e26_endpointParam n / 2 : ℝ)
    push_cast
    rfl
  simpa only [sub_zero, one_mul, zero_div, add_zero] using hsum'

private lemma e26_mobius_tendsto {α : Type*} {l : Filter α} {f : α → ℂ} {z : ℂ}
    (hf : Tendsto f l (𝓝 z)) (hre : 0 ≤ z.re) :
    Tendsto (fun a => chapter9MobiusW (f a)) l (𝓝 (chapter9MobiusW z)) := by
  have hnum : Tendsto (fun a => (1 : ℂ) - f a) l (𝓝 (1 - z)) :=
    tendsto_const_nhds.sub hf
  have hden : Tendsto (fun a => (1 : ℂ) + f a) l (𝓝 (1 + z)) :=
    tendsto_const_nhds.add hf
  have h := hnum.div hden (e26_one_add_ne_zero_of_re_nonneg z hre)
  apply h.congr'
  exact Filter.Eventually.of_forall fun _ => rfl

private lemma e26_landen_closed (z : ℂ)
    (hzre : 0 ≤ z.re) (hznorm : ‖z‖ ≤ 1) (hz0 : z ≠ 0)
    (hWre : 0 ≤ (chapter9MobiusW z).re) (hWnorm : ‖chapter9MobiusW z‖ ≤ 1)
    (hW0 : chapter9MobiusW z ≠ 0) :
    chapter9ComplexOddDilog z + chapter9ComplexOddDilog (chapter9MobiusW z) =
      ((Real.pi ^ 2 / 8 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z) := by
  have hzlim := e26_approxPoint_tendsto z
  have hWlim := e26_mobius_tendsto hzlim hzre
  have hchiZ := e26_odd_dilog_tendsto hzlim hznorm <|
    Filter.Eventually.of_forall fun n => le_of_lt (e26_approxPoint_norm_lt_one z hznorm n)
  have hchiW := e26_odd_dilog_tendsto hWlim hWnorm <|
    Filter.Eventually.of_forall fun n => le_of_lt <|
      chapter9WNormLtOne _ (e26_approxPoint_re_pos z hzre n)
  have hlogZ : Tendsto (fun n => Complex.log (e26_approxPoint z n)) atTop
      (𝓝 (Complex.log z)) :=
    hzlim.clog (e26_mem_slitPlane_of_re_nonneg z hzre hz0)
  have hlogW : Tendsto (fun n => Complex.log (chapter9MobiusW (e26_approxPoint z n)))
      atTop (𝓝 (Complex.log (chapter9MobiusW z))) :=
    hWlim.clog (e26_mem_slitPlane_of_re_nonneg _ hWre hW0)
  have hleft : Tendsto (fun n =>
      chapter9ComplexOddDilog (e26_approxPoint z n) +
        chapter9ComplexOddDilog (chapter9MobiusW (e26_approxPoint z n))) atTop
      (𝓝 (chapter9ComplexOddDilog z +
        chapter9ComplexOddDilog (chapter9MobiusW z))) :=
    hchiZ.add hchiW
  have hhalf : Tendsto (fun n => (1 / 2 : ℂ) *
      Complex.log (e26_approxPoint z n)) atTop
      (𝓝 ((1 / 2 : ℂ) * Complex.log z)) := by
    exact (tendsto_const_nhds.mul hlogZ)
  have hprod : Tendsto (fun n =>
      (1 / 2 : ℂ) * Complex.log (e26_approxPoint z n) *
        Complex.log (chapter9MobiusW (e26_approxPoint z n))) atTop
      (𝓝 ((1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z))) :=
    hhalf.mul hlogW
  have hright : Tendsto (fun n => ((Real.pi ^ 2 / 8 : ℝ) : ℂ) -
      (1 / 2 : ℂ) * Complex.log (e26_approxPoint z n) *
        Complex.log (chapter9MobiusW (e26_approxPoint z n))) atTop
      (𝓝 (((Real.pi ^ 2 / 8 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * Complex.log z * Complex.log (chapter9MobiusW z))) :=
    tendsto_const_nhds.sub hprod
  exact tendsto_nhds_unique_of_forall hleft hright fun n =>
    e26_landen_open _ (e26_approxPoint_re_pos z hzre n)
      (e26_approxPoint_norm_lt_one z hznorm n)

private def e26_polar (r angle : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (Complex.I * (angle : ℂ))

private lemma e26_polar_mul (x y theta phi : ℝ) :
    e26_polar x theta * e26_polar y phi = e26_polar (x * y) (theta + phi) := by
  have hexp : Complex.I * ((theta + phi : ℝ) : ℂ) =
      Complex.I * (theta : ℂ) + Complex.I * (phi : ℂ) := by
    push_cast
    ring
  rw [e26_polar, e26_polar, e26_polar, hexp, Complex.exp_add]
  push_cast
  ring

private lemma e26_factor_relation (x y theta phi : ℝ)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
    (1 + e26_polar x theta) * (1 + e26_polar y phi) = 2 := by
  have hrelation' : e26_polar x theta + e26_polar y phi +
      e26_polar (x * y) (theta + phi) = 1 := by
    simpa only [e26_polar] using hrelation
  calc
    (1 + e26_polar x theta) * (1 + e26_polar y phi)
        = 1 + (e26_polar x theta + e26_polar y phi +
          e26_polar x theta * e26_polar y phi) := by ring
    _ = 1 + (e26_polar x theta + e26_polar y phi +
          e26_polar (x * y) (theta + phi)) := by rw [e26_polar_mul]
    _ = 2 := by rw [hrelation']; norm_num

private lemma e26_mobius_eq_of_factor (u w : ℂ) (h : (1 + u) * (1 + w) = 2) :
    chapter9MobiusW u = w := by
  have hne : 1 + u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at h
    norm_num at h
  rw [chapter9MobiusW, div_eq_iff hne]
  linear_combination -h

private lemma e26_re_nonneg_of_mobius_norm_le_one (z : ℂ) (hden : 1 + z ≠ 0)
    (hW : ‖chapter9MobiusW z‖ ≤ 1) : 0 ≤ z.re := by
  have hdenpos : 0 < ‖1 + z‖ := norm_pos_iff.mpr hden
  have hnorm : ‖1 - z‖ ≤ ‖1 + z‖ := by
    rw [chapter9MobiusW, norm_div] at hW
    exact (div_le_one hdenpos).mp hW
  have hsquare : ‖1 - z‖ ^ 2 ≤ ‖1 + z‖ ^ 2 := by
    nlinarith [norm_nonneg (1 - z), norm_nonneg (1 + z)]
  rw [Complex.sq_norm, Complex.sq_norm] at hsquare
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.one_re,
    Complex.sub_im, Complex.add_im, Complex.one_im] at hsquare
  nlinarith

private lemma e26_norm_polar (r angle : ℝ) : ‖e26_polar r angle‖ = |r| := by
  rw [e26_polar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_I_mul_ofReal, mul_one]

private lemma e26_polar_ne_zero (r angle : ℝ) (hr : r ≠ 0) :
    e26_polar r angle ≠ 0 := by
  rw [e26_polar]
  exact mul_ne_zero (by exact_mod_cast hr) (Complex.exp_ne_zero _)

private lemma e26_log_polar (r angle : ℝ) (hr : 0 < r)
    (hangle0 : -Real.pi < angle) (hangle1 : angle ≤ Real.pi) :
    Complex.log (e26_polar r angle) =
      (Real.log r : ℂ) + Complex.I * (angle : ℂ) := by
  have hexp : Complex.exp ((Real.log r : ℂ) + Complex.I * (angle : ℂ)) =
      e26_polar r angle := by
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr, e26_polar]
  rw [← hexp]
  apply Complex.log_exp
  · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_add] using hangle0
  · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add] using hangle1

private lemma e26_polar_pow (r angle : ℝ) (k : ℕ) :
    e26_polar r angle ^ k =
      ((r ^ k : ℝ) : ℂ) *
        Complex.exp (((k : ℝ) * angle : ℝ) * Complex.I) := by
  rw [e26_polar, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  congr 2
  ring

private lemma e26_odd_dilog_term_re (r angle : ℝ) (j : ℕ) :
    (chapter9ComplexOddDilogTerm (e26_polar r angle) j).re =
      chapter9DilogCosTerm r angle (2 * j) := by
  rw [chapter9ComplexOddDilogTerm, e26_polar_pow]
  have hden : ((((2 * j + 1 : ℕ)) : ℂ) ^ 2) =
      (((((2 * j + 1 : ℕ)) : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hden, Complex.div_ofReal_re]
  simp only [chapter9DilogCosTerm, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

private lemma e26_odd_dilog_term_im (r angle : ℝ) (j : ℕ) :
    (chapter9ComplexOddDilogTerm (e26_polar r angle) j).im =
      chapter9DilogSinTerm r angle (2 * j) := by
  rw [chapter9ComplexOddDilogTerm, e26_polar_pow]
  have hden : ((((2 * j + 1 : ℕ)) : ℂ) ^ 2) =
      (((((2 * j + 1 : ℕ)) : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hden, Complex.div_ofReal_im]
  simp only [chapter9DilogSinTerm, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

private lemma e26_odd_dilog_re (r angle : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (chapter9ComplexOddDilog (e26_polar r angle)).re =
      ∑' j : ℕ, chapter9DilogCosTerm r angle (2 * j) := by
  have hnorm : ‖e26_polar r angle‖ ≤ 1 := by
    rw [e26_norm_polar, abs_of_nonneg hr0]
    exact hr1
  have hsum := chapter9ComplexOddDilogSummable (e26_polar r angle) hnorm
  change (∑' j : ℕ, chapter9ComplexOddDilogTerm (e26_polar r angle) j).re = _
  rw [Complex.re_tsum hsum]
  exact tsum_congr fun j => e26_odd_dilog_term_re r angle j

private lemma e26_odd_dilog_im (r angle : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (chapter9ComplexOddDilog (e26_polar r angle)).im =
      ∑' j : ℕ, chapter9DilogSinTerm r angle (2 * j) := by
  have hnorm : ‖e26_polar r angle‖ ≤ 1 := by
    rw [e26_norm_polar, abs_of_nonneg hr0]
    exact hr1
  have hsum := chapter9ComplexOddDilogSummable (e26_polar r angle) hnorm
  change (∑' j : ℕ, chapter9ComplexOddDilogTerm (e26_polar r angle) j).im = _
  rw [Complex.im_tsum hsum]
  exact tsum_congr fun j => e26_odd_dilog_term_im r angle j

private lemma e26_landen_polar_pair (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
    chapter9ComplexOddDilog (e26_polar x theta) +
        chapter9ComplexOddDilog (e26_polar y phi) =
      ((Real.pi ^ 2 / 8 : ℝ) : ℂ) -
        (1 / 2 : ℂ) * Complex.log (e26_polar x theta) *
          Complex.log (e26_polar y phi) := by
  let u := e26_polar x theta
  let w := e26_polar y phi
  have hfactor : (1 + u) * (1 + w) = 2 :=
    e26_factor_relation x y theta phi hrelation
  have hfactor' : (1 + w) * (1 + u) = 2 := by
    rw [mul_comm]
    exact hfactor
  have hWu : chapter9MobiusW u = w := e26_mobius_eq_of_factor u w hfactor
  have hWw : chapter9MobiusW w = u := e26_mobius_eq_of_factor w u hfactor'
  have hunorm : ‖u‖ ≤ 1 := by
    change ‖e26_polar x theta‖ ≤ 1
    rw [e26_norm_polar, abs_of_nonneg hx0]
    exact hx1
  have hwnorm : ‖w‖ ≤ 1 := by
    change ‖e26_polar y phi‖ ≤ 1
    rw [e26_norm_polar, abs_of_nonneg hy0]
    exact hy1
  have hdenu : 1 + u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfactor
    norm_num at hfactor
  have hdenw : 1 + w ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfactor'
    norm_num at hfactor'
  have hure : 0 ≤ u.re := by
    apply e26_re_nonneg_of_mobius_norm_le_one u hdenu
    rw [hWu]
    exact hwnorm
  have hwre : 0 ≤ w.re := by
    apply e26_re_nonneg_of_mobius_norm_le_one w hdenw
    rw [hWw]
    exact hunorm
  have hu0 : u ≠ 0 := e26_polar_ne_zero x theta hx
  have hw0 : w ≠ 0 := e26_polar_ne_zero y phi hy
  have hclosed := e26_landen_closed u hure hunorm hu0 (by rwa [hWu])
    (by rwa [hWu]) (by rwa [hWu])
  rw [hWu] at hclosed
  exact hclosed

private lemma e26_cos_main (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (∑' j : ℕ, chapter9DilogCosTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogCosTerm y phi (2 * j)) =
      Real.pi ^ 2 / 8 -
        (1 / 2 : ℝ) * chapter9BoundaryLog x * chapter9BoundaryLog y +
        (1 / 2 : ℝ) * theta * phi := by
  have hxpos : 0 < x := lt_of_le_of_ne hx0 hx.symm
  have hypos : 0 < y := lt_of_le_of_ne hy0 hy.symm
  have hcomplex := e26_landen_polar_pair x y theta phi hx0 hx1 hy0 hy1 hx hy hrelation
  have hre := congrArg Complex.re hcomplex
  rw [Complex.add_re, e26_odd_dilog_re x theta hx0 hx1,
    e26_odd_dilog_re y phi hy0 hy1, Complex.sub_re,
    e26_log_polar x theta hxpos htheta0 htheta1,
    e26_log_polar y phi hypos hphi0 hphi1] at hre
  have hlogx : chapter9BoundaryLog x = Real.log x := by
    simp only [chapter9BoundaryLog, hx, ite_false]
  have hlogy : chapter9BoundaryLog y = Real.log y := by
    simp only [chapter9BoundaryLog, hy, ite_false]
  rw [hlogx, hlogy]
  norm_num [Complex.mul_re, Complex.add_re, pow_two] at hre
  linear_combination hre

private lemma e26_sin_main (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (∑' j : ℕ, chapter9DilogSinTerm x theta (2 * j)) +
        (∑' j : ℕ, chapter9DilogSinTerm y phi (2 * j)) =
      -(1 / 2 : ℝ) * phi * chapter9BoundaryLog x -
        (1 / 2 : ℝ) * theta * chapter9BoundaryLog y := by
  have hxpos : 0 < x := lt_of_le_of_ne hx0 hx.symm
  have hypos : 0 < y := lt_of_le_of_ne hy0 hy.symm
  have hcomplex := e26_landen_polar_pair x y theta phi hx0 hx1 hy0 hy1 hx hy hrelation
  have him := congrArg Complex.im hcomplex
  rw [Complex.add_im, e26_odd_dilog_im x theta hx0 hx1,
    e26_odd_dilog_im y phi hy0 hy1, Complex.sub_im,
    e26_log_polar x theta hxpos htheta0 htheta1,
    e26_log_polar y phi hypos hphi0 hphi1] at him
  have hlogx : chapter9BoundaryLog x = Real.log x := by
    simp only [chapter9BoundaryLog, hx, ite_false]
  have hlogy : chapter9BoundaryLog y = Real.log y := by
    simp only [chapter9BoundaryLog, hy, ite_false]
  rw [hlogx, hlogy]
  norm_num [Complex.mul_im, Complex.add_im, pow_two] at him
  linear_combination him

/-- **Ramanujan's Landen-type identity in terms of the Entry 24 series.** For real $\rho$ and
$\alpha$ and $k \ge 1$ let $c_k(\rho, \alpha) = \rho^k \cos(k\alpha) / k^2$ and
$s_k(\rho, \alpha) = \rho^k \sin(k\alpha) / k^2$ be the terms of the dilogarithm series of
Entry 24, and write $C(\rho, \alpha) = \sum_{j \ge 0} c_{2j+1}(\rho, \alpha)$ and
$S(\rho, \alpha) = \sum_{j \ge 0} s_{2j+1}(\rho, \alpha)$. Let $x, y \in [0, 1]$ and
$\theta, \varphi \in (-\pi, \pi]$ satisfy
$x e^{i\theta} + y e^{i\varphi} + xy\, e^{i(\theta + \varphi)} = 1$. Then the four series
defining $C(x, \theta)$, $C(y, \varphi)$, $S(x, \theta)$ and $S(y, \varphi)$ converge absolutely,
and, where $\log$ is the real logarithm with $\log 0 = 0$,
$C(x, \theta) + C(y, \varphi) = \pi^2/8 - \tfrac12 \log x \log y + \tfrac12 \theta\varphi$ and
$S(x, \theta) + S(y, \varphi) = -\tfrac12 \varphi \log x - \tfrac12 \theta \log y$. -/
theorem ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms
    (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
    Summable (fun j : ℕ => Entry24Dougall.chapter9DilogCosTerm x theta (2 * j)) ∧
      Summable (fun j : ℕ => Entry24Dougall.chapter9DilogCosTerm y phi (2 * j)) ∧
      Summable (fun j : ℕ => Entry24Dougall.chapter9DilogSinTerm x theta (2 * j)) ∧
      Summable (fun j : ℕ => Entry24Dougall.chapter9DilogSinTerm y phi (2 * j)) ∧
      (∑' j : ℕ, Entry24Dougall.chapter9DilogCosTerm x theta (2 * j)) +
          (∑' j : ℕ, Entry24Dougall.chapter9DilogCosTerm y phi (2 * j)) =
        Real.pi ^ 2 / 8 - (1 / 2 : ℝ) * Real.log x * Real.log y +
          (1 / 2 : ℝ) * theta * phi ∧
      (∑' j : ℕ, Entry24Dougall.chapter9DilogSinTerm x theta (2 * j)) +
          (∑' j : ℕ, Entry24Dougall.chapter9DilogSinTerm y phi (2 * j)) =
        -(1 / 2 : ℝ) * phi * Real.log x - (1 / 2 : ℝ) * theta * Real.log y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [chapter9DilogCosTerm_eq_entry24] using
      chapter9DilogCosOddSummable x theta hx0 hx1
  · simpa only [chapter9DilogCosTerm_eq_entry24] using
      chapter9DilogCosOddSummable y phi hy0 hy1
  · simpa only [chapter9DilogSinTerm_eq_entry24] using
      chapter9DilogSinOddSummable x theta hx0 hx1
  · simpa only [chapter9DilogSinTerm_eq_entry24] using
      chapter9DilogSinOddSummable y phi hy0 hy1
  · by_cases hx : x = 0
    · simpa only [chapter9DilogCosTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
        chapter9CosEqZeroLeft x y theta phi hy0 hphi0 hphi1 hrelation hx
    · by_cases hy : y = 0
      · simpa only [chapter9DilogCosTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
          chapter9CosEqZeroRight x y theta phi hx0 htheta0 htheta1 hrelation hy
      · simpa only [chapter9DilogCosTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
          e26_cos_main x y theta phi hx0 hx1 hy0 hy1 htheta0 htheta1 hphi0 hphi1
            hrelation hx hy
  · by_cases hx : x = 0
    · simpa only [chapter9DilogSinTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
        chapter9SinEqZeroLeft x y theta phi hy0 hphi0 hphi1 hrelation hx
    · by_cases hy : y = 0
      · simpa only [chapter9DilogSinTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
          chapter9SinEqZeroRight x y theta phi hx0 htheta0 htheta1 hrelation hy
      · simpa only [chapter9DilogSinTerm_eq_entry24, chapter9BoundaryLog_eq_log] using
          e26_sin_main x y theta phi hx0 hx1 hy0 hy1 htheta0 htheta1 hphi0 hphi1
            hrelation hx hy

/-- **Ramanujan's Landen-type dilogarithm identity (Entry 26).** For real $\rho$ and $\alpha$
write $C(\rho, \alpha) = \sum_{j \ge 0} \rho^{2j+1} \cos((2j+1)\alpha) / (2j+1)^2$ and
$S(\rho, \alpha) = \sum_{j \ge 0} \rho^{2j+1} \sin((2j+1)\alpha) / (2j+1)^2$. Let
$x, y \in [0, 1]$ and $\theta, \varphi \in (-\pi, \pi]$ satisfy
$x e^{i\theta} + y e^{i\varphi} + xy\, e^{i(\theta + \varphi)} = 1$. Then the four series
defining $C(x, \theta)$, $C(y, \varphi)$, $S(x, \theta)$ and $S(y, \varphi)$ converge absolutely,
and, with the convention $\log 0 = 0$,
$C(x, \theta) + C(y, \varphi) = \pi^2/8 - \tfrac12 \log x \log y + \tfrac12 \theta\varphi$ and
$S(x, \theta) + S(y, \varphi) = -\tfrac12 \varphi \log x - \tfrac12 \theta \log y$.

Proof: Identify the odd series with Legendre's chi function, prove Landen's identity by
differentiation, and extend it to the closed right half-disk by continuity. This follows the route
in Berndt, Part I, Chapter 9, Entry 26, and Lewin, *Polylogarithms and Associated Functions*,
Chapter 1.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9,
Entry 26, p. 273.
-/
theorem ramanujan_part1_ch9_entry26_ramanujanpi
    (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * Complex.exp (Complex.I * (theta : ℂ)) +
          (y : ℂ) * Complex.exp (Complex.I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((theta + phi : ℝ) : ℂ)) = 1) :
    Summable (fun j : ℕ => chapter9DilogCosTerm x theta (2 * j)) ∧
      Summable (fun j : ℕ => chapter9DilogCosTerm y phi (2 * j)) ∧
      Summable (fun j : ℕ => chapter9DilogSinTerm x theta (2 * j)) ∧
      Summable (fun j : ℕ => chapter9DilogSinTerm y phi (2 * j)) ∧
      (∑' j : ℕ, chapter9DilogCosTerm x theta (2 * j)) +
          (∑' j : ℕ, chapter9DilogCosTerm y phi (2 * j)) =
        Real.pi ^ 2 / 8 -
          (1 / 2 : ℝ) * chapter9BoundaryLog x * chapter9BoundaryLog y +
          (1 / 2 : ℝ) * theta * phi ∧
      (∑' j : ℕ, chapter9DilogSinTerm x theta (2 * j)) +
          (∑' j : ℕ, chapter9DilogSinTerm y phi (2 * j)) =
        -(1 / 2 : ℝ) * phi * chapter9BoundaryLog x -
          (1 / 2 : ℝ) * theta * chapter9BoundaryLog y := by
  simpa only [chapter9DilogCosTerm_eq_entry24, chapter9DilogSinTerm_eq_entry24,
    chapter9BoundaryLog_eq_log] using
    ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms x y theta phi hx0 hx1 hy0 hy1
      htheta0 htheta1 hphi0 hphi1 hrelation

end
end Entry26Ramanujanpi
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
