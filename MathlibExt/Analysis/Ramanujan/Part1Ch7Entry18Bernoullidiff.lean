/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.NumberTheory.LSeries.ZMod
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 18

Functional equation of the Dirichlet beta function.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry18Bernoullidiff

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open DirichletBeta

noncomputable section



def chapter7Entry18FunctionalRight (r : ℂ) : ℂ :=
  Complex.cos (Real.pi * r / 2) *
    Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) (r - 1) *
      Complex.Gamma (1 - r) * chapter7DirichletBeta (1 - r)


def chapter7Entry18Left (r : ℂ) : ℂ :=
  Complex.cos (Real.pi * r / 2) * chapter7EulerStar (1 - r)

def chapter7Entry18Middle (r : ℂ) : ℂ :=
  2 * chapter7DirichletBeta r

def chapter7Entry18Right (r : ℂ) : ℂ :=
  Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) r * chapter7EulerStar r /
    Complex.Gamma r

private lemma betaStdAddChar0 : ZMod.stdAddChar (0 : ZMod 4) = 1 := by simp
private lemma betaStdAddChar1 : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  have h : (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) := by simp
  rw [h, ZMod.stdAddChar_coe]
  have e : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) =
      (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
  rw [e]
  exact Complex.exp_pi_div_two_mul_I
private lemma betaStdAddChar2 : ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  have h : (2 : ZMod 4) = ((2 : ℤ) : ZMod 4) := by simp
  rw [h, ZMod.stdAddChar_coe]
  have e : (2 * (Real.pi : ℂ) * Complex.I * ((2 : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) =
      (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [e]
  exact Complex.exp_pi_mul_I
private lemma betaStdAddChar3 : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have h : (3 : ZMod 4) = ((3 : ℤ) : ZMod 4) := by simp
  rw [h, ZMod.stdAddChar_coe]
  have e : (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) =
      -((Real.pi : ℂ) / 2 * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, Complex.exp_neg,
    Complex.exp_pi_div_two_mul_I, Complex.inv_I]

private lemma betaDft : ZMod.dft chapter7BetaCharacter =
    fun k => (-2 * Complex.I) * chapter7BetaCharacter k := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have red : ∀ k : ZMod 4, ZMod.dft chapter7BetaCharacter k =
      ZMod.stdAddChar (-(1 * k)) + ZMod.stdAddChar (-(3 * k)) * (-1) := by
    intro k
    rw [ZMod.dft_apply, betaCharUnivFour, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [betaChar0, betaChar1, betaChar2, betaChar3, smul_eq_mul, mul_zero, zero_add,
      mul_one]
  have h4 : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  funext k
  rcases h4 k with rfl | rfl | rfl | rfl <;> rw [red]
  · rw [show (-((1 : ZMod 4) * 0) : ZMod 4) = 0 from by decide,
      show (-((3 : ZMod 4) * 0) : ZMod 4) = 0 from by decide, betaStdAddChar0, betaChar0]
    ring
  · rw [show (-((1 : ZMod 4) * 1) : ZMod 4) = 3 from by decide,
      show (-((3 : ZMod 4) * 1) : ZMod 4) = 1 from by decide, betaStdAddChar3,
      betaStdAddChar1, betaChar1]
    ring
  · rw [show (-((1 : ZMod 4) * 2) : ZMod 4) = 2 from by decide,
      show (-((3 : ZMod 4) * 2) : ZMod 4) = 2 from by decide, betaStdAddChar2, betaChar2]
    ring
  · rw [show (-((1 : ZMod 4) * 3) : ZMod 4) = 1 from by decide,
      show (-((3 : ZMod 4) * 3) : ZMod 4) = 3 from by decide, betaStdAddChar1,
      betaStdAddChar3, betaChar3]
    ring

private lemma betaDftNeg : ZMod.dft (fun x => chapter7BetaCharacter (-x)) =
    fun k => (2 * Complex.I) * chapter7BetaCharacter k := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have negEq : (fun x => chapter7BetaCharacter (-x)) = -chapter7BetaCharacter := by
    funext x
    simp [Pi.neg_apply, betaCharOdd x]
  rw [negEq, map_neg, betaDft]
  funext k
  simp only [Pi.neg_apply]
  ring

private lemma betaLFunctionMul (c s : ℂ) :
    ZMod.LFunction (fun k => c * chapter7BetaCharacter k) s =
      c * ZMod.LFunction chapter7BetaCharacter s := by
  have hNe : NeZero 4 := ⟨by decide⟩
  simp only [ZMod.LFunction]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

private lemma hIIaux : ∀ a b c : ℂ, Complex.I * b * (-2 * Complex.I * c) +
    -Complex.I * a * (2 * Complex.I * c) = 2 * c * (a + b) := by
  intro a b c
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-2 * c * b - 2 * c * a) * hI

private lemma betaFE (r : ℂ) (hr : Complex.sin ((Real.pi : ℂ) * r) ≠ 0) :
    ZMod.LFunction chapter7BetaCharacter r =
      Complex.cos ((Real.pi : ℂ) * r / 2) *
      (((Real.pi / 2 : ℝ) : ℂ)) ^ (r - 1) *
      Complex.Gamma (1 - r) * ZMod.LFunction chapter7BetaCharacter (1 - r) := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have hrNat : ∀ n : ℕ, r ≠ -(((n : ℕ)) : ℂ) := by
    intro n hn
    subst hn
    apply hr
    have e1 : (Real.pi : ℂ) * -(((n : ℕ)) : ℂ) = (((-((n : ℝ) * Real.pi) : ℝ)) : ℂ) := by
      push_cast; ring
    rw [e1, ← Complex.ofReal_sin, Real.sin_neg, Real.sin_nat_mul_pi]
    simp
  have hrNat1 : ∀ m : ℕ, (1 - r) ≠ -(((m : ℕ)) : ℂ) := by
    intro m hm
    apply hr
    have hrm : r = 1 + (((m : ℕ)) : ℂ) := by linear_combination -hm
    rw [hrm]
    have e2 : (Real.pi : ℂ) * (1 + (((m : ℕ)) : ℂ)) =
        ((((m : ℝ) + 1) * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [e2, ← Complex.ofReal_sin]
    have e3 : ((m : ℝ) + 1) * Real.pi = (((m + 1 : ℕ)) : ℝ) * Real.pi := by
      push_cast; ring
    rw [e3, Real.sin_nat_mul_pi, Complex.ofReal_zero]
  have hFE := ZMod.LFunction_one_sub chapter7BetaCharacter (s := 1 - r) hrNat1 (Or.inl betaChar0)
  rw [sub_sub_cancel, show (1 - r - 1 : ℂ) = -r from by ring] at hFE
  rw [betaDft, betaDftNeg, betaLFunctionMul, betaLFunctionMul] at hFE
  have eA : (Real.pi : ℂ) * Complex.I * (1 - r) / 2 =
      (Real.pi : ℂ) / 2 * Complex.I + (-(((Real.pi : ℂ) * r / 2) * Complex.I)) := by ring
  have eB : -(Real.pi : ℂ) * Complex.I * (1 - r) / 2 =
      (-(Real.pi : ℂ) / 2 * Complex.I) + (((Real.pi : ℂ) * r / 2) * Complex.I) := by ring
  have hA : Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - r) / 2) =
      Complex.I * Complex.exp (-(((Real.pi : ℂ) * r / 2) * Complex.I)) := by
    rw [eA, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have hB : Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - r) / 2) =
      -Complex.I * Complex.exp ((((Real.pi : ℂ) * r / 2)) * Complex.I) := by
    rw [eB, Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  have hCos : Complex.exp ((((Real.pi : ℂ) * r / 2)) * Complex.I) +
      Complex.exp (-(((Real.pi : ℂ) * r / 2) * Complex.I)) =
      2 * Complex.cos ((Real.pi : ℂ) * r / 2) := by
    have h1 := Complex.cos_add_sin_I (((Real.pi : ℂ) * r / 2))
    have h2 := Complex.cos_add_sin_I (-(((Real.pi : ℂ) * r / 2)))
    simp only [Complex.cos_neg, Complex.sin_neg, neg_mul] at h2
    rw [← h1, ← h2]; ring
  have hBracket : Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - r) / 2) *
        (-2 * Complex.I * ZMod.LFunction chapter7BetaCharacter (1 - r)) +
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - r) / 2) *
        (2 * Complex.I * ZMod.LFunction chapter7BetaCharacter (1 - r)) =
        4 * ZMod.LFunction chapter7BetaCharacter (1 - r) * Complex.cos ((Real.pi : ℂ) * r / 2) := by
    rw [hA, hB, hIIaux _ _ _, hCos]; ring
  rw [hBracket] at hFE
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h4r : (0 : ℝ) ≤ 4 := by norm_num
  have h2pir : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpir2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have f4 : (((4 : ℝ)) : ℂ) = 4 := by norm_num
  have f2pi : (((2 * Real.pi : ℝ)) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
  have b4 : (((4 : ℝ)) : ℂ) ≠ 0 := by norm_num
  have e1 : (4 : ℂ) ^ (-r) * 4 = (((4 : ℝ)) : ℂ) ^ (1 - r) := by
    rw [← f4]
    have h := (Complex.cpow_add (-r) (1 : ℂ) b4).symm
    rw [Complex.cpow_one, show (-r + 1 : ℂ) = 1 - r from by ring] at h
    exact h
  have e2 : (2 * (Real.pi : ℂ)) ^ (-(1 - r)) = ((((2 * Real.pi : ℝ)) : ℂ) ^ (1 - r))⁻¹ := by
    rw [← f2pi, Complex.cpow_neg]
  have e3 : ((((4 / (2 * Real.pi)) : ℝ)) : ℂ) ^ (1 - r) =
      (((4 : ℝ)) : ℂ) ^ (1 - r) / ((((2 * Real.pi : ℝ)) : ℂ) ^ (1 - r)) := by
    rw [Complex.ofReal_div]
    exact Complex.div_cpow_ofReal_nonneg h4r h2pir _
  have e4 : ((((4 / (2 * Real.pi)) : ℝ)) : ℂ) = ((((Real.pi / 2 : ℝ)) : ℂ))⁻¹ := by
    have h : (4 / (2 * Real.pi) : ℝ) = (Real.pi / 2)⁻¹ := by
      field_simp
      ring
    rw [h, Complex.ofReal_inv]
  have e5 : (((((Real.pi / 2 : ℝ)) : ℂ))⁻¹) ^ (1 - r) =
      (((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r))⁻¹ :=
    Complex.inv_cpow_ofReal_nonneg hpir2 _
  have e7 : (((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r))⁻¹ =
      ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) := by
    have hrr : (1 - r : ℂ) = -(r - 1) := by ring
    rw [hrr, Complex.cpow_neg, inv_inv]
  have hN4 : ((((4 : ℕ))) : ℂ) = 4 := by norm_num
  have hPowFull : (4 : ℂ) ^ (-r) * (2 * (Real.pi : ℂ)) ^ (-(1 - r)) * 4 =
      ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) := by
    have hRe : ((4 : ℂ) ^ (-r) * (2 * (Real.pi : ℂ)) ^ (-(1 - r)) * 4) =
        (((4 : ℂ) ^ (-r) * 4) * (2 * (Real.pi : ℂ)) ^ (-(1 - r))) := by ring
    rw [hRe, e1, e2, ← div_eq_mul_inv, ← e3, e4, e5, e7]
  have hRegroup : ((4 : ℂ) ^ (-r) * (2 * (Real.pi : ℂ)) ^ (-(1 - r)) *
        Complex.Gamma (1 - r) *
        (4 * ZMod.LFunction chapter7BetaCharacter (1 - r) * Complex.cos ((Real.pi : ℂ) * r / 2))) =
      (((4 : ℂ) ^ (-r) * (2 * (Real.pi : ℂ)) ^ (-(1 - r)) * 4)) *
        Complex.Gamma (1 - r) *
        (ZMod.LFunction chapter7BetaCharacter (1 - r) * Complex.cos ((Real.pi : ℂ) * r / 2)) := by
    ring
  rw [hN4] at hFE
  rw [hRegroup, hPowFull] at hFE
  have hAssoc : ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) * Complex.Gamma (1 - r) *
      (ZMod.LFunction chapter7BetaCharacter (1 - r) * Complex.cos ((Real.pi : ℂ) * r / 2)) =
      Complex.cos ((Real.pi : ℂ) * r / 2) * ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) *
      Complex.Gamma (1 - r) * ZMod.LFunction chapter7BetaCharacter (1 - r) := by ring
  rw [hAssoc] at hFE
  exact hFE



private lemma betaDirichletMeromorphic : MeromorphicOn chapter7DirichletBeta Set.univ :=
  fun x _ => (Differentiable.analyticAt betaDirichletEntire x).meromorphicAt

private lemma entry18LeftMeromorphic : MeromorphicOn chapter7Entry18Left Set.univ := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have dCos : Differentiable ℂ (fun r : ℂ => Complex.cos ((Real.pi : ℂ) * r / 2)) := by
    fun_prop
  have mCos : MeromorphicOn (fun r : ℂ => Complex.cos ((Real.pi : ℂ) * r / 2)) Set.univ :=
    fun x _ => (Differentiable.analyticAt dCos x).meromorphicAt
  have dCpow : Differentiable ℂ (fun s : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) :=
    Differentiable.const_cpow differentiable_id (Or.inl
      (Complex.ofReal_ne_zero.mpr (by positivity : (Real.pi / 2 : ℝ) ≠ 0)))
  have mCpow : MeromorphicOn (fun s : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) Set.univ :=
    fun x _ => (Differentiable.analyticAt dCpow x).meromorphicAt
  have mEuler : MeromorphicOn chapter7EulerStar Set.univ := by
    show MeromorphicOn (fun s => 2 * Complex.Gamma s * chapter7DirichletBeta s /
      ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) Set.univ
    exact (((MeromorphicOn.const (2 : ℂ) (U := Set.univ)).mul MeromorphicOn.Gamma).mul betaDirichletMeromorphic).div mCpow
  have hAn : AnalyticOnNhd ℂ (fun r : ℂ => 1 - r) Set.univ := by fun_prop
  have mComp : MeromorphicOn (chapter7EulerStar ∘ (fun r : ℂ => 1 - r)) Set.univ :=
    mEuler.comp_analyticOnNhd hAn (Set.mapsTo_univ _ _)
  show MeromorphicOn (fun r => Complex.cos ((Real.pi : ℂ) * r / 2) * chapter7EulerStar (1 - r)) Set.univ
  exact mCos.mul mComp

private lemma entry18RightMeromorphic : MeromorphicOn chapter7Entry18Right Set.univ := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have dCpow : Differentiable ℂ (fun s : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) :=
    Differentiable.const_cpow differentiable_id (Or.inl
      (Complex.ofReal_ne_zero.mpr (by positivity : (Real.pi / 2 : ℝ) ≠ 0)))
  have mCpow : MeromorphicOn (fun s : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) Set.univ :=
    fun x _ => (Differentiable.analyticAt dCpow x).meromorphicAt
  have mEuler : MeromorphicOn chapter7EulerStar Set.univ := by
    show MeromorphicOn (fun s => 2 * Complex.Gamma s * chapter7DirichletBeta s /
      ((((Real.pi / 2 : ℝ)) : ℂ)) ^ s) Set.univ
    exact (((MeromorphicOn.const (2 : ℂ) (U := Set.univ)).mul MeromorphicOn.Gamma).mul
      betaDirichletMeromorphic).div mCpow
  show MeromorphicOn (fun r => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ r * chapter7EulerStar r /
    Complex.Gamma r) Set.univ
  exact (mCpow.mul mEuler).div MeromorphicOn.Gamma

private lemma entry18FRMeromorphic : MeromorphicOn chapter7Entry18FunctionalRight Set.univ := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have dCos : Differentiable ℂ (fun r : ℂ => Complex.cos ((Real.pi : ℂ) * r / 2)) := by
    fun_prop
  have mCos : MeromorphicOn (fun r : ℂ => Complex.cos ((Real.pi : ℂ) * r / 2)) Set.univ :=
    fun x _ => (Differentiable.analyticAt dCos x).meromorphicAt
  have hc : ((((Real.pi / 2 : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
  have hSub : Differentiable ℂ (fun r : ℂ => r - 1) := differentiable_id.sub_const 1
  have dCpowS : Differentiable ℂ (fun r : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1)) :=
    Differentiable.const_cpow hSub (Or.inl hc)
  have mCpowS : MeromorphicOn (fun r : ℂ => ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1)) Set.univ :=
    fun x _ => (Differentiable.analyticAt dCpowS x).meromorphicAt
  have hAn : AnalyticOnNhd ℂ (fun r : ℂ => 1 - r) Set.univ := by fun_prop
  have mGamma : MeromorphicOn (fun r : ℂ => Complex.Gamma (1 - r)) Set.univ :=
    MeromorphicOn.Gamma.comp_analyticOnNhd hAn (Set.mapsTo_univ _ _)
  have mBeta : MeromorphicOn (fun r : ℂ => chapter7DirichletBeta (1 - r)) Set.univ :=
    betaDirichletMeromorphic.comp_analyticOnNhd hAn (Set.mapsTo_univ _ _)
  show MeromorphicOn (fun r => Complex.cos ((Real.pi : ℂ) * r / 2) *
    ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) * Complex.Gamma (1 - r) * chapter7DirichletBeta (1 - r)) Set.univ
  exact ((mCos.mul mCpowS).mul mGamma).mul mBeta

private lemma entry18LeftEqMiddle (r : ℂ) (hr : Complex.sin ((Real.pi : ℂ) * r) ≠ 0) :
    chapter7Entry18Left r = chapter7Entry18Middle r := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have h6r : chapter7DirichletBeta r = chapter7Entry18FunctionalRight r := betaFE r hr
  have hc : ((((Real.pi / 2 : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
  have hcc : ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) *
      ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r) = 1 := by
    rw [← Complex.cpow_add (r - 1) (1 - r) hc,
      show ((r - 1) + (1 - r) : ℂ) = 0 from by ring, Complex.cpow_zero]
  have hc1 : ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  have hcc' : ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) =
      1 / ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r) := by
    rw [eq_div_iff hc1]
    exact hcc
  have hM : chapter7Entry18Middle r = 2 * chapter7Entry18FunctionalRight r := by
    show 2 * chapter7DirichletBeta r = 2 * chapter7Entry18FunctionalRight r
    rw [h6r]
  rw [hM]
  show Complex.cos ((Real.pi : ℂ) * r / 2) * chapter7EulerStar (1 - r) = 2 * chapter7Entry18FunctionalRight r
  show Complex.cos ((Real.pi : ℂ) * r / 2) *
    (2 * Complex.Gamma (1 - r) * chapter7DirichletBeta (1 - r) /
    ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (1 - r)) = 2 *
    (Complex.cos ((Real.pi : ℂ) * r / 2) * ((((Real.pi / 2 : ℝ)) : ℂ)) ^ (r - 1) *
    Complex.Gamma (1 - r) * chapter7DirichletBeta (1 - r))
  rw [hcc']
  ring

private lemma entry18MiddleEqRight (r : ℂ) (hr : Complex.sin ((Real.pi : ℂ) * r) ≠ 0) :
    chapter7Entry18Middle r = chapter7Entry18Right r := by
  have hNe : NeZero 4 := ⟨by decide⟩
  have hrNat : ∀ n : ℕ, r ≠ -(((n : ℕ)) : ℂ) := by
    intro n hn
    subst hn
    apply hr
    have e1 : (Real.pi : ℂ) * -(((n : ℕ)) : ℂ) = (((-((n : ℝ) * Real.pi) : ℝ)) : ℂ) := by
      push_cast; ring
    rw [e1, ← Complex.ofReal_sin, Real.sin_neg, Real.sin_nat_mul_pi]
    simp
  have hGr : Complex.Gamma r ≠ 0 := Complex.Gamma_ne_zero hrNat
  have hc : ((((Real.pi / 2 : ℝ)) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity : (Real.pi / 2 : ℝ) ≠ 0)
  have hcr : ((((Real.pi / 2 : ℝ)) : ℂ)) ^ r ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  show 2 * chapter7DirichletBeta r = ((((Real.pi / 2 : ℝ)) : ℂ)) ^ r * chapter7EulerStar r / Complex.Gamma r
  show 2 * chapter7DirichletBeta r = ((((Real.pi / 2 : ℝ)) : ℂ)) ^ r *
    (2 * Complex.Gamma r * chapter7DirichletBeta r / ((((Real.pi / 2 : ℝ)) : ℂ)) ^ r) / Complex.Gamma r
  field_simp

/-- **Functional equation of the Dirichlet beta function.** Let $\chi$ be the non-principal
Dirichlet character modulo $4$, so $\chi(1) = 1$, $\chi(3) = -1$ and $\chi(0) = \chi(2) = 0$; let
$\beta(s) = L(s, \chi)$ be its Dirichlet $L$-function (the Dirichlet beta function, continued to
all of $\mathbb{C}$); and put $E^*(s) = 2\,\Gamma(s)\,\beta(s) / (\pi/2)^s$. Then the functions
$\cos(\pi r/2)\, E^*(1 - r)$, $(\pi/2)^r E^*(r) / \Gamma(r)$ and
$\cos(\pi r/2)\, (\pi/2)^{r-1}\, \Gamma(1 - r)\, \beta(1 - r)$ of $r \in \mathbb{C}$ are
meromorphic on $\mathbb{C}$, and outside a closed discrete subset of $\mathbb{C}$ we have
$\cos(\pi r/2)\, E^*(1 - r) = 2\beta(r) = (\pi/2)^r E^*(r) / \Gamma(r)$ and
$\beta(r) = \cos(\pi r/2)\, (\pi/2)^{r-1}\, \Gamma(1 - r)\, \beta(1 - r)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
Proves `Wanted` entry `ramanujan_part1_ch7_entry18_bernoullidiff`.
-/
theorem ramanujan_part1_ch7_entry18_bernoullidiff :
    MeromorphicOn chapter7Entry18Left Set.univ ∧
      MeromorphicOn chapter7Entry18Right Set.univ ∧
      MeromorphicOn chapter7Entry18FunctionalRight Set.univ ∧
      chapter7Entry18Left =ᶠ[codiscrete ℂ] chapter7Entry18Middle ∧
      chapter7Entry18Middle =ᶠ[codiscrete ℂ] chapter7Entry18Right ∧
      chapter7DirichletBeta =ᶠ[codiscrete ℂ]
        chapter7Entry18FunctionalRight := by

  have hNe : NeZero 4 := ⟨by decide⟩
  have hSin : Differentiable ℂ (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s)) := by
    fun_prop
  have hSinAn : AnalyticOnNhd ℂ (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s)) Set.univ :=
    fun x _ => Differentiable.analyticAt hSin x
  have hSinHalf : (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s)) (1 / 2) ≠ 0 := by
    have e : (Real.pi : ℂ) * (1 / 2 : ℂ) = ((((Real.pi / 2 : ℝ))) : ℂ) := by
      push_cast; ring
    show Complex.sin ((Real.pi : ℂ) * (1 / 2 : ℂ)) ≠ 0
    rw [e, ← Complex.ofReal_sin, Real.sin_pi_div_two]
    simp
  have hGmem : (fun s : ℂ => Complex.sin ((Real.pi : ℂ) * s)) ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete hSinAn hSinHalf
  have hCombined : ∀ᶠ r in codiscrete ℂ,
      (chapter7Entry18Left r = chapter7Entry18Middle r ∧
        chapter7Entry18Middle r = chapter7Entry18Right r ∧
        chapter7DirichletBeta r = chapter7Entry18FunctionalRight r) := by
    filter_upwards [hGmem] with r hr
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hr
    exact ⟨entry18LeftEqMiddle r hr, entry18MiddleEqRight r hr, betaFE r hr⟩
  refine ⟨entry18LeftMeromorphic, entry18RightMeromorphic, entry18FRMeromorphic,
    hCombined.mono (fun r h => h.1), hCombined.mono (fun r h => h.2.1),
    hCombined.mono (fun r h => h.2.2)⟩
end

end Entry18Bernoullidiff

end MathlibExt.Analysis.Ramanujan.Part1Ch7
