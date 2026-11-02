/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic

import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset Complex Topology MeasureTheory

noncomputable section

private instance fact_pi_pos : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

def chapter9Entry2ConstantTerm (r : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry2Constant (r : ℕ) (a : ℝ) : ℝ :=
  ∑' k : ℕ, chapter9Entry2ConstantTerm r a k

def chapter9Entry2CosineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

def chapter9Entry2SineTerm (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ r) +
    Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ r)

private lemma summable_chapter9Entry2ConstantTerm (s : ℕ) (a : ℝ) (hs : 2 ≤ s) :
    Summable (chapter9Entry2ConstantTerm s a) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |a| < K := exists_nat_gt |a|
  have hmajor : Summable (fun k : ℕ => (2 : ℝ) * ((((k : ℝ) + 1) ^ s)⁻¹)) := by
    have hps : Summable (fun n : ℕ => ((((n : ℝ)) ^ s))⁻¹) :=
      (Real.summable_nat_pow_inv (p := s)).mpr (by omega)
    have hshift : Summable (fun n : ℕ => (((((n + 1 : ℕ)) : ℝ) ^ s))⁻¹) := by
      have h := (summable_nat_add_iff 1).mpr hps
      simpa using h
    have hshift' : Summable (fun n : ℕ => (((((n : ℝ)) + 1) ^ s))⁻¹) := by
      simpa using hshift
    exact hshift'.mul_left 2
  apply Summable.of_norm_bounded_eventually hmajor
  have hev : ∀ᶠ k : ℕ in Filter.cofinite, K ≤ k := by
    rw [Filter.eventually_cofinite]
    have hset : {k : ℕ | ¬ K ≤ k} = Set.Iio K := by ext k; simp [Set.mem_Iio, not_le]
    rw [hset]
    exact Set.finite_Iio K
  filter_upwards [hev] with k hk
  set u : ℝ := (((2 * k + 1 : ℕ)) : ℝ) with hu_def
  have hu_eq : u = 2 * (k : ℝ) + 1 := by rw [hu_def]; push_cast; ring
  have hu_nonneg : (0 : ℝ) ≤ u := by rw [hu_eq]; positivity
  have hka : |a| ≤ (k : ℝ) := le_trans (le_of_lt hK) (by exact_mod_cast hk)
  have hbase : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow : (k : ℝ) + 1 ≤ |u - a| := by
    have h1 : u - |a| ≤ |u - a| := by
      have h2 : |u| - |a| ≤ |u - a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u a)
      rwa [abs_of_nonneg hu_nonneg] at h2
    linarith
  have hlow2 : (k : ℝ) + 1 ≤ |u + a| := by
    have h1 : u - |a| ≤ |u + a| := by
      have h2 : |u| - |-a| ≤ |u - -a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u (-a))
      rw [abs_neg, abs_of_nonneg hu_nonneg] at h2
      simpa using h2
    linarith
  have hp1 : ((k : ℝ) + 1) ^ s ≤ |u - a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow s
  have hp2 : ((k : ℝ) + 1) ^ s ≤ |u + a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow2 s
  have hunfold : chapter9Entry2ConstantTerm s a k
      = 1 / (u - a) ^ s + 1 / (u + a) ^ s := by
    unfold chapter9Entry2ConstantTerm
    rw [hu_def]
  have e1 : ‖(1 : ℝ) / (u - a) ^ s‖ = 1 / |u - a| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  have e2 : ‖(1 : ℝ) / (u + a) ^ s‖ = 1 / |u + a| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  rw [hunfold]
  calc ‖(1 : ℝ) / (u - a) ^ s + 1 / (u + a) ^ s‖
        ≤ ‖(1 : ℝ) / (u - a) ^ s‖ + ‖(1 : ℝ) / (u + a) ^ s‖ := norm_add_le _ _
      _ = 1 / |u - a| ^ s + 1 / |u + a| ^ s := by rw [e1, e2]
      _ ≤ 1 / ((k : ℝ) + 1) ^ s + 1 / ((k : ℝ) + 1) ^ s :=
          add_le_add (one_div_le_one_div_of_le (by positivity) hp1)
            (one_div_le_one_div_of_le (by positivity) hp2)
      _ = 2 * ((((k : ℝ) + 1) ^ s)⁻¹) := by rw [one_div]; ring

private lemma sub_ne_zero_of_ha (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (k : ℕ) : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := by
  intro h
  have ha0 : a = (((2 * k + 1 : ℕ) : ℝ)) := by linarith
  have hcast : ((((2 * (k : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hEq : a = ((((2 * (k : ℤ) + 1 : ℤ)) : ℝ)) := by
    rw [hcast]
    exact ha0
  exact ha (k : ℤ) hEq

private lemma add_ne_zero_of_ha (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (k : ℕ) : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := by
  intro h
  have ha0 : a = -(((2 * k + 1 : ℕ) : ℝ)) := by linarith
  have hcast : ((((2 * (-(k : ℤ) - 1) + 1 : ℤ)) : ℝ)) = -(((2 * k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hEq : a = ((((2 * (-(k : ℤ) - 1) + 1 : ℤ)) : ℝ)) := by
    rw [hcast]
    exact ha0
  exact ha (-(k : ℤ) - 1) hEq

private def chapter9Entry2AbsMajorant (s : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  1 / (|(((2 * k + 1 : ℕ) : ℝ) - a)| ^ s) +
    1 / (|(((2 * k + 1 : ℕ) : ℝ) + a)| ^ s)

private lemma summable_absMajorant (s : ℕ) (a : ℝ) (hs : 2 ≤ s) :
    Summable (chapter9Entry2AbsMajorant s a) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |a| < K := exists_nat_gt |a|
  have hmajor : Summable (fun k : ℕ => (2 : ℝ) * ((((k : ℝ) + 1) ^ s)⁻¹)) := by
    have hps : Summable (fun n : ℕ => ((((n : ℝ)) ^ s))⁻¹) :=
      (Real.summable_nat_pow_inv (p := s)).mpr (by omega)
    have hshift : Summable (fun n : ℕ => (((((n + 1 : ℕ)) : ℝ) ^ s))⁻¹) := by
      have h := (summable_nat_add_iff 1).mpr hps
      simpa using h
    have hshift' : Summable (fun n : ℕ => (((((n : ℝ)) + 1) ^ s))⁻¹) := by
      simpa using hshift
    exact hshift'.mul_left 2
  apply Summable.of_norm_bounded_eventually hmajor
  have hev : ∀ᶠ k : ℕ in Filter.cofinite, K ≤ k := by
    rw [Filter.eventually_cofinite]
    have hset : {k : ℕ | ¬ K ≤ k} = Set.Iio K := by ext k; simp [Set.mem_Iio, not_le]
    rw [hset]
    exact Set.finite_Iio K
  filter_upwards [hev] with k hk
  set u : ℝ := (((2 * k + 1 : ℕ)) : ℝ) with hu_def
  have hu_eq : u = 2 * (k : ℝ) + 1 := by rw [hu_def]; push_cast; ring
  have hu_nonneg : (0 : ℝ) ≤ u := by rw [hu_eq]; positivity
  have hka : |a| ≤ (k : ℝ) := le_trans (le_of_lt hK) (by exact_mod_cast hk)
  have hbase : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow : (k : ℝ) + 1 ≤ |u - a| := by
    have h1 : u - |a| ≤ |u - a| := by
      have h2 : |u| - |a| ≤ |u - a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u a)
      rwa [abs_of_nonneg hu_nonneg] at h2
    linarith
  have hlow2 : (k : ℝ) + 1 ≤ |u + a| := by
    have h1 : u - |a| ≤ |u + a| := by
      have h2 : |u| - |-a| ≤ |u - -a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u (-a))
      rw [abs_neg, abs_of_nonneg hu_nonneg] at h2
      simpa using h2
    linarith
  have hp1 : ((k : ℝ) + 1) ^ s ≤ |u - a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow s
  have hp2 : ((k : ℝ) + 1) ^ s ≤ |u + a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow2 s
  have hnonneg : 0 ≤ chapter9Entry2AbsMajorant s a k := by
    unfold chapter9Entry2AbsMajorant
    apply add_nonneg <;> apply one_div_nonneg.mpr <;> positivity
  have hnorm : ‖chapter9Entry2AbsMajorant s a k‖ = chapter9Entry2AbsMajorant s a k := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  unfold chapter9Entry2AbsMajorant
  rw [← hu_def]
  calc 1 / |u - a| ^ s + 1 / |u + a| ^ s
        ≤ 1 / ((k : ℝ) + 1) ^ s + 1 / ((k : ℝ) + 1) ^ s :=
          add_le_add (one_div_le_one_div_of_le (by positivity) hp1)
            (one_div_le_one_div_of_le (by positivity) hp2)
      _ = 2 * ((((k : ℝ) + 1) ^ s)⁻¹) := by rw [one_div]; ring

private lemma norm_constantTerm_le_absMajorant (s : ℕ) (a : ℝ) (k : ℕ) :
    ‖chapter9Entry2ConstantTerm s a k‖ ≤ chapter9Entry2AbsMajorant s a k := by
  unfold chapter9Entry2ConstantTerm chapter9Entry2AbsMajorant
  set p : ℝ := (((2 * k + 1 : ℕ) : ℝ) - a) with hp_def
  set q : ℝ := (((2 * k + 1 : ℕ) : ℝ) + a) with hq_def
  have e1 : ‖(1 : ℝ) / p ^ s‖ = 1 / |p| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  have e2 : ‖(1 : ℝ) / q ^ s‖ = 1 / |q| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  calc ‖(1 : ℝ) / p ^ s + 1 / q ^ s‖
      ≤ ‖(1 : ℝ) / p ^ s‖ + ‖(1 : ℝ) / q ^ s‖ := norm_add_le _ _
    _ = 1 / |p| ^ s + 1 / |q| ^ s := by rw [e1, e2]

private lemma norm_cosineTerm_le_absMajorant (s : ℕ) (a x : ℝ) (k : ℕ) :
    ‖chapter9Entry2CosineTerm s a x k‖ ≤ chapter9Entry2AbsMajorant s a k := by
  unfold chapter9Entry2CosineTerm chapter9Entry2AbsMajorant
  set p : ℝ := (((2 * k + 1 : ℕ) : ℝ) - a) with hp_def
  set q : ℝ := (((2 * k + 1 : ℕ) : ℝ) + a) with hq_def
  have hcos1 : ‖Real.cos (p * x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hcos2 : ‖Real.cos (q * x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have e1 : ‖Real.cos (p * x) / p ^ s‖ ≤ 1 / |p| ^ s := by
    rw [norm_div, norm_pow, Real.norm_eq_abs]
    have hle : ‖Real.cos (p * x)‖ / ‖p‖ ^ s ≤ 1 / ‖p‖ ^ s :=
      div_le_div_of_nonneg_right hcos1 (pow_nonneg (norm_nonneg _) _)
    simpa using hle
  have e2 : ‖Real.cos (q * x) / q ^ s‖ ≤ 1 / |q| ^ s := by
    rw [norm_div, norm_pow, Real.norm_eq_abs]
    have hle : ‖Real.cos (q * x)‖ / ‖q‖ ^ s ≤ 1 / ‖q‖ ^ s :=
      div_le_div_of_nonneg_right hcos2 (pow_nonneg (norm_nonneg _) _)
    simpa using hle
  calc ‖Real.cos (p * x) / p ^ s + Real.cos (q * x) / q ^ s‖
      ≤ ‖Real.cos (p * x) / p ^ s‖ + ‖Real.cos (q * x) / q ^ s‖ := norm_add_le _ _
    _ ≤ 1 / |p| ^ s + 1 / |q| ^ s := add_le_add e1 e2

private lemma norm_sineTerm_le_absMajorant (s : ℕ) (a x : ℝ) (k : ℕ) :
    ‖chapter9Entry2SineTerm s a x k‖ ≤ chapter9Entry2AbsMajorant s a k := by
  unfold chapter9Entry2SineTerm chapter9Entry2AbsMajorant
  set p : ℝ := (((2 * k + 1 : ℕ) : ℝ) - a) with hp_def
  set q : ℝ := (((2 * k + 1 : ℕ) : ℝ) + a) with hq_def
  have hsin1 : ‖Real.sin (p * x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hsin2 : ‖Real.sin (q * x)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have e1 : ‖Real.sin (p * x) / p ^ s‖ ≤ 1 / |p| ^ s := by
    rw [norm_div, norm_pow, Real.norm_eq_abs]
    have hle : ‖Real.sin (p * x)‖ / ‖p‖ ^ s ≤ 1 / ‖p‖ ^ s :=
      div_le_div_of_nonneg_right hsin1 (pow_nonneg (norm_nonneg _) _)
    simpa using hle
  have e2 : ‖Real.sin (q * x) / q ^ s‖ ≤ 1 / |q| ^ s := by
    rw [norm_div, norm_pow, Real.norm_eq_abs]
    have hle : ‖Real.sin (q * x)‖ / ‖q‖ ^ s ≤ 1 / ‖q‖ ^ s :=
      div_le_div_of_nonneg_right hsin2 (pow_nonneg (norm_nonneg _) _)
    simpa using hle
  calc ‖Real.sin (p * x) / p ^ s + Real.sin (q * x) / q ^ s‖
      ≤ ‖Real.sin (p * x) / p ^ s‖ + ‖Real.sin (q * x) / q ^ s‖ := norm_add_le _ _
    _ ≤ 1 / |p| ^ s + 1 / |q| ^ s := add_le_add e1 e2

private lemma summable_cosineTerm (s : ℕ) (a x : ℝ) (hs : 2 ≤ s) :
    Summable (chapter9Entry2CosineTerm s a x) :=
  (summable_absMajorant s a hs).of_norm_bounded
    (fun k => norm_cosineTerm_le_absMajorant s a x k)

private lemma summable_sineTerm (s : ℕ) (a x : ℝ) (hs : 2 ≤ s) :
    Summable (chapter9Entry2SineTerm s a x) :=
  (summable_absMajorant s a hs).of_norm_bounded
    (fun k => norm_sineTerm_le_absMajorant s a x k)

private def entry2E (a : ℝ) : ℂ :=
  Complex.exp (↑(Real.pi * a) * Complex.I)

private def entry2A (a : ℝ) : ℂ :=
  ((↑Real.pi) ^ 2 * entry2E a) / ((1 + entry2E a) ^ 2)

private def entry2B (a : ℝ) : ℂ :=
  (-(↑Real.pi)) / (1 + entry2E a)

private def entry2h (a : ℝ) (x : ℝ) : ℂ :=
  (entry2A a + entry2B a * ↑x) * Complex.exp (↑((a - 1) * x) * Complex.I)

private lemma exp_odd_mul_pi_I (n : ℤ) (hn : Odd n) :
    Complex.exp ((n : ℂ) * ↑Real.pi * Complex.I) = -1 := by
  have hEq : ((n : ℂ) * ↑Real.pi * Complex.I) = (n : ℂ) * (↑Real.pi * Complex.I) := by
    ring
  have hInt := Complex.exp_int_mul (↑Real.pi * Complex.I) n
  rw [hEq, hInt, Complex.exp_pi_mul_I]
  exact hn.neg_one_zpow

private lemma one_add_E_ne_zero (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    1 + entry2E a ≠ 0 := by
  intro h
  have hE : entry2E a = -1 := by linear_combination h
  have hexp1 : Complex.exp (↑(Real.pi * (a - 1)) * Complex.I) = 1 := by
    have harg : ((↑(Real.pi * (a - 1)) : ℂ)) = ↑(Real.pi * a) - ↑Real.pi := by
      push_cast
      ring
    have hsplit : (↑(Real.pi * (a - 1)) * Complex.I : ℂ)
        = (↑(Real.pi * a) * Complex.I - ↑Real.pi * Complex.I) := by
      rw [harg]
      ring
    rw [hsplit, Complex.exp_sub, Complex.exp_pi_mul_I]
    unfold entry2E at hE
    rw [hE]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  have him := congrArg Complex.im hn
  simp only [Complex.mul_I_im, Complex.ofReal_re] at him
  -- him : Real.pi * (a - 1) = (↑n * (2 * ↑Real.pi * Complex.I)).im
  -- simplify RHS to ↑n * (2 * Real.pi)
  have hRw : ((n : ℂ) * (2 * ↑Real.pi * Complex.I) : ℂ)
      = ((n : ℂ) * 2 * ↑Real.pi) * Complex.I := by ring
  rw [hRw, Complex.mul_I_im] at him
  simp only [Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero] at him
  -- him should now be Real.pi * (a - 1) = ↑n * (2 * Real.pi) in ℝ
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha_eq : a = (((2 * n + 1 : ℤ)) : ℝ) := by
    have h1 : Real.pi * (a - 1) = (n : ℝ) * 2 * Real.pi := him
    have h1' : Real.pi * (a - 1) = Real.pi * ((n : ℝ) * 2) := by linarith
    have h2 : a - 1 = (n : ℝ) * 2 := mul_left_cancel₀ hpi h1'
    have h3 : a = 2 * (n : ℝ) + 1 := by linarith
    have hcast : ((((2 * n + 1 : ℤ)) : ℝ)) = 2 * (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact h3
  exact ha n ha_eq

private lemma exp_w_pi_eq_neg_E (a : ℝ) (j : ℤ) :
    Complex.exp (↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) * Complex.I)
      = -entry2E a := by
  have hOdd : Complex.exp (↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi * Complex.I) = -1 :=
    exp_odd_mul_pi_I (2 * j + 1) ⟨j, rfl⟩
  have harg : ((↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) : ℂ))
      = ↑(Real.pi * a) - ↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi := by
    push_cast
    ring
  have hsplit : (↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) * Complex.I : ℂ)
      = (↑(Real.pi * a) * Complex.I
        - ↑(((2 * j + 1 : ℤ) : ℝ)) * ↑Real.pi * Complex.I) := by
    rw [harg]
    ring
  rw [hsplit, Complex.exp_sub, hOdd]
  unfold entry2E
  field_simp

private lemma h_periodic (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    entry2h a 0 = entry2h a Real.pi := by
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hexp : Complex.exp (↑((a - 1) * Real.pi) * Complex.I) = -entry2E a := by
    have h0 := exp_w_pi_eq_neg_E a 0
    have hcast : ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ)) = 1 := by push_cast; ring
    have hEq : a - ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ)) = a - 1 := by rw [hcast]
    have hEq2 : Real.pi * (a - ((((2 * (0 : ℤ) + 1 : ℤ)) : ℝ))) = (a - 1) * Real.pi := by
      rw [hEq]; ring
    rw [hEq2] at h0
    exact h0
  have hAlg : (entry2A a + entry2B a * ↑Real.pi) * (-entry2E a) = entry2A a := by
    unfold entry2A entry2B
    have hNe2 : (1 + entry2E a) ^ 2 ≠ 0 := pow_ne_zero 2 hNe
    field_simp
    ring
  have h0eq : entry2h a 0 = entry2A a := by
    unfold entry2h
    simp
  have hpieq : entry2h a Real.pi
      = (entry2A a + entry2B a * ↑Real.pi) * (-entry2E a) := by
    unfold entry2h
    rw [hexp]
  rw [h0eq, hpieq]
  exact hAlg.symm

private lemma h_continuous (a : ℝ) : Continuous (entry2h a) := by
  unfold entry2h
  fun_prop

private def entry2w (a : ℝ) (j : ℤ) : ℝ :=
  a - ((2 * j + 1 : ℤ) : ℝ)

private lemma w_ne_zero (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (j : ℤ) :
    entry2w a j ≠ 0 := by
  unfold entry2w
  intro h
  have ha_eq : a = (((2 * j + 1 : ℤ)) : ℝ) := by linarith
  exact ha j ha_eq

private def entry2G (a : ℝ) (j : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((↑(entry2w a j)) * Complex.I) * ↑x) *
    ((entry2A a + entry2B a * ↑x) / ((↑(entry2w a j)) * Complex.I)
      + entry2B a / (((↑(entry2w a j))) ^ 2))

private lemma hasDerivAt_ofReal_id (x : ℝ) :
    HasDerivAt (fun y : ℝ => (↑y : ℂ)) 1 x := by
  have hId : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  simpa using hId.ofReal_comp

private lemma hasDerivAt_G_aux (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => entry2G a j y)
      ((entry2A a + entry2B a * ↑x)
        * Complex.exp (((↑(entry2w a j)) * Complex.I) * ↑x)) x := by
  have hw : (↑(entry2w a j) : ℂ) ≠ 0 := by
    exact_mod_cast w_ne_zero a ha j
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hwI : ((↑(entry2w a j) : ℂ) * Complex.I) ≠ 0 := mul_ne_zero hw hI
  -- ℂ→ℂ linear part, then restrict with comp_ofReal
  have hFc : HasDerivAt (fun z : ℂ => (((↑(entry2w a j) : ℂ) * Complex.I) * z))
      ((↑(entry2w a j) : ℂ) * Complex.I) (↑x : ℂ) := by
    simpa using (hasDerivAt_const_mul (((↑(entry2w a j) : ℂ) * Complex.I)) (x := (↑x : ℂ)))
  have hF : HasDerivAt (fun y : ℝ => (((↑(entry2w a j) : ℂ) * Complex.I) * ↑y))
      ((↑(entry2w a j) : ℂ) * Complex.I) x :=
    hFc.comp_ofReal
  have hE : HasDerivAt (fun y : ℝ => Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑y)))
      (Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
        * ((↑(entry2w a j) : ℂ) * Complex.I)) x :=
    hF.cexp
  have hBc : HasDerivAt (fun z : ℂ => entry2B a * z) (entry2B a) (↑x : ℂ) := by
    simpa using (hasDerivAt_const_mul (entry2B a) (x := (↑x : ℂ)))
  have hB : HasDerivAt (fun y : ℝ => entry2B a * (↑y : ℂ)) (entry2B a) x :=
    hBc.comp_ofReal
  have hABc : HasDerivAt (fun z : ℂ => entry2A a + entry2B a * z)
      (entry2B a) (↑x : ℂ) := by
    have h1 : HasDerivAt (fun _ : ℂ => entry2A a) 0 (↑x : ℂ) := hasDerivAt_const _ _
    have h2 := h1.fun_add hBc
    simpa using h2
  have hAB : HasDerivAt (fun y : ℝ => entry2A a + entry2B a * (↑y : ℂ))
      (entry2B a) x :=
    hABc.comp_ofReal
  have hDiv : HasDerivAt
      (fun y : ℝ => (entry2A a + entry2B a * (↑y : ℂ))
        / ((↑(entry2w a j) : ℂ) * Complex.I))
      (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I)) x :=
    hAB.div_const _
  have hL : HasDerivAt
      (fun y : ℝ => (entry2A a + entry2B a * (↑y : ℂ))
        / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
      (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I)) x := by
    have h2 : HasDerivAt (fun _ : ℝ => entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
        0 x := hasDerivAt_const _ _
    have h3 := hDiv.fun_add h2
    simpa using h3
  have hG := hE.fun_mul hL
  have hEq : (Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
        * ((↑(entry2w a j) : ℂ) * Complex.I))
        * ((entry2A a + entry2B a * ↑x) / ((↑(entry2w a j) : ℂ) * Complex.I)
          + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))
        + Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
          * (entry2B a / ((↑(entry2w a j) : ℂ) * Complex.I))
      = (entry2A a + entry2B a * ↑x)
        * Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    field_simp
    linear_combination entry2B a * hII
  have hGoal : (fun y : ℝ => entry2G a j y)
      = (fun y : ℝ => Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑y))
        * ((entry2A a + entry2B a * ↑y) / ((↑(entry2w a j) : ℂ) * Complex.I)
          + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2))) := by
    ext y
    simp only [entry2G]
  rw [hGoal]
  rw [hEq] at hG
  exact hG

private lemma hasDerivAt_G (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ) :
    HasDerivAt (entry2G a j)
      ((entry2A a + entry2B a * ↑x)
        * Complex.exp (((↑(entry2w a j)) * Complex.I) * ↑x)) x :=
  hasDerivAt_G_aux a j ha x

private lemma integral_eq_pi_div_w2 (a : ℝ) (j : ℤ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∫ x in (0 : ℝ)..Real.pi,
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
      = (↑Real.pi : ℂ) / (((↑(entry2w a j) : ℂ)) ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (entry2G a j)
        ((entry2A a + entry2B a * (↑x : ℂ))
          * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) x := by
    intro x _
    exact hasDerivAt_G a j ha x
  have hcont : Continuous (fun x : ℝ =>
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ =>
      (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp (((↑(entry2w a j) : ℂ) * Complex.I) * ↑x))
      MeasureTheory.volume (0 : ℝ) Real.pi :=
    hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hFTC]
  -- compute G π - G 0
  have hw : (↑(entry2w a j) : ℂ) ≠ 0 := by
    exact_mod_cast w_ne_zero a ha j
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hexp_pi : Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑Real.pi))
      = -entry2E a := by
    have h0 := exp_w_pi_eq_neg_E a j
    have hEq3 : ((↑(Real.pi * (a - ((2 * j + 1 : ℤ) : ℝ))) : ℂ) * Complex.I)
        = ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑Real.pi)) := by
      unfold entry2w
      push_cast
      ring
    rw [hEq3] at h0
    exact h0
  have hexp_0 : Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ((0 : ℝ) : ℂ)))
      = 1 := by
    simp
  have hGpi : entry2G a j Real.pi
      = (-entry2E a) * ((entry2A a + entry2B a * ↑Real.pi)
        / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2)) := by
    unfold entry2G
    rw [hexp_pi]
  have hG0 : entry2G a j 0
      = (entry2A a) / ((↑(entry2w a j) : ℂ) * Complex.I)
        + entry2B a / (((↑(entry2w a j) : ℂ)) ^ 2) := by
    unfold entry2G
    simp
  rw [hGpi, hG0]
  unfold entry2A entry2B
  field_simp
  ring

private def entry2f (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    C(AddCircle Real.pi, ℂ) :=
  ⟨AddCircle.liftIco Real.pi 0 (entry2h a),
    AddCircle.liftIco_zero_continuous (h_periodic a ha) (h_continuous a).continuousOn⟩

private lemma fourierCoeff_eq (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (j : ℤ) :
    fourierCoeff (⇑(entry2f a ha)) j
      = 1 / (((↑(entry2w a j) : ℂ)) ^ 2) := by
  have hLift : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ)
      = AddCircle.liftIco Real.pi 0 (entry2h a) := by
    simp only [entry2f, ContinuousMap.coe_mk]
  rw [hLift, fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  have hT : ((0 : ℝ) + Real.pi - 0) = Real.pi := by ring
  have hT2 : (0 : ℝ) + Real.pi = Real.pi := zero_add _
  rw [hT, hT2]
  -- integrand equality
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hPoint : ∀ x : ℝ, fourier (-j) (↑x : AddCircle Real.pi) • entry2h a x
      = (entry2A a + entry2B a * (↑x : ℂ))
        * Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
    intro x
    rw [smul_eq_mul]
    unfold entry2h
    rw [fourier_coe_apply]
    have hExpAdd : (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
          * Complex.exp (↑((a - 1) * x) * Complex.I))
        = Complex.exp ((((↑(entry2w a j) : ℂ) * Complex.I) * ↑x)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold entry2w
      push_cast
      field_simp
      ring
    have hMul : (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
          * ((entry2A a + entry2B a * ↑x)
            * Complex.exp (↑((a - 1) * x) * Complex.I)))
        = (entry2A a + entry2B a * ↑x)
          * (Complex.exp (2 * ↑Real.pi * Complex.I * ↑(-j) * ↑x / ↑Real.pi)
            * Complex.exp (↑((a - 1) * x) * Complex.I)) := by
      ring
    rw [hMul, hExpAdd]
  simp only [hPoint]
  rw [integral_eq_pi_div_w2 a j ha]
  rw [RCLike.real_smul_eq_coe_mul]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  exact one_div_mul_cancel hpi

private lemma summable_fourierCoeff (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    Summable (fourierCoeff (⇑(entry2f a ha))) := by
  apply Summable.of_nat_of_neg_add_one
  · -- j = n
    have hMaj := summable_absMajorant 2 a (by omega : 2 ≤ 2)
    apply hMaj.of_norm_bounded
    intro n
    rw [fourierCoeff_eq a ha (↑n : ℤ)]
    have hcast : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hw_eq : entry2w a (↑n : ℤ) = a - (((2 * n + 1 : ℕ) : ℝ)) := by
      unfold entry2w
      rw [hcast]
    have hnorm : ‖(1 : ℂ) / (((↑(entry2w a (↑n : ℤ)) : ℂ)) ^ 2)‖
        = 1 / (|entry2w a (↑n : ℤ)| ^ 2) := by
      simp only [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hw_eq]
    unfold chapter9Entry2AbsMajorant
    have h1 : (1 : ℝ) / (|a - ↑(2 * n + 1)| ^ 2)
        = 1 / (|↑(2 * n + 1) - a| ^ 2) := by
      rw [abs_sub_comm]
    rw [h1]
    apply le_add_of_nonneg_right
    apply one_div_nonneg.mpr
    positivity
  · -- j = -(n+1)
    have hMaj := summable_absMajorant 2 a (by omega : 2 ≤ 2)
    apply hMaj.of_norm_bounded
    intro n
    have hJ : (-((↑n : ℤ) + 1) : ℤ) = (-(↑n + 1) : ℤ) := rfl
    rw [fourierCoeff_eq a ha (-((↑n : ℤ) + 1))]
    have hcast : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ))
        = -(((2 * n + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hw_eq : entry2w a (-((↑n : ℤ) + 1)) = a + (((2 * n + 1 : ℕ) : ℝ)) := by
      unfold entry2w
      rw [hcast]
      ring
    have hnorm : ‖(1 : ℂ) / (((↑(entry2w a (-((↑n : ℤ) + 1))) : ℂ)) ^ 2)‖
        = 1 / (|entry2w a (-((↑n : ℤ) + 1))| ^ 2) := by
      simp only [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, hw_eq]
    have hcomm : a + (((2 * n + 1 : ℕ) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) + a := by
      ring
    rw [hcomm]
    unfold chapter9Entry2AbsMajorant
    apply le_add_of_nonneg_left
    apply one_div_nonneg.mpr
    positivity

private lemma hasSum_fourier (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => fourierCoeff (⇑(entry2f a ha)) j
      • fourier j (↑x : AddCircle Real.pi)) (entry2h a x) := by
  have hSum := has_pointwise_sum_fourier_series_of_summable
    (f := entry2f a ha) (summable_fourierCoeff a ha) (↑x : AddCircle Real.pi)
  have hx' : x ∈ Set.Ico (0 : ℝ) (0 + Real.pi) := by
    simpa [zero_add] using hx
  have hCoe : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ) (↑x : AddCircle Real.pi)
      = entry2h a x := by
    have h1 : (⇑(entry2f a ha) : AddCircle Real.pi → ℂ)
        = AddCircle.liftIco Real.pi 0 (entry2h a) := by
      simp only [entry2f, ContinuousMap.coe_mk]
    rw [h1]
    exact AddCircle.liftIco_coe_apply hx'
  rw [hCoe] at hSum
  exact hSum

private lemma hasSum_mul_exp (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => Complex.exp (↑((1 - a) * x) * Complex.I)
      * (fourierCoeff (⇑(entry2f a ha)) j • fourier j (↑x : AddCircle Real.pi)))
      (entry2A a + entry2B a * ↑x) := by
  have hBase := hasSum_fourier a ha x hx
  have hMul := hBase.mul_left (Complex.exp (↑((1 - a) * x) * Complex.I))
  have hRhs : Complex.exp (↑((1 - a) * x) * Complex.I) * entry2h a x
      = entry2A a + entry2B a * ↑x := by
    unfold entry2h
    have hExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
          * Complex.exp (↑((a - 1) * x) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]
      have hArg : ((↑((1 - a) * x) : ℂ) * Complex.I
            + ↑((a - 1) * x) * Complex.I) = 0 := by
        push_cast
        ring
      rw [hArg, Complex.exp_zero]
    calc Complex.exp (↑((1 - a) * x) * Complex.I)
          * ((entry2A a + entry2B a * ↑x)
            * Complex.exp (↑((a - 1) * x) * Complex.I))
        = (entry2A a + entry2B a * ↑x)
          * (Complex.exp (↑((1 - a) * x) * Complex.I)
            * Complex.exp (↑((a - 1) * x) * Complex.I)) := by ring
      _ = (entry2A a + entry2B a * ↑x) * 1 := by rw [hExp]
      _ = entry2A a + entry2B a * ↑x := by ring
  rw [hRhs] at hMul
  exact hMul

private lemma hasSum_exp_div (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (fun j : ℤ => Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
      / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2))
      (entry2A a + entry2B a * ↑x) := by
  have hBase := hasSum_mul_exp a ha x hx
  apply hBase.congr_fun
  intro j
  rw [smul_eq_mul, fourierCoeff_eq a ha j, fourier_coe_apply]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
        * (1 / (((↑(entry2w a j) : ℂ)) ^ 2)
          * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi)))
      = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
        / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by
    have hArg : ((↑((1 - a) * x) : ℂ) * Complex.I
          + (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = ((↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) : ℂ) * Complex.I) := by
      push_cast
      field_simp
      ring
    have hDen : ((((↑(entry2w a j) : ℂ)) ^ 2))
        = (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by
      have hw : (↑(entry2w a j) : ℂ) = -((((2 * j + 1 : ℤ) : ℂ)) - ↑a) := by
        unfold entry2w
        push_cast
        ring
      rw [hw, neg_sq]
    have hMulExp : (Complex.exp (↑((1 - a) * x) * Complex.I)
          * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I) := by
      rw [← Complex.exp_add, hArg]
    calc Complex.exp (↑((1 - a) * x) * Complex.I)
            * (1 / (((↑(entry2w a j) : ℂ)) ^ 2)
              * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
        = (Complex.exp (↑((1 - a) * x) * Complex.I)
            * Complex.exp (2 * ↑Real.pi * Complex.I * ↑j * ↑x / ↑Real.pi))
          / (((↑(entry2w a j) : ℂ)) ^ 2) := by
          field_simp
      _ = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
          / (((↑(entry2w a j) : ℂ)) ^ 2) := by rw [hMulExp]
      _ = Complex.exp (↑((((2 * j + 1 : ℤ) : ℝ) - a) * x) * Complex.I)
          / (((((2 * j + 1 : ℤ) : ℂ)) - ↑a) ^ 2) := by rw [hDen]
  exact hExp.symm

private lemma exp_div_ofReal_re (d x : ℝ) :
    (Complex.exp (↑(d * x) * Complex.I) / (↑d : ℂ) ^ 2).re
      = Real.cos (d * x) / d ^ 2 := by
  have hdc : ((d : ℂ)) ^ 2 = ((d ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdc, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, div_eq_mul_inv,
    mul_zero, sub_zero]

private lemma hasSum_cosine_re (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm 2 a x)
      ((entry2A a).re + x * (entry2B a).re) := by
  have hBase := hasSum_exp_div a ha x hx
  have hNat := hBase.nat_add_neg_add_one
  have hRe := Complex.hasSum_re hNat
  have hValEq : (entry2A a + entry2B a * (↑x : ℂ)).re
      = (entry2A a).re + x * (entry2B a).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [← hValEq]
  refine hRe.congr_fun fun n => ?_
  have hcast1 : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hcast2 : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ))
      = -(((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hd1 : ((((2 * (↑n : ℤ) + 1 : ℤ)) : ℂ)) - (↑a : ℂ)
      = ((((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a : ℝ) : ℂ) := by
    push_cast
    ring
  have hd2 : ((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℂ)) - (↑a : ℂ)
      = ((((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a : ℝ) : ℂ) := by
    push_cast
    ring
  rw [Complex.add_re, hd1, hd2,
    exp_div_ofReal_re _ _, exp_div_ofReal_re _ _]
  have hcos2 : (((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a) * x
      = -((((((2 * n + 1 : ℕ) : ℝ)) + a) * x)) := by
    rw [hcast2]
    ring
  have hsq2 : ((((((2 * (-((↑n : ℤ) + 1)) + 1 : ℤ)) : ℝ)) - a)) ^ 2
      = (((((2 * n + 1 : ℕ) : ℝ)) + a)) ^ 2 := by
    rw [hcast2]
    ring
  rw [hcos2, Real.cos_neg, hsq2]
  have hcos1 : (((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a) * x
      = (((((2 * n + 1 : ℕ) : ℝ)) - a) * x) := by
    rw [hcast1]
  have hsq1 : ((((((2 * (↑n : ℤ) + 1 : ℤ)) : ℝ)) - a)) ^ 2
      = (((((2 * n + 1 : ℕ) : ℝ)) - a)) ^ 2 := by
    rw [hcast1]
  rw [hcos1, hsq1]
  simp only [chapter9Entry2CosineTerm]

private def entry2CosSummand (r : ℕ) (a : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
    y ^ (2 * k) / ((2 * k).factorial : ℝ)

private def entry2CosPi (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (r / 2) * Real.pi * x ^ (r - 1) / (2 * ((r - 1).factorial : ℝ))

private def entry2Pcos (r : ℕ) (a x : ℝ) : ℝ :=
  (∑ k ∈ range (r / 2), entry2CosSummand r a k x) + entry2CosPi r x

private def entry2SinSummand (r : ℕ) (a : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
    y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

private def entry2SinPi (r : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ (r - 1) / (2 * ((r - 1).factorial : ℝ))

private def entry2Psin (r : ℕ) (a x : ℝ) : ℝ :=
  (∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k x) + entry2SinPi r x

private def entry2CosSummandDeriv (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
    ((((2 * k : ℕ)) : ℝ) * x ^ (2 * k - 1)) / ((2 * k).factorial : ℝ)

private def entry2CosPiDeriv (r : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ (r / 2) * Real.pi) * ((((r - 1 : ℕ)) : ℝ) * x ^ ((r - 1) - 1)) /
    (2 * ((r - 1).factorial : ℝ))

private def entry2SinSummandDeriv (r : ℕ) (a x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
    ((((2 * k + 1 : ℕ)) : ℝ) * x ^ (2 * k + 1 - 1)) / ((2 * k + 1).factorial : ℝ)

private def entry2SinPiDeriv (r : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ ((r - 1) / 2) * Real.pi) * ((((r - 1 : ℕ)) : ℝ) * x ^ ((r - 1) - 1)) /
    (2 * ((r - 1).factorial : ℝ))

private lemma inv_one_add_E_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    ((1 + entry2E a)⁻¹).re = 1 / 2 := by
  have hNe : 1 + entry2E a ≠ 0 := one_add_E_ne_zero a ha
  have hre : (1 + entry2E a).re = 1 + Real.cos (Real.pi * a) := by
    simp only [Complex.add_re, Complex.one_re, entry2E, Complex.exp_ofReal_mul_I_re]
  have him : (1 + entry2E a).im = Real.sin (Real.pi * a) := by
    simp only [Complex.add_im, Complex.one_im, entry2E, Complex.exp_ofReal_mul_I_im,
      zero_add]
  have hns : (1 + entry2E a).normSq = 2 * (1 + entry2E a).re := by
    rw [Complex.normSq_apply, him, hre]
    have hcs : Real.cos (Real.pi * a) ^ 2 + Real.sin (Real.pi * a) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    linear_combination hcs
  have hre_ne : (1 + entry2E a).re ≠ 0 := by
    intro h0
    apply hNe
    have h00 : (1 + entry2E a).normSq = 0 := by rw [hns, h0, mul_zero]
    exact Complex.normSq_eq_zero.mp h00
  have h2 : 2 * (1 + entry2E a).re ≠ 0 := mul_ne_zero (by norm_num) hre_ne
  rw [Complex.inv_re, hns, div_eq_div_iff h2 (by norm_num)]
  ring

private lemma entry2B_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (entry2B a).re = -Real.pi / 2 := by
  have h := inv_one_add_E_re a ha
  unfold entry2B
  rw [div_eq_mul_inv, Complex.mul_re]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
    neg_zero]
  rw [h]
  ring

private lemma cosineTerm_zero_eq (r : ℕ) (a : ℝ) (k : ℕ) :
    chapter9Entry2CosineTerm r a 0 k = chapter9Entry2ConstantTerm r a k := by
  unfold chapter9Entry2CosineTerm chapter9Entry2ConstantTerm
  simp only [mul_zero, Real.cos_zero]

private lemma sineTerm_zero_eq (r : ℕ) (a : ℝ) (k : ℕ) :
    chapter9Entry2SineTerm r a 0 k = 0 := by
  unfold chapter9Entry2SineTerm
  simp only [mul_zero, Real.sin_zero, zero_div, add_zero]

private lemma summable_cosineTerm_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) :
    Summable (fun k => chapter9Entry2CosineTerm r a 0 k) := by
  have hfun : (fun k => chapter9Entry2CosineTerm r a 0 k)
      = chapter9Entry2ConstantTerm r a := by
    funext k
    exact cosineTerm_zero_eq r a k
  rw [hfun]
  exact summable_chapter9Entry2ConstantTerm r a hr

private lemma entry2A_re (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (entry2A a).re = chapter9Entry2Constant 2 a := by
  have hx0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos⟩
  have hBase := hasSum_cosine_re a ha 0 hx0
  rw [zero_mul, add_zero] at hBase
  have hC : HasSum (chapter9Entry2ConstantTerm 2 a)
      (chapter9Entry2Constant 2 a) :=
    (summable_chapter9Entry2ConstantTerm 2 a (by omega)).hasSum
  have hfun : chapter9Entry2CosineTerm 2 a 0
      = chapter9Entry2ConstantTerm 2 a := by
    funext k
    exact cosineTerm_zero_eq 2 a k
  rw [hfun] at hBase
  exact hBase.unique hC

private lemma Pcos_two (a x : ℝ) :
    entry2Pcos 2 a x = chapter9Entry2Constant 2 a - Real.pi * x / 2 := by
  have h22 : (2 / 2 : ℕ) = 1 := by omega
  have h21 : (2 - 1 : ℕ) = 1 := rfl
  have hf0 : (0 : ℕ).factorial = 1 := rfl
  have hf1 : (1 : ℕ).factorial = 1 := rfl
  unfold entry2Pcos entry2CosSummand entry2CosPi
  rw [h22, h21, Finset.sum_range_one]
  simp only [mul_zero, Nat.sub_zero, pow_zero, pow_one, hf0, hf1, Nat.cast_one,
    one_mul, mul_one, div_one]
  ring

private lemma hasSum_Q2 (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (x : ℝ)
    (hx : x ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm 2 a x) (entry2Pcos 2 a x) := by
  have hBase := hasSum_cosine_re a ha x hx
  have hval : (entry2A a).re + x * (entry2B a).re = entry2Pcos 2 a x := by
    rw [entry2A_re a ha, entry2B_re a ha, Pcos_two a x]
    ring
  rw [hval] at hBase
  exact hBase

private def entry2Q (a : ℝ) (r : ℕ) : Prop :=
  ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
    (Even r → HasSum (chapter9Entry2CosineTerm r a x) (entry2Pcos r a x)) ∧
      (Odd r → HasSum (chapter9Entry2SineTerm r a x) (entry2Psin r a x))

private lemma entry2Q_two (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) : entry2Q a 2 := by
  intro x hx
  constructor
  · intro _
    exact hasSum_Q2 a ha x hx
  · intro ho
    obtain ⟨m, hm⟩ := ho
    omega

private lemma hasDerivAt_cos_div (u : ℝ) (hu : u ≠ 0) (r : ℕ) (hr : 1 ≤ r)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (u * y) / u ^ r)
      (-(Real.sin (u * x) / u ^ (r - 1))) x := by
  have hlin : HasDerivAt (fun y : ℝ => u * y) u x := by
    simpa using (hasDerivAt_id' x).const_mul u
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (u * y))
      (-Real.sin (u * x) * u) x :=
    (Real.hasDerivAt_cos (u * x)).comp x hlin
  have hdiv := hcos.div_const (u ^ r)
  have hrw : r = 1 + (r - 1) := by omega
  have hpow : u ^ r = u * u ^ (r - 1) := by
    conv_lhs => rw [hrw]
    rw [pow_add, pow_one]
  have heq : (-Real.sin (u * x) * u) / u ^ r
      = -(Real.sin (u * x) / u ^ (r - 1)) := by
    rw [hpow]
    have h1 : u ^ (r - 1) ≠ 0 := pow_ne_zero _ hu
    have hprod : u * u ^ (r - 1) ≠ 0 := mul_ne_zero hu h1
    field_simp
  rw [heq] at hdiv
  exact hdiv

private lemma hasDerivAt_sin_div (u : ℝ) (hu : u ≠ 0) (r : ℕ) (hr : 1 ≤ r)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (u * y) / u ^ r)
      (Real.cos (u * x) / u ^ (r - 1)) x := by
  have hlin : HasDerivAt (fun y : ℝ => u * y) u x := by
    simpa using (hasDerivAt_id' x).const_mul u
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (u * y))
      (Real.cos (u * x) * u) x :=
    (Real.hasDerivAt_sin (u * x)).comp x hlin
  have hdiv := hsin.div_const (u ^ r)
  have hrw : r = 1 + (r - 1) := by omega
  have hpow : u ^ r = u * u ^ (r - 1) := by
    conv_lhs => rw [hrw]
    rw [pow_add, pow_one]
  have heq : (Real.cos (u * x) * u) / u ^ r
      = Real.cos (u * x) / u ^ (r - 1) := by
    rw [hpow]
    have h1 : u ^ (r - 1) ≠ 0 := pow_ne_zero _ hu
    have hprod : u * u ^ (r - 1) ≠ 0 := mul_ne_zero hu h1
    field_simp
  rw [heq] at hdiv
  exact hdiv

private lemma hasDerivAt_cosineTerm (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 1 ≤ r) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => chapter9Entry2CosineTerm r a y k)
      (-(chapter9Entry2SineTerm (r - 1) a x k)) x := by
  have hp : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := sub_ne_zero_of_ha a ha k
  have hq : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := add_ne_zero_of_ha a ha k
  have h1 := hasDerivAt_cos_div _ hp r hr x
  have h2 := hasDerivAt_cos_div _ hq r hr x
  have hsum := h1.fun_add h2
  have hderiv : (-(Real.sin (((((2 * k + 1 : ℕ)) : ℝ) - a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) - a) ^ (r - 1)) +
        -(Real.sin (((((2 * k + 1 : ℕ)) : ℝ) + a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) + a) ^ (r - 1)))
      = -(chapter9Entry2SineTerm (r - 1) a x k) := by
    unfold chapter9Entry2SineTerm
    ring
  rw [hderiv] at hsum
  exact hsum

private lemma hasDerivAt_sineTerm (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 1 ≤ r) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => chapter9Entry2SineTerm r a y k)
      (chapter9Entry2CosineTerm (r - 1) a x k) x := by
  have hp : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := sub_ne_zero_of_ha a ha k
  have hq : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := add_ne_zero_of_ha a ha k
  have h1 := hasDerivAt_sin_div _ hp r hr x
  have h2 := hasDerivAt_sin_div _ hq r hr x
  have hsum := h1.fun_add h2
  have hderiv : (Real.cos (((((2 * k + 1 : ℕ)) : ℝ) - a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) - a) ^ (r - 1) +
        Real.cos (((((2 * k + 1 : ℕ)) : ℝ) + a) * x) /
          ((((2 * k + 1 : ℕ)) : ℝ) + a) ^ (r - 1))
      = chapter9Entry2CosineTerm (r - 1) a x k := by
    unfold chapter9Entry2CosineTerm
    ring
  rw [hderiv] at hsum
  exact hsum

private lemma hasDerivAt_tsum_cosine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' k, chapter9Entry2CosineTerm r a y k)
      (-(∑' k, chapter9Entry2SineTerm (r - 1) a x k)) x := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r - 1 := by omega
  have hu : Summable (chapter9Entry2AbsMajorant (r - 1) a) :=
    summable_absMajorant (r - 1) a hr2
  have hg : ∀ k y, HasDerivAt (fun z : ℝ => chapter9Entry2CosineTerm r a z k)
      (-(chapter9Entry2SineTerm (r - 1) a y k)) y :=
    fun k y => hasDerivAt_cosineTerm r a ha hr1 k y
  have hg' : ∀ k y, ‖-(chapter9Entry2SineTerm (r - 1) a y k)‖ ≤
      chapter9Entry2AbsMajorant (r - 1) a k := by
    intro k y
    rw [norm_neg]
    exact norm_sineTerm_le_absMajorant (r - 1) a y k
  have hg0 : Summable (fun k => chapter9Entry2CosineTerm r a 0 k) :=
    summable_cosineTerm_zero r a (by omega)
  have hneg : (∑' k, -(chapter9Entry2SineTerm (r - 1) a x k))
      = -(∑' k, chapter9Entry2SineTerm (r - 1) a x k) := tsum_neg
  rw [← hneg]
  exact hasDerivAt_tsum (u := chapter9Entry2AbsMajorant (r - 1) a)
    (g := fun k y => chapter9Entry2CosineTerm r a y k)
    (g' := fun k y => -(chapter9Entry2SineTerm (r - 1) a y k)) (y₀ := (0 : ℝ))
    hu hg hg' hg0 x

private lemma hasDerivAt_tsum_sine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' k, chapter9Entry2SineTerm r a y k)
      (∑' k, chapter9Entry2CosineTerm (r - 1) a x k) x := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : 2 ≤ r - 1 := by omega
  have hu : Summable (chapter9Entry2AbsMajorant (r - 1) a) :=
    summable_absMajorant (r - 1) a hr2
  have hg : ∀ k y, HasDerivAt (fun z : ℝ => chapter9Entry2SineTerm r a z k)
      (chapter9Entry2CosineTerm (r - 1) a y k) y :=
    fun k y => hasDerivAt_sineTerm r a ha hr1 k y
  have hg' : ∀ k y, ‖chapter9Entry2CosineTerm (r - 1) a y k‖ ≤
      chapter9Entry2AbsMajorant (r - 1) a k :=
    fun k y => norm_cosineTerm_le_absMajorant (r - 1) a y k
  have hg0 : Summable (fun k => chapter9Entry2SineTerm r a 0 k) := by
    have hfun : (fun k => chapter9Entry2SineTerm r a 0 k) = (fun _ => (0 : ℝ)) := by
      funext k
      exact sineTerm_zero_eq r a k
    rw [hfun]
    exact summable_zero
  exact hasDerivAt_tsum (u := chapter9Entry2AbsMajorant (r - 1) a)
    (g := fun k y => chapter9Entry2SineTerm r a y k)
    (g' := fun k y => chapter9Entry2CosineTerm (r - 1) a y k) (y₀ := (0 : ℝ))
    hu hg hg' hg0 x

private lemma hasDerivAt_cosSummand (r : ℕ) (a x : ℝ) (k : ℕ) :
    HasDerivAt (entry2CosSummand r a k) (entry2CosSummandDeriv r a x k) x := by
  exact (((hasDerivAt_pow (2 * k) x).const_mul
    ((-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a)).div_const
    (((2 * k).factorial : ℕ) : ℝ))

private lemma hasDerivAt_sinSummand (r : ℕ) (a x : ℝ) (k : ℕ) :
    HasDerivAt (entry2SinSummand r a k) (entry2SinSummandDeriv r a x k) x := by
  exact (((hasDerivAt_pow (2 * k + 1) x).const_mul
    ((-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a)).div_const
    (((2 * k + 1).factorial : ℕ) : ℝ))

private lemma hasDerivAt_cosPi (r : ℕ) (x : ℝ) :
    HasDerivAt (entry2CosPi r) (entry2CosPiDeriv r x) x := by
  exact (((hasDerivAt_pow (r - 1) x).const_mul
    ((-1 : ℝ) ^ (r / 2) * Real.pi)).div_const
    (2 * ((((r - 1).factorial : ℕ)) : ℝ)))

private lemma hasDerivAt_sinPi (r : ℕ) (x : ℝ) :
    HasDerivAt (entry2SinPi r) (entry2SinPiDeriv r x) x := by
  exact (((hasDerivAt_pow (r - 1) x).const_mul
    ((-1 : ℝ) ^ ((r - 1) / 2) * Real.pi)).div_const
    (2 * ((((r - 1).factorial : ℕ)) : ℝ)))

private lemma cosDeriv_term_eq (r : ℕ) (a x : ℝ) (j : ℕ) :
    entry2CosSummandDeriv r a x (j + 1)
      = -entry2SinSummand (r - 1) a j x := by
  unfold entry2CosSummandDeriv entry2SinSummand
  have hC : r - 2 * (j + 1) = r - 1 - 1 - 2 * j := by omega
  have he' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hF : (2 * (j + 1)).factorial = (2 * (j + 1)) * (2 * j + 1).factorial := by
    have hN : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    conv_lhs => rw [hN]
    rw [Nat.factorial_succ, ← hN]
  have hF' : ((((2 * (j + 1)).factorial : ℕ)) : ℝ)
      = (((2 * (j + 1) : ℕ)) : ℝ) * ((((2 * j + 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hF
  rw [hC, he', hF', pow_succ (-1 : ℝ) j]
  have hN' : (((2 * (j + 1) : ℕ)) : ℝ) ≠ 0 := by
    have hne : 2 * (j + 1) ≠ 0 := by omega
    exact_mod_cast hne
  have hF2 : ((((2 * j + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (((2 * (j + 1) : ℕ)) : ℝ)
      * ((((2 * j + 1).factorial : ℕ)) : ℝ) ≠ 0 := mul_ne_zero hN' hF2
  field_simp

private lemma cosPiDeriv_eq (r : ℕ) (x : ℝ) (hr : 2 ≤ r) (he : Even r) :
    entry2CosPiDeriv r x
      = -((-1 : ℝ) ^ ((r - 1 - 1) / 2) * Real.pi * x ^ (r - 1 - 1) /
        (2 * ((((r - 1 - 1).factorial : ℕ)) : ℝ))) := by
  unfold entry2CosPiDeriv
  have hsr : (r - 1 - 1) / 2 + 1 = r / 2 := by
    obtain ⟨m, hm⟩ := he
    omega
  have hfac : (r - 1).factorial = (r - 1) * (r - 1 - 1).factorial := by
    have h1 : r - 1 = (r - 1 - 1) + 1 := by omega
    conv_lhs => rw [h1]
    rw [Nat.factorial_succ, ← h1]
  have hfac' : ((((r - 1).factorial : ℕ)) : ℝ)
      = ((((r - 1 : ℕ))) : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hfac
  rw [hfac', ← hsr, pow_succ]
  have h1 : ((((r - 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : r - 1 ≠ 0 := by omega
    exact_mod_cast hne
  have h2 : ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (2 : ℝ) * (((((r - 1 : ℕ))) : ℝ)
      * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hprod2 : (2 : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) h2
  field_simp

private lemma hasDerivAt_Pcos (r : ℕ) (a x : ℝ) (hr : 2 ≤ r) (he : Even r) :
    HasDerivAt (entry2Pcos r a) (-(entry2Psin (r - 1) a x)) x := by
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ range (r / 2), entry2CosSummand r a k y)
      (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k) x :=
    HasDerivAt.fun_sum (A := entry2CosSummand r a) (A' := entry2CosSummandDeriv r a x)
      (fun k _ => hasDerivAt_cosSummand r a x k)
  have hpi : HasDerivAt (entry2CosPi r) (entry2CosPiDeriv r x) x :=
    hasDerivAt_cosPi r x
  have htot := hsum.fun_add hpi
  have hval : (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k)
      + entry2CosPiDeriv r x = -(entry2Psin (r - 1) a x) := by
    have hsum_eq : (∑ k ∈ range (r / 2), entry2CosSummandDeriv r a x k)
        = -(∑ k ∈ range ((r - 1 - 1) / 2), entry2SinSummand (r - 1) a k x) := by
      have hs1 : r / 2 = (r - 1 - 1) / 2 + 1 := by
        obtain ⟨m, hm⟩ := he
        omega
      conv_lhs => rw [hs1]
      simp only [Finset.sum_range_succ']
      have hf0 : entry2CosSummandDeriv r a x 0 = 0 := by
        unfold entry2CosSummandDeriv
        simp only [mul_zero, Nat.cast_zero, zero_mul, zero_div]
      rw [hf0, add_zero]
      have hneg : -(∑ k ∈ range ((r - 1 - 1) / 2),
            entry2SinSummand (r - 1) a k x)
          = ∑ k ∈ range ((r - 1 - 1) / 2),
            -entry2SinSummand (r - 1) a k x :=
        (Finset.sum_neg_distrib _).symm
      rw [hneg]
      apply Finset.sum_congr rfl
      intro j hj
      exact cosDeriv_term_eq r a x j
    have hpi_eq := cosPiDeriv_eq r x hr he
    rw [hsum_eq, hpi_eq]
    unfold entry2Psin entry2SinSummand entry2SinPi
    ring
  rw [hval] at htot
  exact htot

private lemma sinDeriv_term_eq (r : ℕ) (a x : ℝ) (k : ℕ) :
    entry2SinSummandDeriv r a x k
      = entry2CosSummand (r - 1) a k x := by
  unfold entry2SinSummandDeriv entry2CosSummand
  have he' : 2 * k + 1 - 1 = 2 * k := by omega
  have hF : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial :=
    Nat.factorial_succ (2 * k)
  have hF' : ((((2 * k + 1).factorial : ℕ)) : ℝ)
      = ((((2 * k + 1 : ℕ))) : ℝ) * ((((2 * k).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hF
  rw [he', hF']
  have hN' : ((((2 * k + 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : 2 * k + 1 ≠ 0 := by omega
    exact_mod_cast hne
  have hF2 : ((((2 * k).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : ((((2 * k + 1 : ℕ))) : ℝ)
      * ((((2 * k).factorial : ℕ)) : ℝ) ≠ 0 := mul_ne_zero hN' hF2
  field_simp

private lemma sinPiDeriv_eq (r : ℕ) (x : ℝ) (hr : 2 ≤ r) :
    entry2SinPiDeriv r x
      = (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ ((r - 1) - 1) /
        (2 * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) := by
  unfold entry2SinPiDeriv
  have hfac : (r - 1).factorial = (r - 1) * (r - 1 - 1).factorial := by
    have h1 : r - 1 = (r - 1 - 1) + 1 := by omega
    conv_lhs => rw [h1]
    rw [Nat.factorial_succ, ← h1]
  have hfac' : ((((r - 1).factorial : ℕ)) : ℝ)
      = ((((r - 1 : ℕ))) : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) := by
    exact_mod_cast hfac
  rw [hfac']
  have h1 : ((((r - 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : r - 1 ≠ 0 := by omega
    exact_mod_cast hne
  have h2 : ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hprod : (2 : ℝ) * (((((r - 1 : ℕ))) : ℝ)
      * ((((r - 1 - 1).factorial : ℕ)) : ℝ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hprod2 : (2 : ℝ) * ((((r - 1 - 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) h2
  field_simp

private lemma hasDerivAt_Psin (r : ℕ) (a x : ℝ) (hr : 2 ≤ r) :
    HasDerivAt (entry2Psin r a) (entry2Pcos (r - 1) a x) x := by
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k y)
      (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k) x :=
    HasDerivAt.fun_sum (A := entry2SinSummand r a) (A' := entry2SinSummandDeriv r a x)
      (fun k _ => hasDerivAt_sinSummand r a x k)
  have hpi : HasDerivAt (entry2SinPi r) (entry2SinPiDeriv r x) x :=
    hasDerivAt_sinPi r x
  have htot := hsum.fun_add hpi
  have hval : (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k)
      + entry2SinPiDeriv r x = entry2Pcos (r - 1) a x := by
    have hsum_eq : (∑ k ∈ range ((r - 1) / 2), entry2SinSummandDeriv r a x k)
        = ∑ k ∈ range ((r - 1) / 2), entry2CosSummand (r - 1) a k x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact sinDeriv_term_eq r a x k
    have hpi_eq := sinPiDeriv_eq r x hr
    rw [hsum_eq, hpi_eq]
    unfold entry2Pcos entry2CosSummand entry2CosPi
    ring
  rw [hval] at htot
  exact htot

private lemma Pcos_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) (he : Even r) :
    entry2Pcos r a 0 = chapter9Entry2Constant r a := by
  have hs : 1 ≤ r / 2 := by
    obtain ⟨m, hm⟩ := he
    omega
  have hsum : (∑ k ∈ range (r / 2), entry2CosSummand r a k 0)
      = entry2CosSummand r a 0 0 := by
    apply Finset.sum_eq_single 0
    · intro k hk hk0
      unfold entry2CosSummand
      have hne : 2 * k ≠ 0 := by omega
      simp only [zero_pow hne, mul_zero, zero_div]
    · intro h0
      simp only [Finset.mem_range, Nat.not_lt] at h0
      have hF : False := by omega
      exact hF.elim
  have hF0 : entry2CosSummand r a 0 0 = chapter9Entry2Constant r a := by
    unfold entry2CosSummand
    simp only [mul_zero, Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, mul_one, div_one]
  have hpi : entry2CosPi r 0 = 0 := by
    unfold entry2CosPi
    have hne : r - 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  unfold entry2Pcos
  rw [hsum, hF0, hpi, add_zero]

private lemma Psin_zero (r : ℕ) (a : ℝ) (hr : 2 ≤ r) :
    entry2Psin r a 0 = 0 := by
  have hsum : (∑ k ∈ range ((r - 1) / 2), entry2SinSummand r a k 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    unfold entry2SinSummand
    have hne : 2 * k + 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  have hpi : entry2SinPi r 0 = 0 := by
    unfold entry2SinPi
    have hne : r - 1 ≠ 0 := by omega
    simp only [zero_pow hne, mul_zero, zero_div]
  unfold entry2Psin
  rw [hsum, hpi, add_zero]

private lemma step_cosine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r) (he : Even r)
    (IH : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
      HasSum (chapter9Entry2SineTerm (r - 1) a x) (entry2Psin (r - 1) a x))
    (x0 : ℝ) (hx0 : x0 ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2CosineTerm r a x0) (entry2Pcos r a x0) := by
  have hr2 : 2 ≤ r := by omega
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
      (-(∑' k, chapter9Entry2SineTerm (r - 1) a y k)) y :=
    fun y => hasDerivAt_tsum_cosine r a ha hr y
  have hP : ∀ y : ℝ, HasDerivAt (entry2Pcos r a)
      (-(entry2Psin (r - 1) a y)) y :=
    fun y => hasDerivAt_Pcos r a y hr2 he
  have hD : ∀ y : ℝ, HasDerivAt
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      ((-(∑' k, chapter9Entry2SineTerm (r - 1) a y k))
        - (-(entry2Psin (r - 1) a y))) y :=
    fun y => (hS y).sub (hP y)
  have hcont : ContinuousOn
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      (Set.Icc 0 x0) := by
    have hC : Continuous
        ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a) :=
      continuous_iff_continuousAt.mpr (fun y => (hD y).continuousAt)
    exact hC.continuousOn
  have hderiv : ∀ y ∈ Set.Ico 0 x0, HasDerivWithinAt
      ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k) - entry2Pcos r a)
      0 (Set.Ici y) y := by
    intro y hy
    have hyIco : y ∈ Set.Ico (0 : ℝ) Real.pi := ⟨hy.1, lt_of_lt_of_le hy.2 hx0.2.le⟩
    have hIH := IH y hyIco
    have htsum : (∑' k, chapter9Entry2SineTerm (r - 1) a y k)
        = entry2Psin (r - 1) a y := hIH.tsum_eq
    have h0 : ((-(∑' k, chapter9Entry2SineTerm (r - 1) a y k))
        - (-(entry2Psin (r - 1) a y))) = 0 := by
      rw [htsum, sub_self]
    have hDy := hD y
    rw [h0] at hDy
    exact hDy.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  have hx0mem : x0 ∈ Set.Icc 0 x0 := ⟨hx0.1, le_rfl⟩
  have hD0 : ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
        - entry2Pcos r a) x0
      = ((fun z : ℝ => ∑' k, chapter9Entry2CosineTerm r a z k)
        - entry2Pcos r a) 0 :=
    hconst x0 hx0mem
  simp only [Pi.sub_apply] at hD0
  have hS0 : (∑' k, chapter9Entry2CosineTerm r a 0 k)
      = chapter9Entry2Constant r a := by
    unfold chapter9Entry2Constant
    apply tsum_congr
    intro k
    exact cosineTerm_zero_eq r a k
  have hP0 : entry2Pcos r a 0 = chapter9Entry2Constant r a :=
    Pcos_zero r a hr2 he
  have hSeq : (∑' k, chapter9Entry2CosineTerm r a x0 k)
      = entry2Pcos r a x0 := by
    linarith [hD0, hS0, hP0]
  have hsum := (summable_cosineTerm r a x0 hr2).hasSum
  rw [hSeq] at hsum
  exact hsum

private lemma step_sine (r : ℕ) (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hr : 3 ≤ r)
    (IH : ∀ x ∈ Set.Ico (0 : ℝ) Real.pi,
      HasSum (chapter9Entry2CosineTerm (r - 1) a x) (entry2Pcos (r - 1) a x))
    (x0 : ℝ) (hx0 : x0 ∈ Set.Ico (0 : ℝ) Real.pi) :
    HasSum (chapter9Entry2SineTerm r a x0) (entry2Psin r a x0) := by
  have hr2 : 2 ≤ r := by omega
  have hS : ∀ y : ℝ, HasDerivAt
      (fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
      (∑' k, chapter9Entry2CosineTerm (r - 1) a y k) y :=
    fun y => hasDerivAt_tsum_sine r a ha hr y
  have hP : ∀ y : ℝ, HasDerivAt (entry2Psin r a)
      (entry2Pcos (r - 1) a y) y :=
    fun y => hasDerivAt_Psin r a y hr2
  have hD : ∀ y : ℝ, HasDerivAt
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      ((∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        - entry2Pcos (r - 1) a y) y :=
    fun y => (hS y).sub (hP y)
  have hcont : ContinuousOn
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      (Set.Icc 0 x0) := by
    have hC : Continuous
        ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a) :=
      continuous_iff_continuousAt.mpr (fun y => (hD y).continuousAt)
    exact hC.continuousOn
  have hderiv : ∀ y ∈ Set.Ico 0 x0, HasDerivWithinAt
      ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k) - entry2Psin r a)
      0 (Set.Ici y) y := by
    intro y hy
    have hyIco : y ∈ Set.Ico (0 : ℝ) Real.pi := ⟨hy.1, lt_of_lt_of_le hy.2 hx0.2.le⟩
    have hIH := IH y hyIco
    have htsum : (∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        = entry2Pcos (r - 1) a y := hIH.tsum_eq
    have h0 : ((∑' k, chapter9Entry2CosineTerm (r - 1) a y k)
        - entry2Pcos (r - 1) a y) = 0 := by
      rw [htsum, sub_self]
    have hDy := hD y
    rw [h0] at hDy
    exact hDy.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  have hx0mem : x0 ∈ Set.Icc 0 x0 := ⟨hx0.1, le_rfl⟩
  have hD0 : ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
        - entry2Psin r a) x0
      = ((fun z : ℝ => ∑' k, chapter9Entry2SineTerm r a z k)
        - entry2Psin r a) 0 :=
    hconst x0 hx0mem
  simp only [Pi.sub_apply] at hD0
  have hS0 : (∑' k, chapter9Entry2SineTerm r a 0 k) = 0 := by
    have hfun : ∀ k, chapter9Entry2SineTerm r a 0 k = 0 :=
      fun k => sineTerm_zero_eq r a k
    rw [tsum_congr hfun]
    exact tsum_zero
  have hP0 : entry2Psin r a 0 = 0 := Psin_zero r a hr2
  have hSeq : (∑' k, chapter9Entry2SineTerm r a x0 k)
      = entry2Psin r a x0 := by
    linarith [hD0, hS0, hP0]
  have hsum := (summable_sineTerm r a x0 hr2).hasSum
  rw [hSeq] at hsum
  exact hsum

private lemma entry2Q_step (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (n : ℕ) (hn : 2 ≤ n)
    (IH : entry2Q a n) : entry2Q a (n + 1) := by
  have hr : 3 ≤ n + 1 := by omega
  have hn1 : n + 1 - 1 = n := by omega
  intro x hx
  rcases Nat.even_or_odd (n + 1) with he | ho
  · constructor
    · intro _
      have hon : Odd n := by
        obtain ⟨m, hm⟩ := he
        exact ⟨m - 1, by omega⟩
      have IH' : ∀ y ∈ Set.Ico (0 : ℝ) Real.pi,
          HasSum (chapter9Entry2SineTerm (n + 1 - 1) a y)
            (entry2Psin (n + 1 - 1) a y) := by
        intro y hy
        have hcon := IH y hy
        rw [hn1]
        exact hcon.2 hon
      exact step_cosine (n + 1) a ha hr he IH' x hx
    · intro ho'
      obtain ⟨m, hm⟩ := he
      obtain ⟨k, hk⟩ := ho'
      omega
  · constructor
    · intro he'
      obtain ⟨m, hm⟩ := he'
      obtain ⟨k, hk⟩ := ho
      omega
    · intro _
      have hen : Even n := by
        obtain ⟨m, hm⟩ := ho
        exact ⟨m, by omega⟩
      have IH' : ∀ y ∈ Set.Ico (0 : ℝ) Real.pi,
          HasSum (chapter9Entry2CosineTerm (n + 1 - 1) a y)
            (entry2Pcos (n + 1 - 1) a y) := by
        intro y hy
        have hcon := IH y hy
        rw [hn1]
        exact hcon.1 hen
      exact step_sine (n + 1) a ha hr IH' x hx

private lemma entry2Q_all_aux (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    ∀ n : ℕ, entry2Q a (2 + n) := by
  intro n
  induction n with
  | zero =>
    change entry2Q a 2
    exact entry2Q_two a ha
  | succ n IH =>
    have h := entry2Q_step a ha (2 + n) (by omega) IH
    have heq : 2 + (n + 1) = (2 + n) + 1 := by omega
    rw [heq]
    exact h

private lemma entry2Q_all (a : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (r : ℕ) (hr : 2 ≤ r) :
    entry2Q a r := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hr
  rw [hn]
  exact entry2Q_all_aux a ha n

/-- **Sum series over $2k+1 \pm a$ on $(0, \pi)$.** Let $r \ge 2$ be an integer, $a$ a real
number that is not an odd integer, and $x$ a real number with $0 < x < \pi$. For a natural
number $s$ let $d_k(s) = (2k+1-a)^{-s} + (2k+1+a)^{-s}$ and
$D_s(a) = \sum_{k=0}^{\infty} d_k(s)$. Then $\sum_k d_k(r)$ is summable, and either $r$ is
even, $\sum_k d_k(r-2j)$ is summable for $0 \le j < r/2$, and the partial sums of
$\sum_{k=0}^{\infty} \bigl(\frac{\cos((2k+1-a)x)}{(2k+1-a)^r} +
\frac{\cos((2k+1+a)x)}{(2k+1+a)^r}\bigr)$ converge to
$\sum_{0 \le j < r/2} (-1)^j D_{r-2j}(a) \frac{x^{2j}}{(2j)!} +
(-1)^{r/2} \frac{\pi x^{r-1}}{2 (r-1)!}$; or $r$ is odd, $\sum_k d_k(r-1-2j)$ is summable
for $0 \le j < (r-1)/2$, and the partial sums of
$\sum_{k=0}^{\infty} \bigl(\frac{\sin((2k+1-a)x)}{(2k+1-a)^r} +
\frac{\sin((2k+1+a)x)}{(2k+1+a)^r}\bigr)$ converge to
$\sum_{0 \le j < (r-1)/2} (-1)^j D_{r-1-2j}(a) \frac{x^{2j+1}}{(2j+1)!} +
(-1)^{(r-1)/2} \frac{\pi x^{r-1}}{2 (r-1)!}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry2 (r : ℕ) (a x : ℝ)
    (hr : 2 ≤ r)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (hxLower : 0 < x) (hxUpper : x < Real.pi) :
    Summable (chapter9Entry2ConstantTerm r a) ∧
      ((Even r ∧
          (∀ k ∈ range (r / 2),
            Summable (chapter9Entry2ConstantTerm (r - 2 * k) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry2CosineTerm r a x k)
            atTop
            (𝓝 ((∑ k ∈ range (r / 2),
              (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
                x ^ (2 * k) / ((2 * k).factorial : ℝ)) +
              (-1 : ℝ) ^ (r / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ))))) ∨
        (Odd r ∧
          (∀ k ∈ range ((r - 1) / 2),
            Summable (chapter9Entry2ConstantTerm (r - 1 - 2 * k) a)) ∧
          Tendsto
            (fun N : ℕ =>
              ∑ k ∈ range N, chapter9Entry2SineTerm r a x k)
            atTop
            (𝓝 ((∑ k ∈ range ((r - 1) / 2),
              (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
                x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) +
              (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ)))))) := by
  have hkey : ∀ s : ℕ, 2 ≤ s → Summable (chapter9Entry2ConstantTerm s a) :=
    fun s hs => summable_chapter9Entry2ConstantTerm s a hs
  have hQ := entry2Q_all a ha r hr
  have hxIco : x ∈ Set.Ico (0 : ℝ) Real.pi := ⟨le_of_lt hxLower, hxUpper⟩
  have hcon := hQ x hxIco
  refine ⟨hkey r hr, ?_⟩
  rcases Nat.even_or_odd r with he | ho
  · left
    refine ⟨he, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_range] at hk
      apply hkey
      obtain ⟨m, hm⟩ := he
      omega
    · have hHas := hcon.1 he
      change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry2CosineTerm r a x k)
        atTop (𝓝 (entry2Pcos r a x))
      exact hHas.tendsto_sum_nat
  · right
    refine ⟨ho, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_range] at hk
      apply hkey
      obtain ⟨m, hm⟩ := ho
      omega
    · have hHas := hcon.2 ho
      change Tendsto (fun N : ℕ => ∑ k ∈ range N, chapter9Entry2SineTerm r a x k)
        atTop (𝓝 (entry2Psin r a x))
      exact hHas.tendsto_sum_nat

end
end Entry2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
