/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_eq_fderivWithin_mul.lean`,
`Definitions/Def_LanglandsTunnell_JLConverse.lean`
and
`P2M/Sol/S_LanglandsTunnell_Converse_ArchDatumR_exists_W_eq_fderivWithin_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Analysis.MellinArchDatum

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Derivatives of real archimedean Whittaker data

For a real archimedean Whittaker datum `d` and a matrix `X`, the right derivative
`g ↦ D_{g X} W(g)` of its Whittaker function along `X` is again the Whittaker function
of a real archimedean Whittaker datum. The proof checks smoothness, the unipotent and
central laws, and transports the zeta integral, its entire continuation, functional
equation, finite-order growth and decay bounds through differentiation.
-/

@[expose] public section

set_option autoImplicit false

section SpanGamma
set_option autoImplicit false

open Complex ComplexConjugate
open scoped Real

namespace ArchWhittakerGrowth
namespace Gamma

private theorem cosh_le_exp_abs (u : ℝ) : Real.cosh u ≤ Real.exp |u| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_le_exp.2 (by linarith [abs_nonneg u] : -|u| ≤ |u|)]

private theorem norm_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < ‖z‖ :=
  lt_of_lt_of_le hz (Complex.re_le_norm z)

private theorem norm_Gamma_pos {s : ℂ} (hs : 0 < s.re) : 0 < ‖Gamma s‖ :=
  norm_pos_iff.2 (Gamma_ne_zero_of_re_pos hs)

private theorem ne_neg_nat_of_pos {x : ℝ} (hx : 0 < x) (j : ℕ) : x ≠ -j := by
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  intro h; linarith

private theorem ofReal_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -m := by
  intro h
  have h' : x = -m := by exact_mod_cast h
  exact ne_neg_nat_of_pos hx m h'

private theorem continuousOn_Gamma_ofReal {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun x : ℝ => Gamma (x : ℂ)) (Set.Icc A B) := by
  intro x hx
  exact ((continuousAt_Gamma (x : ℂ) (ofReal_ne_neg_nat (hA.trans_le hx.1))).comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

private theorem re_add_natCast (s : ℂ) (j : ℕ) : (s + j).re = s.re + j := by simp

private theorem norm_ofReal_add_natCast {x : ℝ} (hx : 0 < x) (j : ℕ) : ‖(x : ℂ) + j‖ = x + j := by
  have e : ((x : ℂ) + (j : ℂ)) = ((x + j : ℝ) : ℂ) := by push_cast; ring
  have h0 : (0 : ℝ) ≤ x + j := by positivity
  rw [e, Complex.norm_of_nonneg h0]

private theorem norm_ofReal_add_mul_I_add_natCast (x y : ℝ) (j : ℕ) :
    ‖(x : ℂ) + y * I + j‖ = Real.sqrt ((x + j) ^ 2 + y ^ 2) := by
  have e : ((x : ℂ) + y * I + (j : ℂ)) = ((x + j : ℝ) : ℂ) + (y : ℂ) * I := by push_cast; ring
  rw [e, Complex.norm_add_mul_I]

private theorem norm_add_natCast_le {s : ℂ} {R : ℝ} (j : ℕ) (hR : |s.re + j| ≤ R) :
    ‖s + j‖ ≤ (R + 1) * (1 + |s.im|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (s + j)
  have him : (s + j).im = s.im := by simp
  rw [re_add_natCast, him] at h1
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  nlinarith [abs_nonneg s.im, mul_nonneg hR0 (abs_nonneg s.im)]

private theorem norm_Gamma_half_sq (y : ℝ) :
    ‖Gamma (1 / 2 + y * I)‖ ^ 2 = π / Real.cosh (π * y) := by
  have h := Gamma_mul_Gamma_one_sub (1 / 2 + y * I)
  have h1 : (1 : ℂ) - (1 / 2 + y * I) = conj (1 / 2 + y * I : ℂ) := by
    apply Complex.ext <;> norm_num
  have h2 : Complex.sin ((π : ℂ) * (1 / 2 + y * I)) = (Real.cosh (π * y) : ℂ) := by
    have e : (π : ℂ) * (1 / 2 + y * I) = ((π * y : ℝ) : ℂ) * I + (π : ℂ) / 2 := by
      push_cast; ring
    rw [e, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [h1, Gamma_conj, Complex.mul_conj, h2, normSq_eq_norm_sq] at h
  exact_mod_cast h

private theorem exp_sq_eq (y : ℝ) : Real.exp (-(π / 2 * |y|)) ^ 2 = (Real.exp (π * |y|))⁻¹ := by
  rw [sq, ← Real.exp_add, ← Real.exp_neg]
  congr 1; ring

private theorem exp_le_norm_Gamma_half (y : ℝ) :
    Real.exp (-(π / 2 * |y|)) ≤ ‖Gamma (1 / 2 + y * I)‖ := by
  have hc : 0 < Real.cosh (π * y) := Real.cosh_pos _
  have hE : 0 < Real.exp (π * |y|) := Real.exp_pos _
  have h1 : Real.cosh (π * y) ≤ Real.exp (π * |y|) := by
    have h := cosh_le_exp_abs (π * y)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at h
  have hsq : Real.exp (-(π / 2 * |y|)) ^ 2 ≤ ‖Gamma (1 / 2 + y * I)‖ ^ 2 := by
    rw [norm_Gamma_half_sq, exp_sq_eq, inv_eq_one_div, div_le_div_iff₀ hE hc]
    nlinarith [Real.two_le_pi, mul_nonneg (sub_nonneg.2 Real.two_le_pi) hE.le]
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).1 hsq

private theorem norm_GammaSeq (s : ℂ) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq s n‖ =
      (n : ℝ) ^ s.re * (n.factorial : ℝ) / ∏ j ∈ Finset.range (n + 1), ‖s + j‖ := by
  rw [GammaSeq, norm_div, norm_mul, norm_natCast_cpow_of_pos hn, Complex.norm_natCast,
    Complex.norm_prod]

private theorem norm_GammaSeq_le_of_re_pos {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq s n‖ ≤ ‖GammaSeq (s.re : ℂ) n‖ := by
  rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, Complex.ofReal_re]
  refine div_le_div_of_nonneg_left (by positivity) ?_ ?_
  · refine Finset.prod_pos fun j _ => norm_pos_of_re_pos ?_
    rw [re_add_natCast, Complex.ofReal_re]; positivity
  · refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
    rw [norm_ofReal_add_natCast hs j, ← re_add_natCast]
    exact Complex.re_le_norm _

private theorem norm_Gamma_le_norm_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ ‖Gamma
    (s.re : ℂ)‖ := by
  refine le_of_tendsto_of_tendsto (GammaSeq_tendsto_Gamma s).norm
    (GammaSeq_tendsto_Gamma (s.re : ℂ)).norm ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact norm_GammaSeq_le_of_re_pos hs hn

private theorem exists_norm_Gamma_le_of_strip {A : ℝ} (B : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖Gamma s‖ ≤ K := by
  obtain ⟨K, hK⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Gamma_ofReal (B := B) hA)
  exact ⟨K, fun s h1 h2 =>
    (norm_Gamma_le_norm_Gamma_re (hA.trans_le h1)).trans (hK s.re ⟨h1, h2⟩)⟩

private theorem factor_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : ℝ) :
    a * Real.sqrt (b ^ 2 + y ^ 2) ≤ Real.sqrt (a ^ 2 + y ^ 2) * b := by
  have hb : 0 < b := ha.trans_le hab
  have h1 : (0 : ℝ) ≤ b ^ 2 + y ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ a ^ 2 + y ^ 2 := by positivity
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  nlinarith [mul_nonneg (sub_nonneg.2 (mul_le_mul hab hab ha.le hb.le)) (sq_nonneg y)]

private theorem norm_GammaSeq_mul_le {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) (y : ℝ) {n : ℕ}
    (hn : 0 < n) :
    ‖GammaSeq (x₁ + y * I) n‖ * ‖GammaSeq (x₂ : ℂ) n‖ ≤
      ‖GammaSeq (x₁ : ℂ) n‖ * ‖GammaSeq (x₂ + y * I) n‖ := by
  have hx₂ : 0 < x₂ := hx₁.trans_le hx
  have hre₁ : (x₁ + y * I : ℂ).re = x₁ := by simp
  have hre₂ : (x₂ + y * I : ℂ).re = x₂ := by simp
  rw [norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn, norm_GammaSeq _ hn]
  simp only [hre₁, hre₂, Complex.ofReal_re]
  rw [div_mul_div_comm, div_mul_div_comm]
  refine div_le_div_of_nonneg_left (by positivity) ?_ ?_
  · refine mul_pos (Finset.prod_pos fun j _ => ?_) (Finset.prod_pos fun j _ => ?_)
    · rw [norm_ofReal_add_natCast hx₁ j]; positivity
    · rw [norm_ofReal_add_mul_I_add_natCast]; positivity
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    rw [norm_ofReal_add_natCast hx₁ j, norm_ofReal_add_natCast hx₂ j,
      norm_ofReal_add_mul_I_add_natCast, norm_ofReal_add_mul_I_add_natCast]
    exact factor_le (by positivity) (by linarith) y

private theorem norm_Gamma_mul_le {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) (y : ℝ) :
    ‖Gamma (x₁ + y * I)‖ * ‖Gamma (x₂ : ℂ)‖ ≤ ‖Gamma (x₁ : ℂ)‖ * ‖Gamma (x₂ + y * I)‖ := by
  have h₁ := (GammaSeq_tendsto_Gamma (x₁ + y * I)).norm.mul (GammaSeq_tendsto_Gamma (x₂ : ℂ)).norm
  have h₂ := (GammaSeq_tendsto_Gamma (x₁ : ℂ)).norm.mul (GammaSeq_tendsto_Gamma (x₂ + y * I)).norm
  refine le_of_tendsto_of_tendsto h₁ h₂ ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact norm_GammaSeq_mul_le hx₁ hx y hn

private theorem norm_Gamma_le_div_mul {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) (y : ℝ) :
    ‖Gamma (x₁ + y * I)‖ ≤ ‖Gamma (x₁ : ℂ)‖ / ‖Gamma (x₂ : ℂ)‖ * ‖Gamma (x₂ + y * I)‖ := by
  have h₂ : 0 < ‖Gamma (x₂ : ℂ)‖ := norm_Gamma_pos (by rw [Complex.ofReal_re]; linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ h₂]
  exact norm_Gamma_mul_le hx₁ hx y

private theorem exp_mul_le_of_half_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    Real.exp (-(π / 2 * |y|)) * ‖Gamma (x : ℂ)‖ ≤ ‖Gamma (1 / 2 : ℂ)‖ * ‖Gamma (x + y * I)‖ := by
  have hcmp := norm_Gamma_mul_le (by norm_num : (0 : ℝ) < 1 / 2) hx y
  have e : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [e] at hcmp
  exact (mul_le_mul_of_nonneg_right (exp_le_norm_Gamma_half y) (norm_nonneg _)).trans hcmp

private theorem Gamma_add_nat_eq (w : ℂ) (hw : ∀ j : ℕ, w + j ≠ 0) (m : ℕ) :
    Gamma (w + m) = (∏ j ∈ Finset.range m, (w + j)) * Gamma w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Gamma_add_one _ (hw m), ih]
    ring

private theorem inv_Gamma_eq (s : ℂ) (m : ℕ) :
    (Gamma s)⁻¹ = (∏ j ∈ Finset.range m, (s + j)) * (Gamma (s + m))⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, Finset.prod_range_succ, Nat.cast_succ, ← add_assoc,
      one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s + m)]
    ring

private theorem add_natCast_ne_zero_of_re {s : ℂ} (hs : ∀ j : ℕ, s.re + j ≠ 0)
    (j : ℕ) : s + j ≠ 0 := by
  intro h
  apply hs j
  rw [← re_add_natCast, h, Complex.zero_re]

private theorem Gammaℝ_add_two_mul_nat (s : ℂ) (N : ℕ)
    (hs : ∀ j ∈ Finset.range N, s + 2 * (j : ℂ) ≠ 0) :
    Gammaℝ (s + 2 * N) = Gammaℝ s * ∏ j ∈ Finset.range N, (s + 2 * (j : ℂ)) / (2 * (π : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs' : ∀ j ∈ Finset.range N, s + 2 * (j : ℂ) ≠ 0 := fun j hj =>
      hs j (by simp only [Finset.mem_range] at hj ⊢; omega)
    have hN : s + 2 * (N : ℂ) ≠ 0 := hs N (Finset.mem_range.2 (Nat.lt_succ_self N))
    have e : s + 2 * ((N + 1 : ℕ) : ℂ) = s + 2 * (N : ℂ) + 2 := by push_cast; ring
    rw [e, Gammaℝ_add_two hN, ih hs', Finset.prod_range_succ]
    ring

private theorem Gammaℂ_add_nat (s : ℂ) (N : ℕ) (hs : ∀ j ∈ Finset.range N, s + (j : ℂ) ≠ 0) :
    Gammaℂ (s + N) = Gammaℂ s * ∏ j ∈ Finset.range N, (s + (j : ℂ)) / (2 * (π : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs' : ∀ j ∈ Finset.range N, s + (j : ℂ) ≠ 0 := fun j hj =>
      hs j (by simp only [Finset.mem_range] at hj ⊢; omega)
    have hN : s + (N : ℂ) ≠ 0 := hs N (Finset.mem_range.2 (Nat.lt_succ_self N))
    rw [Nat.cast_succ, ← add_assoc, Gammaℂ_add_one hN, ih hs', Finset.prod_range_succ]
    ring

private theorem Gammaℝ_eq_shift (N : ℕ) {s : ℂ} (hs : ∀ j : ℕ, j < N → s + 2 * (j : ℂ) ≠ 0) :
    Gammaℝ s * ∏ j ∈ Finset.range N, (s + 2 * (j : ℂ)) / (2 * (π : ℂ)) = Gammaℝ (s + 2 * N) :=
  (Gammaℝ_add_two_mul_nat s N fun j hj => hs j (Finset.mem_range.1 hj)).symm

private theorem Gammaℂ_eq_shift (N : ℕ) {s : ℂ} (hs : ∀ j : ℕ, j < N → s + (j : ℂ) ≠ 0) :
    Gammaℂ s * ∏ j ∈ Finset.range N, (s + (j : ℂ)) / (2 * (π : ℂ)) = Gammaℂ (s + N) :=
  (Gammaℂ_add_nat s N fun j hj => hs j (Finset.mem_range.1 hj)).symm

private theorem exists_norm_Gamma_le_mul_norm_Gamma {α β : ℝ} (hα : ∀ j : ℕ, α ≠ -j) (hβ : 1 ≤ β)
    (hαβ : α ≤ β) :
    ∃ C : ℝ, ∀ τ : ℝ, ‖Gamma (α + τ * I)‖ ≤ C * ‖Gamma (β + τ * I)‖ := by
  obtain ⟨m, hm0, hmβ⟩ : ∃ m : ℕ, 0 < α + m ∧ α + m ≤ β := by
    by_cases h : 0 < α
    · exact ⟨0, by simpa using h, by simpa using hαβ⟩
    · have h' : α ≤ 0 := not_lt.1 h
      refine ⟨⌊-α⌋₊ + 1, ?_, ?_⟩
      · push_cast; linarith [Nat.lt_floor_add_one (-α)]
      · push_cast; linarith [Nat.floor_le (neg_nonneg.2 h')]
  have hαj : ∀ j : ℕ, α + j ≠ 0 := fun j h => hα j (by linarith)
  have hD : 0 < ∏ j ∈ Finset.range m, |α + j| := Finset.prod_pos fun j _ => abs_pos.2 (hαj j)
  refine ⟨‖Gamma ((α + m : ℝ) : ℂ)‖ / ‖Gamma (β : ℂ)‖ / ∏ j ∈ Finset.range m, |α + j|,
    fun τ => ?_⟩
  have hre : (α + τ * I : ℂ).re = α := by simp
  have hw : ∀ j : ℕ, (α + τ * I : ℂ) + j ≠ 0 :=
    add_natCast_ne_zero_of_re fun j => by rw [hre]; exact hαj j
  have hid := Gamma_add_nat_eq (α + τ * I) hw m
  have hpt : ((α + τ * I : ℂ) + m) = ((α + m : ℝ) : ℂ) + τ * I := by push_cast; ring
  rw [hpt] at hid
  have hlow : (∏ j ∈ Finset.range m, |α + j|) * ‖Gamma (α + τ * I)‖ ≤
      ‖Gamma (((α + m : ℝ) : ℂ) + τ * I)‖ := by
    rw [hid, norm_mul, Complex.norm_prod]
    refine mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => ?_) (norm_nonneg _)
    have h := Complex.abs_re_le_norm ((α + τ * I : ℂ) + j)
    rwa [re_add_natCast, hre] at h
  have hup := norm_Gamma_le_div_mul hm0 hmβ τ
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  calc ‖Gamma (α + τ * I)‖ * ∏ j ∈ Finset.range m, |α + j|
      = (∏ j ∈ Finset.range m, |α + j|) * ‖Gamma (α + τ * I)‖ := mul_comm _ _
    _ ≤ ‖Gamma (((α + m : ℝ) : ℂ) + τ * I)‖ := hlow
    _ ≤ ‖Gamma ((α + m : ℝ) : ℂ)‖ / ‖Gamma (β : ℂ)‖ * ‖Gamma (β + τ * I)‖ := hup

private theorem exists_norm_inv_Gamma_le_of_strip (A B : ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
      ‖(Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (π / 2 * |s.im|) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / 2 ≤ A + n :=
    ⟨⌈1 / 2 - A⌉₊, by linarith [Nat.le_ceil (1 / 2 - A)]⟩
  have hGh : 0 < ‖Gamma (1 / 2 : ℂ)‖ := norm_Gamma_pos (by norm_num)
  obtain ⟨κ, hκ, hκle⟩ : ∃ κ : ℝ, 0 < κ ∧
      ∀ x : ℝ, A + n ≤ x → x ≤ B + n → κ ≤ ‖Gamma (x : ℂ)‖ := by
    by_cases hAB : A + n ≤ B + n
    · obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hAB)
        (continuousOn_Gamma_ofReal (B := B + n) (by linarith)).norm
      refine ⟨‖Gamma (x₀ : ℂ)‖, norm_Gamma_pos ?_, fun x h1 h2 => isMinOn_iff.1 hmin x ⟨h1, h2⟩⟩
      rw [Complex.ofReal_re]; linarith [hx₀.1]
    · exact ⟨1, one_pos, fun x h1 h2 => absurd (h1.trans h2) hAB⟩
  refine ⟨(|A| + |B| + n + 1) ^ n * (‖Gamma (1 / 2 : ℂ)‖ / κ), n, fun s h1 h2 => ?_⟩
  have hsn : 1 / 2 ≤ s.re + n := by linarith
  have hpt : (s + n : ℂ) = ((s.re + n : ℝ) : ℂ) + s.im * I := by
    conv_lhs => rw [← Complex.re_add_im s]
    push_cast; ring
  have hpos : 0 < ‖Gamma (s + n)‖ := norm_Gamma_pos (by rw [re_add_natCast]; linarith)
  have hlow : Real.exp (-(π / 2 * |s.im|)) * κ ≤ ‖Gamma (1 / 2 : ℂ)‖ * ‖Gamma (s + n)‖ := by
    have h := exp_mul_le_of_half_le hsn s.im
    rw [← hpt] at h
    exact (mul_le_mul_of_nonneg_left (hκle _ (by linarith) (by linarith)) (Real.exp_pos _).le).trans
        h
  have hinv : ‖Gamma (s + n)‖⁻¹ ≤ ‖Gamma (1 / 2 : ℂ)‖ / κ * Real.exp (π / 2 * |s.im|) := by
    rw [inv_le_comm₀ hpos (mul_pos (div_pos hGh hκ) (Real.exp_pos (π / 2 * |s.im|))), mul_inv,
      inv_div, ← Real.exp_neg, div_mul_eq_mul_div, div_le_iff₀ hGh]
    linarith [hlow]
  have hprod : ∏ j ∈ Finset.range n, ‖s + j‖ ≤ ((|A| + |B| + n + 1) * (1 + |s.im|)) ^ n := by
    have h : ∏ j ∈ Finset.range n, ‖s + j‖ ≤
        ∏ _j ∈ Finset.range n, (|A| + |B| + n + 1) * (1 + |s.im|) := by
      refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
      have hj' : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.1 hj).le
      refine norm_add_natCast_le j (abs_le.2 ⟨?_, ?_⟩)
      · linarith [neg_abs_le A, abs_nonneg B, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      · linarith [le_abs_self B, abs_nonneg A]
    rwa [Finset.prod_const, Finset.card_range] at h
  rw [inv_Gamma_eq s n, norm_mul, Complex.norm_prod, norm_inv]
  calc (∏ j ∈ Finset.range n, ‖s + j‖) * ‖Gamma (s + n)‖⁻¹
      ≤ ((|A| + |B| + n + 1) * (1 + |s.im|)) ^ n *
          (‖Gamma (1 / 2 : ℂ)‖ / κ * Real.exp (π / 2 * |s.im|)) :=
        mul_le_mul hprod hinv (inv_nonneg.2 (norm_nonneg _)) (by positivity)
    _ = (|A| + |B| + n + 1) ^ n * (‖Gamma (1 / 2 : ℂ)‖ / κ) * (1 + |s.im|) ^ n *
          Real.exp (π / 2 * |s.im|) := by rw [mul_pow]; ring

private theorem one_add_pow_le_exp (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) ^ N ≤ ((N : ℝ) + 1) ^ N * Real.exp (π / 2 * u) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : 1 + u ≤ ((N : ℝ) + 1) * Real.exp (u / (N + 1)) := by
    have h := Real.add_one_le_exp (u / (N + 1))
    have h' : u / (N + 1) ≤ Real.exp (u / (N + 1)) - 1 := by linarith
    rw [div_le_iff₀ hN] at h'
    nlinarith [h', hN0]
  have h2 : Real.exp (u / (N + 1)) ^ N ≤ Real.exp (π / 2 * u) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have h3 : (N : ℝ) * (u / (N + 1)) ≤ u := by
      rw [← mul_div_assoc, div_le_iff₀ hN]
      nlinarith [hu, hN0]
    nlinarith [h3, mul_le_mul_of_nonneg_right Real.one_le_pi_div_two hu]
  calc (1 + u) ^ N ≤ (((N : ℝ) + 1) * Real.exp (u / (N + 1))) ^ N :=
        pow_le_pow_left₀ (by positivity) h1 N
    _ = ((N : ℝ) + 1) ^ N * Real.exp (u / (N + 1)) ^ N := mul_pow _ _ _
    _ ≤ ((N : ℝ) + 1) ^ N * Real.exp (π / 2 * u) := mul_le_mul_of_nonneg_left h2 (by positivity)

private theorem exists_norm_inv_Gamma_le_exp_of_strip (A B : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖(Gamma s)⁻¹‖ ≤ C * Real.exp (π * |s.im|) := by
  obtain ⟨C, N, h⟩ := exists_norm_inv_Gamma_le_of_strip A B
  refine ⟨max C 0 * ((N : ℝ) + 1) ^ N, fun s h1 h2 => ?_⟩
  have hE : Real.exp (π / 2 * |s.im|) * Real.exp (π / 2 * |s.im|) = Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX : 0 ≤ (1 + |s.im|) ^ N * Real.exp (π / 2 * |s.im|) := by positivity
  have hpoly := one_add_pow_le_exp N (abs_nonneg s.im)
  calc ‖(Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (π / 2 * |s.im|) := h s h1 h2
    _ = C * ((1 + |s.im|) ^ N * Real.exp (π / 2 * |s.im|)) := by ring
    _ ≤ max C 0 * ((1 + |s.im|) ^ N * Real.exp (π / 2 * |s.im|)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    _ ≤ max C 0 * (((N : ℝ) + 1) ^ N * Real.exp (π / 2 * |s.im|) * Real.exp (π / 2 * |s.im|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le) (le_max_right _ _)
    _ = max C 0 * ((N : ℝ) + 1) ^ N * Real.exp (π * |s.im|) := by
        rw [mul_assoc (((N : ℝ) + 1) ^ N), hE]; ring

end ArchWhittakerGrowth.Gamma
end SpanGamma

section SpanStrip
set_option autoImplicit false

open Complex Set Filter Asymptotics
open scoped Real

namespace ArchWhittakerGrowth
namespace Strip

private theorem one_le_re_add {a : ℝ} {s : ℂ} (hs : a ≤ s.re) : 1 ≤ (s + ((1 - a : ℝ) : ℂ)).re := by
  rw [Complex.add_re, Complex.ofReal_re]; linarith

private theorem one_add_abs_im_le {a : ℝ} {s : ℂ} (hs : a ≤ s.re) :
    1 + |s.im| ≤ 2 * ‖s + ((1 - a : ℝ) : ℂ)‖ := by
  have h1 := Complex.re_le_norm (s + ((1 - a : ℝ) : ℂ))
  have h2 := Complex.abs_im_le_norm (s + ((1 - a : ℝ) : ℂ))
  have h3 : (s + ((1 - a : ℝ) : ℂ)).im = s.im := by simp
  rw [h3] at h2
  linarith [one_le_re_add hs]

private theorem norm_add_le_mul {a b : ℝ} (hab : a < b) {s : ℂ} (hs : a ≤ s.re) (hs' : s.re ≤ b) :
    ‖s + ((1 - a : ℝ) : ℂ)‖ ≤ (b + 1 - a) * (1 + |s.im|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (s + ((1 - a : ℝ) : ℂ))
  have h3 : (s + ((1 - a : ℝ) : ℂ)).im = s.im := by simp
  have h4 : (s + ((1 - a : ℝ) : ℂ)).re = s.re + (1 - a) := by
    rw [Complex.add_re, Complex.ofReal_re]
  rw [h3, h4, abs_of_pos (by linarith)] at h1
  nlinarith [abs_nonneg s.im, mul_nonneg (sub_pos.2 hab).le (abs_nonneg s.im)]

private theorem norm_pow_add_pos {a : ℝ} {s : ℂ} (hs : a ≤ s.re) (N : ℕ) :
    0 < ‖(s + ((1 - a : ℝ) : ℂ)) ^ N‖ := by
  rw [norm_pow]
  have h := one_le_re_add hs
  have : 0 < ‖s + ((1 - a : ℝ) : ℂ)‖ := lt_of_lt_of_le one_pos (h.trans (Complex.re_le_norm _))
  positivity

private theorem add_pow_ne_zero {a : ℝ} {s : ℂ} (hs : a ≤ s.re) (N : ℕ) :
    (s + ((1 - a : ℝ) : ℂ)) ^ N ≠ 0 :=
  norm_pos_iff.1 (norm_pow_add_pos hs N)

private theorem one_add_abs_im_pow_le {a : ℝ} {s : ℂ} (hs : a ≤ s.re) (N : ℕ) :
    (1 + |s.im|) ^ N ≤ 2 ^ N * ‖(s + ((1 - a : ℝ) : ℂ)) ^ N‖ := by
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_abs_im_le hs) N

private theorem norm_pow_add_le {a b : ℝ} (hab : a < b) {s : ℂ} (hs : a ≤ s.re) (hs' : s.re ≤ b)
    (N : ℕ) :
    ‖(s + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ ((b + 1 - a) * (1 + |s.im|)) ^ N := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le_mul hab hs hs') N

private theorem mul_le_div_mul_exp {κ : ℝ} (hκ : 0 < κ) (D : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    D * u ≤ max D 0 / κ * Real.exp (κ * u) := by
  have h1 : κ * u ≤ Real.exp (κ * u) := by linarith [Real.add_one_le_exp (κ * u)]
  have h2 : D * u ≤ max D 0 * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu
  have h3 : max D 0 * u = max D 0 / κ * (κ * u) := by field_simp
  have h4 : 0 ≤ max D 0 / κ := div_nonneg (le_max_right _ _) hκ.le
  calc D * u ≤ max D 0 * u := h2
    _ = max D 0 / κ * (κ * u) := h3
    _ ≤ max D 0 / κ * Real.exp (κ * u) := mul_le_mul_of_nonneg_left h1 h4

private theorem strip_bound_of_edges (a b : ℝ) (hab : a < b) (N : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
      DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
      (∃ C D : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C * Real.exp (D * |s.im|)) →
      (∀ s : ℂ, s.re = a ∨ s.re = b → ‖f s‖ ≤ M * (1 + |s.im|) ^ N) →
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ c * M * (1 + |s.im|) ^ N := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hb1 : 0 < b + 1 - a := by linarith
  refine ⟨2 ^ N * (b + 1 - a) ^ N, mul_pos (pow_pos two_pos N) (pow_pos hb1 N),
    fun f M hM hf hgrowth hedge s hsa hsb => ?_⟩
  obtain ⟨C, D, hCD⟩ := hgrowth
  set g : ℂ → ℂ := fun w => f w / (w + ((1 - a : ℝ) : ℂ)) ^ N
  have hcl : closure (Complex.re ⁻¹' Set.Ioo a b) = Complex.re ⁻¹' Set.Icc a b := by
    rw [Complex.closure_preimage_re, closure_Ioo hab.ne]
  have hpow_diff : Differentiable ℂ fun w : ℂ => (w + ((1 - a : ℝ) : ℂ)) ^ N :=
    (differentiable_id.add_const _).pow N
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) := by
    refine ⟨hf.differentiableOn.div hpow_diff.differentiableOn fun w hw => add_pow_ne_zero hw.1.le
        N, ?_⟩
    refine hf.continuousOn.div hpow_diff.continuous.continuousOn fun w hw => ?_
    rw [hcl] at hw
    exact add_pow_ne_zero hw.1 N
  have hκ : 0 < π / (2 * (b - a)) := by positivity
  have hκlt : π / (2 * (b - a)) < π / (b - a) :=
    div_lt_div_of_pos_left Real.pi_pos hba (by linarith)
  have hB : ∃ κ < π / (b - a), ∃ B : ℝ, g =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟
      (Complex.re ⁻¹' Set.Ioo a b)]
      fun w => Real.exp (B * Real.exp (κ * |w.im|)) := by
    refine ⟨π / (2 * (b - a)), hκlt, max D 0 / (π / (2 * (b - a))), ?_⟩
    refine IsBigO.of_bound (2 ^ N * max C 0) ?_
    rw [eventually_inf_principal]
    refine Eventually.of_forall fun w hw => ?_
    have hwa : a ≤ w.re := hw.1.le
    have hwb : w.re ≤ b := hw.2.le
    have hpos := norm_pow_add_pos hwa N
    have h1 : ‖f w‖ ≤ max C 0 * Real.exp (D * |w.im|) :=
      (hCD w hwa hwb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h2 : Real.exp (D * |w.im|) ≤
        Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |w.im|)) :=
      Real.exp_le_exp.2 (mul_le_div_mul_exp hκ D (abs_nonneg _))
    have h3 : (1 : ℝ) ≤ 2 ^ N * ‖(w + ((1 - a : ℝ) : ℂ)) ^ N‖ := by
      have := one_add_abs_im_pow_le hwa N
      exact (one_le_pow₀ (by linarith [abs_nonneg w.im])).trans this
    have hE : ‖Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |w.im|))‖ =
        Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |w.im|)) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hE]
    change ‖f w / (w + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ _
    rw [norm_div, div_le_iff₀ hpos]
    calc ‖f w‖ ≤ max C 0 * Real.exp (D * |w.im|) := h1
      _ ≤ max C 0 * Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp
          (π / (2 * (b - a)) * |w.im|)) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = max C 0 * Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |w.im|))
          * 1 :=
          (mul_one _).symm
      _ ≤ max C 0 * Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp (π / (2 * (b - a)) * |w.im|))
          *
            (2 ^ N * ‖(w + ((1 - a : ℝ) : ℂ)) ^ N‖) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ N * max C 0 * Real.exp (max D 0 / (π / (2 * (b - a))) * Real.exp
          (π / (2 * (b - a)) * |w.im|)) *
            ‖(w + ((1 - a : ℝ) : ℂ)) ^ N‖ := by ring
  have hedge' : ∀ w : ℂ, w.re = a ∨ w.re = b → ‖g w‖ ≤ 2 ^ N * M := by
    intro w hw
    have hwa : a ≤ w.re := by rcases hw with h | h <;> linarith
    have hpos := norm_pow_add_pos hwa N
    change ‖f w / (w + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ 2 ^ N * M
    rw [norm_div, div_le_iff₀ hpos]
    calc ‖f w‖ ≤ M * (1 + |w.im|) ^ N := hedge w hw
      _ ≤ M * (2 ^ N * ‖(w + ((1 - a : ℝ) : ℂ)) ^ N‖) := mul_le_mul_of_nonneg_left
          (one_add_abs_im_pow_le hwa N) hM
      _ = 2 ^ N * M * ‖(w + ((1 - a : ℝ) : ℂ)) ^ N‖ := by ring
  have hPL : ‖g s‖ ≤ 2 ^ N * M :=
    PhragmenLindelof.vertical_strip hgd hB (fun w hw => hedge' w (Or.inl hw))
      (fun w hw => hedge' w (Or.inr hw)) hsa hsb
  have hpos := norm_pow_add_pos hsa N
  have hPL' : ‖f s‖ ≤ 2 ^ N * M * ‖(s + ((1 - a : ℝ) : ℂ)) ^ N‖ := by
    have h : ‖f s / (s + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ 2 ^ N * M := hPL
    rwa [norm_div, div_le_iff₀ hpos] at h
  calc ‖f s‖ ≤ 2 ^ N * M * ‖(s + ((1 - a : ℝ) : ℂ)) ^ N‖ := hPL'
    _ ≤ 2 ^ N * M * ((b + 1 - a) * (1 + |s.im|)) ^ N :=
        mul_le_mul_of_nonneg_left (norm_pow_add_le hab hsa hsb N) (by positivity)
    _ = 2 ^ N * (b + 1 - a) ^ N * M * (1 + |s.im|) ^ N := by rw [mul_pow]; ring

end ArchWhittakerGrowth.Strip
end SpanStrip

section SpanLShift
set_option autoImplicit false

noncomputable section

open Complex
open scoped Real ComplexConjugate

namespace ArchWhittakerGrowth
namespace LShift

open ArchWhittakerGrowth.Gamma ArchWhittakerGrowth.Strip

section generic

variable {S : Set ℂ}

private theorem exists_norm_prod_le (R : Multiset ℂ) (F : ℂ → ℂ → ℂ)
    (hF : ∀ μ ∈ R, ∃ K : ℝ, ∀ s ∈ S, ‖F μ s‖ ≤ K) :
    ∃ K : ℝ, ∀ s ∈ S, ‖(R.map fun μ => F μ s).prod‖ ≤ K := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨1, fun s _ => by simp⟩
  | cons μ R ih =>
    obtain ⟨K₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ R)
    obtain ⟨K₂, h₂⟩ := ih fun μ' hμ' => hF μ' (Multiset.mem_cons_of_mem hμ')
    refine ⟨max K₁ 0 * max K₂ 0, fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_mul ((h₁ s hs).trans (le_max_left _ _)) ((h₂ s hs).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)

private theorem exists_norm_prod_le_exp (R : Multiset ℂ) (F : ℂ → ℂ → ℂ)
    (hF : ∀ μ ∈ R, ∃ K c : ℝ, ∀ s ∈ S, ‖F μ s‖ ≤ K * Real.exp (c * |s.im|)) :
    ∃ K c : ℝ, ∀ s ∈ S, ‖(R.map fun μ => F μ s).prod‖ ≤ K * Real.exp (c * |s.im|) := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨1, 0, fun s _ => by simp⟩
  | cons μ R ih =>
    obtain ⟨K₁, c₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ R)
    obtain ⟨K₂, c₂, h₂⟩ := ih fun μ' hμ' => hF μ' (Multiset.mem_cons_of_mem hμ')
    refine ⟨max K₁ 0 * max K₂ 0, c₁ + c₂, fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have e₁ : ‖F μ s‖ ≤ max K₁ 0 * Real.exp (c₁ * |s.im|) :=
      (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have e₂ : ‖(R.map fun μ => F μ s).prod‖ ≤ max K₂ 0 * Real.exp (c₂ * |s.im|) :=
      (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖F μ s‖ * ‖(R.map fun μ => F μ s).prod‖
        ≤ (max K₁ 0 * Real.exp (c₁ * |s.im|)) * (max K₂ 0 * Real.exp (c₂ * |s.im|)) :=
          mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = max K₁ 0 * max K₂ 0 * (Real.exp (c₁ * |s.im|) * Real.exp (c₂ * |s.im|)) := by ring
      _ = max K₁ 0 * max K₂ 0 * Real.exp ((c₁ + c₂) * |s.im|) := by
          rw [← Real.exp_add]; congr 2; ring

private theorem exists_norm_prod_le_pow (R : Multiset ℂ) (F : ℂ → ℂ → ℂ) (n : ℕ)
    (hF : ∀ μ ∈ R, ∃ K : ℝ, ∀ s ∈ S, ‖F μ s‖ ≤ K * (1 + |s.im|) ^ n) :
    ∃ K : ℝ, ∀ s ∈ S, ‖(R.map fun μ => F μ s).prod‖ ≤ K * (1 + |s.im|) ^ (n * Multiset.card R) := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨1, fun s _ => by simp⟩
  | cons μ R ih =>
    obtain ⟨K₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ R)
    obtain ⟨K₂, h₂⟩ := ih fun μ' hμ' => hF μ' (Multiset.mem_cons_of_mem hμ')
    refine ⟨max K₁ 0 * max K₂ 0, fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, Nat.mul_succ, pow_add]
    have e₁ : ‖F μ s‖ ≤ max K₁ 0 * (1 + |s.im|) ^ n :=
      (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have e₂ : ‖(R.map fun μ => F μ s).prod‖ ≤ max K₂ 0 * (1 + |s.im|) ^ (n * Multiset.card R) :=
      (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    calc ‖F μ s‖ * ‖(R.map fun μ => F μ s).prod‖
        ≤ (max K₁ 0 * (1 + |s.im|) ^ n) * (max K₂ 0 * (1 + |s.im|) ^ (n * Multiset.card R)) :=
          mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = max K₁ 0 * max K₂ 0 * ((1 + |s.im|) ^ (n * Multiset.card R) * (1 + |s.im|) ^ n) := by ring

private theorem differentiableOn_prod (U : Set ℂ) (R : Multiset ℂ) (F : ℂ → ℂ → ℂ)
    (hF : ∀ μ ∈ R, DifferentiableOn ℂ (F μ) U) :
    DifferentiableOn ℂ (fun s => (R.map fun μ => F μ s).prod) U := by
  induction R using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact differentiableOn_const 1
  | cons μ R ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (hF μ (Multiset.mem_cons_self μ R)).mul (ih fun μ' hμ' => hF μ'
        (Multiset.mem_cons_of_mem hμ'))

private theorem prod_map_mul_prod_map_eq (R : Multiset ℂ) (F G H : ℂ → ℂ)
    (h : ∀ μ ∈ R, F μ * G μ = H μ) :
    (R.map F).prod * (R.map G).prod = (R.map H).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons μ R ih =>
    have ih' := ih fun μ' hμ' => h μ' (Multiset.mem_cons_of_mem hμ')
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← h μ (Multiset.mem_cons_self μ R), ← ih']
    ring

end generic

private def gammaFactor (R C : Multiset ℂ) (s : ℂ) : ℂ :=
  (R.map fun μ => Gammaℝ (s + μ)).prod * (C.map fun ν => Gammaℂ (s + ν)).prod

private def shiftFactor (R C : Multiset ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  (R.map fun μ => Gammaℝ (s + μ + 2 * N)).prod * (C.map fun ν => Gammaℂ (s + ν + N)).prod

private def polyR (N : ℕ) (w : ℂ) : ℂ := ∏ j ∈ Finset.range N, (w + 2 * (j : ℂ)) / (2 * (π : ℂ))

private def polyC (N : ℕ) (w : ℂ) : ℂ := ∏ j ∈ Finset.range N, (w + (j : ℂ)) / (2 * (π : ℂ))

private def shiftPoly (R C : Multiset ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  (R.map fun μ => polyR N (s + μ)).prod * (C.map fun ν => polyC N (s + ν)).prod

private def OffPoles (R C : Multiset ℂ) (N : ℕ) (s : ℂ) : Prop :=
  (∀ μ ∈ R, ∀ j : ℕ, j < N → s + μ + 2 * (j : ℂ) ≠ 0) ∧
      (∀ ν ∈ C, ∀ j : ℕ, j < N → s + ν + (j : ℂ) ≠ 0)

private theorem offPoles_of_re {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re)
    (N : ℕ) {s : ℂ} (hs : A ≤ s.re) : OffPoles R C N s := by
  refine ⟨fun μ hμ j _ h => ?_, fun ν hν j _ h => ?_⟩
  · have hre : (s + μ + 2 * (j : ℂ)).re = s.re + μ.re + 2 * j := by simp
    have h0 : (s + μ + 2 * (j : ℂ)).re = 0 := by rw [h, Complex.zero_re]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have := hR μ hμ
    rw [hre] at h0
    linarith
  · have hre : (s + ν + (j : ℂ)).re = s.re + ν.re + j := by simp
    have h0 : (s + ν + (j : ℂ)).re = 0 := by rw [h, Complex.zero_re]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have := hC ν hν
    rw [hre] at h0
    linarith

private theorem gammaFactor_mul_shiftPoly (R C : Multiset ℂ) (N : ℕ) {s : ℂ}
    (h : OffPoles R C N s) :
    gammaFactor R C s * shiftPoly R C N s = shiftFactor R C N s := by
  unfold gammaFactor shiftPoly shiftFactor
  rw [mul_mul_mul_comm]
  congr 1
  · exact prod_map_mul_prod_map_eq R _ _ _ fun μ hμ => Gammaℝ_eq_shift N (h.1 μ hμ)
  · exact prod_map_mul_prod_map_eq C _ _ _ fun ν hν => Gammaℂ_eq_shift N (h.2 ν hν)

private theorem differentiableAt_Gammaℝ_of_re_pos {w : ℂ}
    (hw : 0 < w.re) : DifferentiableAt ℂ Gammaℝ w := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) w :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) w := by
    have hpole : ∀ m : ℕ, w / 2 ≠ -m := by
      intro m h
      have h' := congrArg Complex.re h
      rw [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at h'
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (differentiableAt_Gamma _ hpole).comp w (differentiableAt_id.div_const 2)
  exact h1.mul h2

private theorem differentiableAt_Gammaℂ_of_re_pos {w : ℂ}
    (hw : 0 < w.re) : DifferentiableAt ℂ Gammaℂ w := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (2 * (π : ℂ)) ^ (-z)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl (by simp [Real.pi_ne_zero]))
  have hpole : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have h' := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at h'
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact (h1.const_mul 2).mul (differentiableAt_Gamma w hpole)

private theorem norm_Gammaℝ (w : ℂ) : ‖Gammaℝ w‖ = π ^ (-w.re / 2) * ‖Gamma (w / 2)‖ := by
  have e : (-w / 2).re = -w.re / 2 := by simp
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, e]

private theorem norm_Gammaℂ (w : ℂ) : ‖Gammaℂ w‖ = 2 * (2 * π) ^ (-w.re) * ‖Gamma w‖ := by
  have e : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, norm_mul, norm_mul, e, norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.neg_re,
    Complex.norm_ofNat]

private theorem exists_norm_Gammaℝ_shift_le {A : ℝ} (B : ℝ) (μ : ℂ) (N : ℕ)
    (h : 0 < A + μ.re + 2 * N) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖Gammaℝ (s + μ + 2 * N)‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_norm_Gamma_le_of_strip (A := (A + μ.re + 2 * N) / 2)
      ((B + μ.re + 2 * N) / 2)
    (by positivity)
  refine ⟨π ^ (-(A + μ.re + 2 * N) / 2) * max K 0, fun s hsA hsB => ?_⟩
  have hre : (s + μ + 2 * (N : ℂ)).re = s.re + μ.re + 2 * N := by simp
  have hre2 : ((s + μ + 2 * (N : ℂ)) / 2).re = (s.re + μ.re + 2 * N) / 2 := by
    rw [Complex.div_ofNat_re, hre]
  rw [norm_Gammaℝ, hre]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  · refine (hK _ ?_ ?_).trans (le_max_left _ _) <;> rw [hre2] <;> linarith

private theorem exists_norm_Gammaℂ_shift_le {A : ℝ} (B : ℝ) (ν : ℂ) (N : ℕ) (h : 0 < A + ν.re + N) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖Gammaℂ (s + ν + N)‖ ≤ K := by
  obtain ⟨K, hK⟩ := exists_norm_Gamma_le_of_strip (A := A + ν.re + N) (B + ν.re + N) h
  refine ⟨2 * (2 * π) ^ (-(A + ν.re + N)) * max K 0, fun s hsA hsB => ?_⟩
  have hre : (s + ν + (N : ℂ)).re = s.re + ν.re + N := by simp
  rw [norm_Gammaℂ, hre]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · refine mul_le_mul_of_nonneg_left ?_ two_pos.le
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  · refine (hK _ ?_ ?_).trans (le_max_left _ _) <;> rw [hre] <;> linarith

private theorem exists_norm_inv_Gammaℝ_shift_le (A B : ℝ) (μ : ℂ) (N : ℕ) :
    ∃ K c : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖(Gammaℝ (s + μ + 2 * N))⁻¹‖ ≤ K * Real.exp
        (c * |s.im|) := by
  obtain ⟨K, hK⟩ := exists_norm_inv_Gamma_le_exp_of_strip ((A + μ.re + 2 * N) / 2)
      ((B + μ.re + 2 * N) / 2)
  refine ⟨π ^ ((B + μ.re + 2 * N) / 2) * (max K 0 * Real.exp (π * (|μ.im| / 2))), π / 2,
    fun s hsA hsB => ?_⟩
  have hre : (s + μ + 2 * (N : ℂ)).re = s.re + μ.re + 2 * N := by simp
  have hre2 : ((s + μ + 2 * (N : ℂ)) / 2).re = (s.re + μ.re + 2 * N) / 2 := by
    rw [Complex.div_ofNat_re, hre]
  have him2 : ((s + μ + 2 * (N : ℂ)) / 2).im = (s.im + μ.im) / 2 := by
    rw [Complex.div_ofNat_im]; simp
  rw [norm_inv, norm_Gammaℝ, hre, mul_inv, ← Real.rpow_neg Real.pi_pos.le, ← norm_inv]
  have h1 : π ^ (-(-(s.re + μ.re + 2 * N) / 2)) ≤ π ^ ((B + μ.re + 2 * N) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  have h2 : ‖(Gamma ((s + μ + 2 * (N : ℂ)) / 2))⁻¹‖ ≤ max K 0 * Real.exp (π * (|μ.im| / 2)) *
      Real.exp (π / 2 * |s.im|) := by
    have h := hK _ (by rw [hre2]; linarith) (by rw [hre2]; linarith)
    rw [him2] at h
    refine h.trans ?_
    have habs : |(s.im + μ.im) / 2| ≤ |s.im| / 2 + |μ.im| / 2 := by
      rw [abs_div, abs_two]; linarith [abs_add_le s.im μ.im]
    have hexp : Real.exp (π * |(s.im + μ.im) / 2|) ≤
        Real.exp (π * (|μ.im| / 2)) * Real.exp (π / 2 * |s.im|) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [Real.pi_pos, habs]
    calc K * Real.exp (π * |(s.im + μ.im) / 2|)
        ≤ max K 0 * Real.exp (π * |(s.im + μ.im) / 2|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max K 0 * (Real.exp (π * (|μ.im| / 2)) * Real.exp (π / 2 * |s.im|)) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
      _ = max K 0 * Real.exp (π * (|μ.im| / 2)) * Real.exp (π / 2 * |s.im|) := by ring
  calc π ^ (-(-(s.re + μ.re + 2 * N) / 2)) * ‖(Gamma ((s + μ + 2 * (N : ℂ)) / 2))⁻¹‖
      ≤ π ^ ((B + μ.re + 2 * N) / 2) *
          (max K 0 * Real.exp (π * (|μ.im| / 2)) * Real.exp (π / 2 * |s.im|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = π ^ ((B + μ.re + 2 * N) / 2) * (max K 0 * Real.exp (π * (|μ.im| / 2))) *
          Real.exp (π / 2 * |s.im|) := by ring

private theorem exists_norm_inv_Gammaℂ_shift_le (A B : ℝ) (ν : ℂ) (N : ℕ) :
    ∃ K c : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖(Gammaℂ (s + ν + N))⁻¹‖ ≤ K * Real.exp
        (c * |s.im|) := by
  obtain ⟨K, hK⟩ := exists_norm_inv_Gamma_le_exp_of_strip (A + ν.re + N) (B + ν.re + N)
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ⟨2⁻¹ * (2 * π) ^ (B + ν.re + N) * (max K 0 * Real.exp (π * |ν.im|)), π,
      fun s hsA hsB => ?_⟩
  have hre : (s + ν + (N : ℂ)).re = s.re + ν.re + N := by simp
  have him : (s + ν + (N : ℂ)).im = s.im + ν.im := by simp
  rw [norm_inv, norm_Gammaℂ, hre, mul_inv, mul_inv, ← Real.rpow_neg (by positivity), neg_neg,
      ← norm_inv]
  have h1 : (2 * π) ^ (s.re + ν.re + N) ≤ (2 * π) ^ (B + ν.re + N) :=
    Real.rpow_le_rpow_of_exponent_le h2π (by linarith)
  have h2 : ‖(Gamma (s + ν + N))⁻¹‖ ≤ max K 0 * Real.exp (π * |ν.im|) * Real.exp (π * |s.im|) := by
    have h := hK _ (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at h
    refine h.trans ?_
    have hexp : Real.exp (π * |s.im + ν.im|) ≤ Real.exp (π * |ν.im|) * Real.exp (π * |s.im|) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [Real.pi_pos, abs_add_le s.im ν.im]
    calc K * Real.exp (π * |s.im + ν.im|)
        ≤ max K 0 * Real.exp (π * |s.im + ν.im|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max K 0 * (Real.exp (π * |ν.im|) * Real.exp (π * |s.im|)) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
      _ = max K 0 * Real.exp (π * |ν.im|) * Real.exp (π * |s.im|) := by ring
  calc 2⁻¹ * (2 * π) ^ (s.re + ν.re + N) * ‖(Gamma (s + ν + N))⁻¹‖
      ≤ 2⁻¹ * (2 * π) ^ (B + ν.re + N) * (max K 0 * Real.exp (π * |ν.im|) * Real.exp
          (π * |s.im|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (norm_nonneg _) (by positivity)
    _ = 2⁻¹ * (2 * π) ^ (B + ν.re + N) * (max K 0 * Real.exp (π * |ν.im|)) * Real.exp
        (π * |s.im|) := by
        ring

private theorem norm_linear_le {A B : ℝ} (μ c : ℂ) {s : ℂ} (hsA : A ≤ s.re) (hsB : s.re ≤ B) :
    ‖s + μ + c‖ ≤ (|A| + |B| + ‖μ‖ + ‖c‖ + 1) * (1 + |s.im|) := by
  have h1 : ‖s + μ + c‖ ≤ ‖s‖ + ‖μ‖ + ‖c‖ := norm_add₃_le
  have h2 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h3 : |s.re| ≤ |A| + |B| := by
    rw [abs_le]; constructor <;> linarith [neg_abs_le A, le_abs_self B, abs_nonneg A, abs_nonneg B]
  nlinarith [abs_nonneg s.im, norm_nonneg μ, norm_nonneg c, abs_nonneg A, abs_nonneg B,
    mul_nonneg (add_nonneg (add_nonneg (add_nonneg (abs_nonneg A) (abs_nonneg B)) (norm_nonneg μ))
      (norm_nonneg c)) (abs_nonneg s.im)]

private theorem norm_div_two_pi_le (z : ℂ) : ‖z / (2 * (π : ℂ))‖ ≤ ‖z‖ := by
  rw [norm_div]
  have e : ‖(2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [e]
  exact div_le_self (norm_nonneg _) (by linarith [Real.two_le_pi])

private theorem exists_norm_polyR_le (A B : ℝ) (μ : ℂ) (N : ℕ) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖polyR N (s + μ)‖ ≤ K * (1 + |s.im|) ^ N := by
  refine ⟨(|A| + |B| + ‖μ‖ + (2 * N) + 1) ^ N, fun s hsA hsB => ?_⟩
  unfold polyR
  rw [Complex.norm_prod, ← mul_pow, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hj).le
  refine (norm_div_two_pi_le _).trans ((norm_linear_le μ (2 * (j : ℂ)) hsA hsB).trans ?_)
  have hc : ‖(2 * (j : ℂ))‖ ≤ 2 * N := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]; linarith
  have h0 : 0 ≤ 1 + |s.im| := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) h0

private theorem exists_norm_polyC_le (A B : ℝ) (ν : ℂ) (N : ℕ) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖polyC N (s + ν)‖ ≤ K * (1 + |s.im|) ^ N := by
  refine ⟨(|A| + |B| + ‖ν‖ + N + 1) ^ N, fun s hsA hsB => ?_⟩
  unfold polyC
  rw [Complex.norm_prod, ← mul_pow, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j hj => ?_
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hj).le
  refine (norm_div_two_pi_le _).trans ((norm_linear_le ν (j : ℂ) hsA hsB).trans ?_)
  have hc : ‖(j : ℂ)‖ ≤ N := by rw [Complex.norm_natCast]; exact hjN
  have h0 : 0 ≤ 1 + |s.im| := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) h0

private def _root_.ArchWhittakerGrowth.LShift.strip (A B : ℝ) : Set ℂ := {s | A ≤ s.re ∧ s.re ≤ B}

private def ShiftsPos (R C : Multiset ℂ) (N : ℕ) (A : ℝ) : Prop :=
  (∀ μ ∈ R, 0 < A + μ.re + 2 * N) ∧ (∀ ν ∈ C, 0 < A + ν.re + N)

private theorem exists_le_of_multiset (R : Multiset ℂ) (g : ℂ → ℝ) : ∃ L : ℝ, ∀ μ ∈ R, g μ ≤ L := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨0, fun μ hμ => by simp at hμ⟩
  | cons μ R ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨max (g μ) L, fun μ' hμ' => ?_⟩
    rcases Multiset.mem_cons.1 hμ' with rfl | hμ'
    · exact le_max_left _ _
    · exact (hL μ' hμ').trans (le_max_right _ _)

private theorem exists_shiftsPos (R C : Multiset ℂ) (A : ℝ) : ∃ N : ℕ, ShiftsPos R C N A := by
  obtain ⟨L₁, hL₁⟩ := exists_le_of_multiset R fun μ => -(A + μ.re)
  obtain ⟨L₂, hL₂⟩ := exists_le_of_multiset C fun ν => -(A + ν.re)
  refine ⟨⌈max L₁ L₂⌉₊ + 1, fun μ hμ => ?_, fun ν hν => ?_⟩
  · have h1 : -(A + μ.re) ≤ L₁ := hL₁ μ hμ
    have h2 : L₁ ≤ ⌈max L₁ L₂⌉₊ := (le_max_left L₁ L₂).trans (Nat.le_ceil _)
    push_cast
    linarith
  · have h1 : -(A + ν.re) ≤ L₂ := hL₂ ν hν
    have h2 : L₂ ≤ ⌈max L₁ L₂⌉₊ := (le_max_right L₁ L₂).trans (Nat.le_ceil _)
    push_cast
    linarith

private theorem shiftsPos_mono {R C : Multiset ℂ} {N : ℕ} {A A' : ℝ} (h : ShiftsPos R C N A)
    (hAA' : A ≤ A') :
    ShiftsPos R C N A' :=
  ⟨fun μ hμ => by linarith [h.1 μ hμ], fun ν hν => by linarith [h.2 ν hν]⟩

private theorem differentiableOn_shiftFactor {R C : Multiset ℂ} {N : ℕ} {A : ℝ}
    (h : ShiftsPos R C N A) :
    DifferentiableOn ℂ (shiftFactor R C N) {s : ℂ | A < s.re} := by
  unfold shiftFactor
  refine (differentiableOn_prod _ R (fun μ s => Gammaℝ (s + μ + 2 * N)) fun μ hμ => ?_).mul
    (differentiableOn_prod _ C (fun ν s => Gammaℂ (s + ν + N)) fun ν hν => ?_)
  · intro s hs
    have hre : 0 < (s + μ + 2 * (N : ℂ)).re := by
      simp only [Set.mem_ofPred_eq] at hs
      have := h.1 μ hμ
      simp; linarith
    exact ((differentiableAt_Gammaℝ_of_re_pos hre).comp s
      ((differentiableAt_id.add_const μ).add_const _)).differentiableWithinAt
  · intro s hs
    have hre : 0 < (s + ν + (N : ℂ)).re := by
      simp only [Set.mem_ofPred_eq] at hs
      have := h.2 ν hν
      simp; linarith
    exact ((differentiableAt_Gammaℂ_of_re_pos hre).comp s
      ((differentiableAt_id.add_const ν).add_const _)).differentiableWithinAt

private theorem exists_norm_shiftFactor_le {R C : Multiset ℂ} {N : ℕ} {A : ℝ} (B : ℝ)
    (h : ShiftsPos R C N A) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖shiftFactor R C N s‖ ≤ K := by
  obtain ⟨K₁, h₁⟩ := exists_norm_prod_le (S := strip A B) R (fun μ s => Gammaℝ (s + μ + 2 * N))
    fun μ hμ => by
      obtain ⟨K, hK⟩ := exists_norm_Gammaℝ_shift_le B μ N (h.1 μ hμ)
      exact ⟨K, fun s hs => hK s hs.1 hs.2⟩
  obtain ⟨K₂, h₂⟩ := exists_norm_prod_le (S := strip A B) C (fun ν s => Gammaℂ (s + ν + N))
    fun ν hν => by
      obtain ⟨K, hK⟩ := exists_norm_Gammaℂ_shift_le B ν N (h.2 ν hν)
      exact ⟨K, fun s hs => hK s hs.1 hs.2⟩
  refine ⟨max K₁ 0 * max K₂ 0, fun s hsA hsB => ?_⟩
  have hs : s ∈ strip A B := ⟨hsA, hsB⟩
  unfold shiftFactor
  rw [norm_mul]
  exact mul_le_mul ((h₁ s hs).trans (le_max_left _ _)) ((h₂ s hs).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private theorem exists_norm_inv_shiftFactor_le (R C : Multiset ℂ) (N : ℕ) (A B : ℝ) :
    ∃ K c : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖(shiftFactor R C N s)⁻¹‖ ≤ K * Real.exp
        (c * |s.im|) := by
  obtain ⟨K₁, c₁, h₁⟩ := exists_norm_prod_le_exp (S := strip A B) R
    (fun μ s => (Gammaℝ (s + μ + 2 * N))⁻¹) fun μ _ => by
      obtain ⟨K, c, hK⟩ := exists_norm_inv_Gammaℝ_shift_le A B μ N
      exact ⟨K, c, fun s hs => hK s hs.1 hs.2⟩
  obtain ⟨K₂, c₂, h₂⟩ := exists_norm_prod_le_exp (S := strip A B) C
    (fun ν s => (Gammaℂ (s + ν + N))⁻¹) fun ν _ => by
      obtain ⟨K, c, hK⟩ := exists_norm_inv_Gammaℂ_shift_le A B ν N
      exact ⟨K, c, fun s hs => hK s hs.1 hs.2⟩
  refine ⟨max K₁ 0 * max K₂ 0, c₁ + c₂, fun s hsA hsB => ?_⟩
  have hs : s ∈ strip A B := ⟨hsA, hsB⟩
  unfold shiftFactor
  rw [mul_inv, ← Multiset.prod_map_inv, ← Multiset.prod_map_inv, norm_mul]
  have e₁ := (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₁ 0) (Real.exp_pos _).le)
  have e₂ := (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₂ 0) (Real.exp_pos _).le)
  calc _ ≤ (max K₁ 0 * Real.exp (c₁ * |s.im|)) * (max K₂ 0 * Real.exp (c₂ * |s.im|)) :=
        mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
    _ = max K₁ 0 * max K₂ 0 * (Real.exp (c₁ * |s.im|) * Real.exp (c₂ * |s.im|)) := by ring
    _ = max K₁ 0 * max K₂ 0 * Real.exp ((c₁ + c₂) * |s.im|) := by rw [← Real.exp_add]; congr 2; ring

private theorem exists_norm_shiftPoly_le (R C : Multiset ℂ) (N : ℕ) (A B : ℝ) :
    ∃ K : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
      ‖shiftPoly R C N s‖ ≤ K * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C) := by
  obtain ⟨K₁, h₁⟩ := exists_norm_prod_le_pow (S := strip A B) R (fun μ s => polyR N (s + μ)) N
    fun μ _ => by
      obtain ⟨K, hK⟩ := exists_norm_polyR_le A B μ N
      exact ⟨K, fun s hs => hK s hs.1 hs.2⟩
  obtain ⟨K₂, h₂⟩ := exists_norm_prod_le_pow (S := strip A B) C (fun ν s => polyC N (s + ν)) N
    fun ν _ => by
      obtain ⟨K, hK⟩ := exists_norm_polyC_le A B ν N
      exact ⟨K, fun s hs => hK s hs.1 hs.2⟩
  refine ⟨max K₁ 0 * max K₂ 0, fun s hsA hsB => ?_⟩
  have hs : s ∈ strip A B := ⟨hsA, hsB⟩
  unfold shiftPoly
  rw [norm_mul, pow_add]
  have e₁ := (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₁ 0) (by positivity))
  have e₂ := (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₂ 0) (by positivity))
  calc _ ≤ (max K₁ 0 * (1 + |s.im|) ^ (N * Multiset.card R)) *
        (max K₂ 0 * (1 + |s.im|) ^ (N * Multiset.card C)) :=
        mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
    _ = _ := by ring

private def OffPoleAbscissae (R C : Multiset ℂ) (A : ℝ) : Prop :=
  (∀ μ ∈ R, ∀ j : ℕ, A + μ.re + 2 * j ≠ 0) ∧ (∀ ν ∈ C, ∀ j : ℕ, A + ν.re + j ≠ 0)

private theorem OffPoleAbscissae.offPoles {R C : Multiset ℂ} {A : ℝ} (h : OffPoleAbscissae R C A)
    (N : ℕ) {s : ℂ}
    (hs : s.re = A) : OffPoles R C N s := by
  refine ⟨fun μ hμ j _ h0 => h.1 μ hμ j ?_, fun ν hν j _ h0 => h.2 ν hν j ?_⟩
  · have hre : (s + μ + 2 * (j : ℂ)).re = s.re + μ.re + 2 * j := by simp
    have h1 : (s + μ + 2 * (j : ℂ)).re = 0 := by rw [h0, Complex.zero_re]
    rw [hre, hs] at h1
    exact h1
  · have hre : (s + ν + (j : ℂ)).re = s.re + ν.re + j := by simp
    have h1 : (s + ν + (j : ℂ)).re = 0 := by rw [h0, Complex.zero_re]
    rw [hre, hs] at h1
    exact h1

private theorem exists_left_edge (R C : Multiset ℂ) (L : ℝ) : ∃ A : ℝ, A < L ∧
    OffPoleAbscissae R C A := by
  let bad : Set ℝ :=
    (⋃ μ : R.toFinset, Set.range fun j : ℕ => -(μ : ℂ).re - 2 * j) ∪
      ⋃ ν : C.toFinset, Set.range fun j : ℕ => -(ν : ℂ).re - j
  have hbad : bad.Countable :=
    (Set.countable_iUnion fun _ => Set.countable_range _).union
      (Set.countable_iUnion fun _ => Set.countable_range _)
  obtain ⟨A, hA, hAL⟩ := (hbad.dense_compl ℝ).exists_mem_open (isOpen_Iio (a := L)) ⟨L - 1, by simp⟩
  have hA' : A ∉ bad := hA
  have hAL' : A < L := hAL
  refine ⟨A, hAL', fun μ hμ j hj => hA' ?_, fun ν hν j hj => hA' ?_⟩
  · exact Or.inl (Set.mem_iUnion.2 ⟨⟨μ, Multiset.mem_toFinset.2 hμ⟩, ⟨j, by beta_reduce; linarith⟩⟩)
  · exact Or.inr (Set.mem_iUnion.2 ⟨⟨ν, Multiset.mem_toFinset.2 hν⟩, ⟨j, by beta_reduce; linarith⟩⟩)

private def Paired (μ μ' : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ μ' = -μ + r

private def FarLeft (R C : Multiset ℂ) (A : ℝ) : Prop := (∀ μ ∈ R, A + μ.re ≤ -1) ∧
    (∀ ν ∈ C, A + ν.re ≤ -1)

private theorem exists_left_edge' (R C : Multiset ℂ) (L : ℝ) :
    ∃ A : ℝ, A < L ∧ OffPoleAbscissae R C A ∧ FarLeft R C A := by
  obtain ⟨L₁, hL₁⟩ := exists_le_of_multiset R fun μ => μ.re
  obtain ⟨L₂, hL₂⟩ := exists_le_of_multiset C fun ν => ν.re
  obtain ⟨A, hA, hoff⟩ := exists_left_edge R C (min L (min (-1 - L₁) (-1 - L₂)))
  have h1 : A < L := hA.trans_le (min_le_left _ _)
  have h2 : A < -1 - L₁ := hA.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : A < -1 - L₂ := hA.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨A, h1, hoff, fun μ hμ => ?_, fun ν hν => ?_⟩
  · have : μ.re ≤ L₁ := hL₁ μ hμ
    linarith
  · have : ν.re ≤ L₂ := hL₂ ν hν
    linarith

private theorem norm_Gamma_neg_im (β y : ℝ) : ‖Gamma ((β : ℂ) + ((-y : ℝ) : ℂ) * I)‖ = ‖Gamma
    ((β : ℂ) + (y : ℂ) * I)‖ := by
  have e : (β : ℂ) + ((-y : ℝ) : ℂ) * I = (starRingEnd ℂ) ((β : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [e, Gamma_conj, Complex.norm_conj]

private theorem exists_norm_Gammaℝ_le_paired {μ μ' : ℂ} (hp : Paired μ μ') {A : ℝ}
    (hoff : ∀ j : ℕ, A + μ.re + 2 * j ≠ 0) (hfar : A + μ.re ≤ -1) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = A → ‖Gammaℝ (s + μ)‖ ≤ K * ‖Gammaℝ (1 - s + μ')‖ := by
  obtain ⟨r, hr, rfl⟩ := hp
  have hα : ∀ j : ℕ, (A + μ.re) / 2 ≠ -j := by
    intro j h
    apply hoff j
    linarith
  have hβ : (1 : ℝ) ≤ (1 - (A + μ.re) + r) / 2 := by linarith
  have hαβ : (A + μ.re) / 2 ≤ (1 - (A + μ.re) + r) / 2 := by linarith
  obtain ⟨K₀, hK₀⟩ := exists_norm_Gamma_le_mul_norm_Gamma hα hβ hαβ
  have hπ' : (0 : ℝ) < π ^ (-(1 - (A + μ.re) + r) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨π ^ (-(A + μ.re) / 2) * K₀ / π ^ (-(1 - (A + μ.re) + r) / 2), fun s hs => ?_⟩
  have hre₁ : (s + μ).re = A + μ.re := by simp [hs]
  have hre₂ : (1 - s + (-μ + (r : ℂ))).re = 1 - (A + μ.re) + r := by simp [hs]; ring
  have hpt₁ : (s + μ) / 2 = (((A + μ.re) / 2 : ℝ) : ℂ) + (((s.im + μ.im) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hs]
  have hpt₂ : (1 - s + (-μ + (r : ℂ))) / 2 =
      (((1 - (A + μ.re) + r) / 2 : ℝ) : ℂ) + ((-((s.im + μ.im) / 2) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hs] <;> ring
  rw [norm_Gammaℝ, norm_Gammaℝ, hre₁, hre₂, hpt₁, hpt₂, norm_Gamma_neg_im]
  calc π ^ (-(A + μ.re) / 2) * ‖Gamma ((((A + μ.re) / 2 : ℝ) : ℂ) +
         (((s.im + μ.im) / 2 : ℝ) : ℂ) * I)‖
      ≤ π ^ (-(A + μ.re) / 2) *
          (K₀ * ‖Gamma ((((1 - (A + μ.re) + r) / 2 : ℝ) : ℂ) +
              (((s.im + μ.im) / 2 : ℝ) : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left (hK₀ _) (Real.rpow_nonneg Real.pi_pos.le _)
    _ = π ^ (-(A + μ.re) / 2) * K₀ / π ^ (-(1 - (A + μ.re) + r) / 2) *
          (π ^ (-(1 - (A + μ.re) + r) / 2) *
            ‖Gamma ((((1 - (A + μ.re) + r) / 2 : ℝ) : ℂ) +
                (((s.im + μ.im) / 2 : ℝ) : ℂ) * I)‖) := by
        field_simp

private theorem exists_norm_Gammaℂ_le_paired {ν ν' : ℂ} (hp : Paired ν ν') {A : ℝ}
    (hoff : ∀ j : ℕ, A + ν.re + j ≠ 0) (hfar : A + ν.re ≤ -1) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = A → ‖Gammaℂ (s + ν)‖ ≤ K * ‖Gammaℂ (1 - s + ν')‖ := by
  obtain ⟨r, hr, rfl⟩ := hp
  have hα : ∀ j : ℕ, A + ν.re ≠ -j := by
    intro j h
    apply hoff j
    linarith
  have hβ : (1 : ℝ) ≤ 1 - (A + ν.re) + r := by linarith
  have hαβ : A + ν.re ≤ 1 - (A + ν.re) + r := by linarith
  obtain ⟨K₀, hK₀⟩ := exists_norm_Gamma_le_mul_norm_Gamma hα hβ hαβ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hπ' : (0 : ℝ) < 2 * (2 * π) ^ (-(1 - (A + ν.re) + r)) := by
    have := Real.rpow_pos_of_pos h2π (-(1 - (A + ν.re) + r)); positivity
  refine ⟨2 * (2 * π) ^ (-(A + ν.re)) * K₀ / (2 * (2 * π) ^ (-(1 - (A + ν.re) + r))),
      fun s hs => ?_⟩
  have hre₁ : (s + ν).re = A + ν.re := by simp [hs]
  have hre₂ : (1 - s + (-ν + (r : ℂ))).re = 1 - (A + ν.re) + r := by simp [hs]; ring
  have hpt₁ : s + ν = ((A + ν.re : ℝ) : ℂ) + ((s.im + ν.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hs]
  have hpt₂ : 1 - s + (-ν + (r : ℂ)) = ((1 - (A + ν.re) + r : ℝ) : ℂ) +
      ((-(s.im + ν.im) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hs] <;> ring
  rw [norm_Gammaℂ, norm_Gammaℂ, hre₁, hre₂, hpt₁, hpt₂, norm_Gamma_neg_im]
  calc 2 * (2 * π) ^ (-(A + ν.re)) * ‖Gamma (((A + ν.re : ℝ) : ℂ) + ((s.im + ν.im : ℝ) : ℂ) * I)‖
      ≤ 2 * (2 * π) ^ (-(A + ν.re)) *
          (K₀ * ‖Gamma (((1 - (A + ν.re) + r : ℝ) : ℂ) + ((s.im + ν.im : ℝ) : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left (hK₀ _) (by positivity)
    _ = 2 * (2 * π) ^ (-(A + ν.re)) * K₀ / (2 * (2 * π) ^ (-(1 - (A + ν.re) + r))) *
          (2 * (2 * π) ^ (-(1 - (A + ν.re) + r)) *
            ‖Gamma (((1 - (A + ν.re) + r : ℝ) : ℂ) + ((s.im + ν.im : ℝ) : ℂ) * I)‖) := by
        field_simp

private theorem exists_norm_prodR_le_paired {R R' : Multiset ℂ} (hrel : Multiset.Rel Paired R R')
    {A : ℝ}
    (hoff : ∀ μ ∈ R, ∀ j : ℕ, A + μ.re + 2 * j ≠ 0) (hfar : ∀ μ ∈ R, A + μ.re ≤ -1) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = A →
      ‖(R.map fun μ => Gammaℝ (s + μ)).prod‖ ≤ K *
          ‖(R'.map fun μ' => Gammaℝ (1 - s + μ')).prod‖ := by
  induction hrel with
  | zero => exact ⟨1, fun s _ => by simp⟩
  | @cons μ μ' R R' hp _ ih =>
    obtain ⟨K₁, h₁⟩ := exists_norm_Gammaℝ_le_paired hp (hoff μ (Multiset.mem_cons_self μ R))
      (hfar μ (Multiset.mem_cons_self μ R))
    obtain ⟨K₂, h₂⟩ := ih (fun μ₁ hμ₁ => hoff μ₁ (Multiset.mem_cons_of_mem hμ₁))
      fun μ₁ hμ₁ => hfar μ₁ (Multiset.mem_cons_of_mem hμ₁)
    refine ⟨max K₁ 0 * max K₂ 0, fun s hs => ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have e₁ : ‖Gammaℝ (s + μ)‖ ≤ max K₁ 0 * ‖Gammaℝ (1 - s + μ')‖ :=
      (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have e₂ := (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₂ 0) (norm_nonneg _))
    calc ‖Gammaℝ (s + μ)‖ * ‖(R.map fun μ => Gammaℝ (s + μ)).prod‖
        ≤ (max K₁ 0 * ‖Gammaℝ (1 - s + μ')‖) *
            (max K₂ 0 * ‖(R'.map fun μ' => Gammaℝ (1 - s + μ')).prod‖) :=
          mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = max K₁ 0 * max K₂ 0 *
            (‖Gammaℝ (1 - s + μ')‖ * ‖(R'.map fun μ' => Gammaℝ (1 - s + μ')).prod‖) := by ring

private theorem exists_norm_prodC_le_paired {C C' : Multiset ℂ} (hrel : Multiset.Rel Paired C C')
    {A : ℝ}
    (hoff : ∀ ν ∈ C, ∀ j : ℕ, A + ν.re + j ≠ 0) (hfar : ∀ ν ∈ C, A + ν.re ≤ -1) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = A →
      ‖(C.map fun ν => Gammaℂ (s + ν)).prod‖ ≤ K *
          ‖(C'.map fun ν' => Gammaℂ (1 - s + ν')).prod‖ := by
  induction hrel with
  | zero => exact ⟨1, fun s _ => by simp⟩
  | @cons ν ν' C C' hp _ ih =>
    obtain ⟨K₁, h₁⟩ := exists_norm_Gammaℂ_le_paired hp (hoff ν (Multiset.mem_cons_self ν C))
      (hfar ν (Multiset.mem_cons_self ν C))
    obtain ⟨K₂, h₂⟩ := ih (fun ν₁ hν₁ => hoff ν₁ (Multiset.mem_cons_of_mem hν₁))
      fun ν₁ hν₁ => hfar ν₁ (Multiset.mem_cons_of_mem hν₁)
    refine ⟨max K₁ 0 * max K₂ 0, fun s hs => ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have e₁ : ‖Gammaℂ (s + ν)‖ ≤ max K₁ 0 * ‖Gammaℂ (1 - s + ν')‖ :=
      (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have e₂ := (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₂ 0) (norm_nonneg _))
    calc ‖Gammaℂ (s + ν)‖ * ‖(C.map fun ν => Gammaℂ (s + ν)).prod‖
        ≤ (max K₁ 0 * ‖Gammaℂ (1 - s + ν')‖) *
            (max K₂ 0 * ‖(C'.map fun ν' => Gammaℂ (1 - s + ν')).prod‖) :=
          mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
      _ = max K₁ 0 * max K₂ 0 *
            (‖Gammaℂ (1 - s + ν')‖ * ‖(C'.map fun ν' => Gammaℂ (1 - s + ν')).prod‖) := by ring

private theorem exists_norm_gammaFactor_le_dual {R C R' C' : Multiset ℂ}
    (hR : Multiset.Rel Paired R R')
    (hC : Multiset.Rel Paired C C') {A : ℝ} (hA : OffPoleAbscissae R C A) (hfar : FarLeft R C A) :
    ∃ K : ℝ, ∀ s : ℂ, s.re = A → ‖gammaFactor R C s‖ ≤ K * ‖gammaFactor R' C' (1 - s)‖ := by
  obtain ⟨K₁, h₁⟩ := exists_norm_prodR_le_paired hR hA.1 hfar.1
  obtain ⟨K₂, h₂⟩ := exists_norm_prodC_le_paired hC hA.2 hfar.2
  refine ⟨max K₁ 0 * max K₂ 0, fun s hs => ?_⟩
  unfold gammaFactor
  rw [norm_mul, norm_mul]
  have e₁ := (h₁ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₁ 0) (norm_nonneg _))
  have e₂ := (h₂ s hs).trans (mul_le_mul_of_nonneg_right (le_max_left K₂ 0) (norm_nonneg _))
  calc _ ≤ (max K₁ 0 * ‖(R'.map fun μ' => Gammaℝ (1 - s + μ')).prod‖) *
        (max K₂ 0 * ‖(C'.map fun ν' => Gammaℂ (1 - s + ν')).prod‖) :=
        mul_le_mul e₁ e₂ (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ArchWhittakerGrowth.LShift

end
end SpanLShift

section SpanCalculus
set_option autoImplicit false

noncomputable section

namespace ArchWhittakerGrowth

variable {𝕜 : Type} [RCLike 𝕜]

private def invertibleCoords (𝕜 : Type) [RCLike 𝕜] : Set (Fin 2 → Fin 2 → 𝕜) :=
    {A | (Matrix.of A).det ≠ 0}

private theorem isOpen_invertibleCoords : IsOpen (invertibleCoords 𝕜) := by
  have hdet : Continuous fun p : Fin 2 → Fin 2 → 𝕜 => (Matrix.of p).det := by
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  exact isOpen_ne_fun hdet continuous_const

private theorem uniqueDiffOn_invertibleCoords : UniqueDiffOn ℝ (invertibleCoords 𝕜) :=
  isOpen_invertibleCoords.uniqueDiffOn

variable (𝕜) in
private def mulCoordsₗ : (Fin 2 → Fin 2 → 𝕜) →ₗ[ℝ] (Fin 2 → Fin 2 → 𝕜) →ₗ[ℝ] (Fin 2 → Fin 2 → 𝕜) :=
  LinearMap.mk₂ ℝ (fun a b => Matrix.of.symm (Matrix.of a * Matrix.of b))
    (fun a a' b => by ext i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib])
    (fun c a b => by ext i j; simp [Matrix.mul_apply])
    (fun a b b' => by ext i j; simp [Matrix.mul_apply, mul_add, Finset.sum_add_distrib])
    (fun c a b => by ext i j; simp [Matrix.mul_apply])

variable (𝕜) in
private def mulCoords : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap (mulCoordsₗ 𝕜 a)
      map_add' := fun a a' => by ext b : 1; simp
      map_smul' := fun r a => by ext b : 1; simp }

@[local simp] private theorem mulCoords_apply (a b : Fin 2 → Fin 2 → 𝕜) :
    mulCoords 𝕜 a b = Matrix.of.symm (Matrix.of a * Matrix.of b) := by
  simp [mulCoords, mulCoordsₗ]

private def rightDeriv (X : Matrix (Fin 2) (Fin 2) 𝕜) (G : (Fin 2 → Fin 2 → 𝕜) → ℂ)
    (q : Fin 2 → Fin 2 → 𝕜) : ℂ :=
  fderivWithin ℝ G (invertibleCoords 𝕜) q (Matrix.of.symm (Matrix.of q * X))

private theorem rightDeriv_eq (X : Matrix (Fin 2) (Fin 2) 𝕜) (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) :
    rightDeriv X G = fun q => fderivWithin ℝ G (invertibleCoords 𝕜) q
        ((mulCoords 𝕜).flip (Matrix.of.symm X) q) := by
  funext q
  simp [rightDeriv, -Matrix.symm_of]

private theorem contDiffOn_rightDeriv (X : Matrix (Fin 2) (Fin 2) 𝕜) {F : (Fin 2 → Fin 2 → 𝕜) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rightDeriv X F) (invertibleCoords 𝕜) := by
  rw [rightDeriv_eq]
  exact ((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_invertibleCoords).1 hF).2.clm_apply
    ((mulCoords 𝕜).flip (Matrix.of.symm X)).contDiff.contDiffOn

private def _root_.ArchWhittakerGrowth.diagOneMulCoords (t : 𝕜)
    (k : Matrix (Fin 2) (Fin 2) 𝕜) : Fin 2 → Fin 2 → 𝕜 :=
  Matrix.of.symm (!![t, 0; 0, 1] * k)

private theorem det_ne_zero_of_mem_unitaryGroup {k : Matrix (Fin 2) (Fin 2) 𝕜}
    (hk : k ∈ Matrix.unitaryGroup (Fin 2) 𝕜) :
    k.det ≠ 0 := by
  have h : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  have hdet : k.det * (star k).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one hdet

private theorem _root_.ArchWhittakerGrowth.diagOneMulCoords_mem (t : 𝕜)
    (k : Matrix (Fin 2) (Fin 2) 𝕜) (hk : k ∈ Matrix.unitaryGroup (Fin 2) 𝕜)
    (ht : t ≠ 0) : diagOneMulCoords t k ∈ invertibleCoords 𝕜 := by
  change (Matrix.of (Matrix.of.symm (!![t, 0; 0, 1] * k))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_fin_two_of]
  simpa using mul_ne_zero ht (det_ne_zero_of_mem_unitaryGroup hk)

end ArchWhittakerGrowth

end
end SpanCalculus

section SpanEnvelope
set_option autoImplicit false

noncomputable section

namespace ArchWhittakerGrowth

variable {𝕜 : Type} [RCLike 𝕜]

private def derivSum (a : ℕ) (F : (Fin 2 → Fin 2 → 𝕜) → ℂ) (p : Fin 2 → Fin 2 → 𝕜) : ℝ :=
  ∑ m ∈ Finset.range (a + 1), ‖iteratedFDerivWithin ℝ m F (invertibleCoords 𝕜) p‖

private theorem derivSum_nonneg (a : ℕ) (F : (Fin 2 → Fin 2 → 𝕜) → ℂ)
    (p : Fin 2 → Fin 2 → 𝕜) : 0 ≤ derivSum a F p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem norm_iteratedFDerivWithin_le_derivSum {m a : ℕ} (hm : m ≤ a)
    (F : (Fin 2 → Fin 2 → 𝕜) → ℂ)
    (p : Fin 2 → Fin 2 → 𝕜) : ‖iteratedFDerivWithin ℝ m F
        (invertibleCoords 𝕜) p‖ ≤ derivSum a F p := by
  unfold derivSum
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i F (invertibleCoords 𝕜) p‖)
    (fun i _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

private theorem norm_iteratedFDerivWithin_clm_le (L : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜))
    (m : ℕ)
    {p : Fin 2 → Fin 2 → 𝕜} (hp : p ∈ invertibleCoords 𝕜) :
    ‖iteratedFDerivWithin ℝ m (⇑L) (invertibleCoords 𝕜) p‖ ≤ ‖L‖ * max 1 ‖p‖ := by
  have hS : UniqueDiffOn ℝ (invertibleCoords 𝕜) := uniqueDiffOn_invertibleCoords
  have hL0 : (0 : ℝ) ≤ ‖L‖ := norm_nonneg _
  have hm1 : (1 : ℝ) ≤ max 1 ‖p‖ := le_max_left _ _
  rcases m with _ | m
  · rw [norm_iteratedFDerivWithin_zero]
    exact (L.le_opNorm p).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hL0)
  · rw [← norm_iteratedFDerivWithin_fderivWithin hS hp]
    have hcongr : Set.EqOn (fderivWithin ℝ (⇑L) (invertibleCoords 𝕜)) (fun _ => L)
        (invertibleCoords 𝕜) :=
      fun q hq => L.fderivWithin (hS q hq)
    rw [iteratedFDerivWithin_congr hcongr hp m]
    rcases m with _ | m
    · rw [norm_iteratedFDerivWithin_zero]
      exact le_mul_of_one_le_right hL0 hm1
    · simp only [iteratedFDerivWithin_const_of_ne (show m + 1 ≠ 0 by omega), Pi.zero_apply,
        norm_zero]
      positivity

private theorem norm_iteratedFDerivWithin_rightDeriv_le (X : Matrix (Fin 2) (Fin 2) 𝕜) (j : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ F : (Fin 2 → Fin 2 → 𝕜) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜) →
      ∀ p ∈ invertibleCoords 𝕜,
        ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords 𝕜) p‖
          ≤ c * max 1 ‖p‖ * derivSum (j + 1) F p := by
  obtain ⟨L, hL⟩ : ∃ L : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜), L = (mulCoords 𝕜).flip
      (Matrix.of.symm X) :=
    ⟨_, rfl⟩
  refine ⟨2 ^ j * ‖L‖, by positivity, fun F hF p hp => ?_⟩
  have hS : UniqueDiffOn ℝ (invertibleCoords 𝕜) := uniqueDiffOn_invertibleCoords
  have hF' : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ F (invertibleCoords 𝕜)) (invertibleCoords 𝕜) :=
    ((contDiffOn_infty_iff_fderivWithin hS).1 hF).2
  have hm0 : (0 : ℝ) ≤ max 1 ‖p‖ := zero_le_one.trans (le_max_left _ _)
  have hd0 : 0 ≤ derivSum (j + 1) F p := derivSum_nonneg _ _ _
  rw [rightDeriv_eq, ← hL]
  refine (norm_iteratedFDerivWithin_clm_apply hF' L.contDiff.contDiffOn hS hp (n := j)
      (mod_cast le_top)).trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ F (invertibleCoords 𝕜))
              (invertibleCoords 𝕜) p‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (⇑L) (invertibleCoords 𝕜) p‖
        ≤ (j.choose i : ℝ) * (‖L‖ * max 1 ‖p‖ * derivSum (j + 1) F p) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 : ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ F (invertibleCoords 𝕜))
        (invertibleCoords 𝕜) p‖
        ≤ derivSum (j + 1) F p := by
      rw [norm_iteratedFDerivWithin_fderivWithin hS hp]
      exact norm_iteratedFDerivWithin_le_derivSum (Nat.succ_le_succ hi') F p
    have h2 := norm_iteratedFDerivWithin_clm_le L (j - i) hp
    calc (j.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ F (invertibleCoords 𝕜))
                (invertibleCoords 𝕜) p‖ *
            ‖iteratedFDerivWithin ℝ (j - i) (⇑L) (invertibleCoords 𝕜) p‖
        ≤ (j.choose i : ℝ) * derivSum (j + 1) F p * (‖L‖ * max 1 ‖p‖) := by gcongr
      _ = (j.choose i : ℝ) * (‖L‖ * max 1 ‖p‖ * derivSum (j + 1) F p) := by ring
  calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
         (‖L‖ * max 1 ‖p‖ * derivSum (j + 1) F p) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ j * ‖L‖ * max 1 ‖p‖ * derivSum (j + 1) F p := by
        rw [← Finset.sum_mul]
        have h2 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [h2]; ring

private theorem norm_diagOneMulCoords_le (t : 𝕜) {k : Matrix (Fin 2) (Fin 2) 𝕜}
    (hk : k ∈ Matrix.unitaryGroup (Fin 2) 𝕜) :
    ‖diagOneMulCoords t k‖ ≤ max 1 ‖t‖ := by
  have hentry : ∀ i j, ‖k i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hk i j
  have hm0 : (0 : ℝ) ≤ max 1 ‖t‖ := zero_le_one.trans (le_max_left _ _)
  have h0 : ∀ j, diagOneMulCoords t k 0 j = t * k 0 j := by
    intro j
    simp only [diagOneMulCoords, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have h1 : ∀ j, diagOneMulCoords t k 1 j = k 1 j := by
    intro j
    simp only [diagOneMulCoords, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have key : ∀ i j, ‖diagOneMulCoords t k i j‖ ≤ max 1 ‖t‖ := by
    refine Fin.forall_fin_two.2 ⟨fun j => ?_, fun j => ?_⟩
    · rw [h0, norm_mul]
      calc ‖t‖ * ‖k 0 j‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hentry 0 j) (norm_nonneg _)
        _ = ‖t‖ := mul_one _
        _ ≤ max 1 ‖t‖ := le_max_right _ _
    · rw [h1]
      exact (hentry 1 j).trans (le_max_left _ _)
  rw [pi_norm_le_iff_of_nonneg hm0]
  intro i
  rw [pi_norm_le_iff_of_nonneg hm0]
  exact key i

private theorem decay_top_rightDeriv (X : Matrix (Fin 2) (Fin 2) 𝕜) (j : ℕ)
    {F : (Fin 2 → Fin 2 → 𝕜) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜))
    (hdec : ∀ m ≤ j + 1, ∀ N : ℕ, ∃ C : ℝ, ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜),
      k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → 1 ≤ ‖t‖ →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords 𝕜) (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^
            (-(N : ℝ)))
    (N : ℕ) :
    ∃ C : ℝ, ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜), k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → 1 ≤ ‖t‖ →
      ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords 𝕜) (diagOneMulCoords t k)‖
        ≤ C * ‖t‖ ^ (-(N : ℝ)) := by
  obtain ⟨c, hc0, hc⟩ := norm_iteratedFDerivWithin_rightDeriv_le X j
  have hdec' : ∀ m, m ≤ j + 1 → ∃ C : ℝ, ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜),
      k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → 1 ≤ ‖t‖ →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords 𝕜) (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^
            (-((N + 1 : ℕ) : ℝ)) :=
    fun m hm => hdec m hm (N + 1)
  choose! Cm hCm using hdec'
  refine ⟨c * ∑ m ∈ Finset.range (j + 1 + 1), Cm m, fun t k hk ht => ?_⟩
  have ht0 : 0 < ‖t‖ := one_pos.trans_le ht
  have htne : t ≠ 0 := norm_pos_iff.1 ht0
  have hp : diagOneMulCoords t k ∈ invertibleCoords 𝕜 := diagOneMulCoords_mem t k hk htne
  have hmax : max 1 ‖diagOneMulCoords t k‖ ≤ ‖t‖ :=
    max_le ht ((norm_diagOneMulCoords_le t hk).trans (le_of_eq (max_eq_right ht)))
  have hd0 : 0 ≤ derivSum (j + 1) F (diagOneMulCoords t k) := derivSum_nonneg _ _ _
  have hsum : derivSum (j + 1) F (diagOneMulCoords t k)
      ≤ (∑ m ∈ Finset.range (j + 1 + 1), Cm m) * ‖t‖ ^ (-((N + 1 : ℕ) : ℝ)) := by
    unfold derivSum
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    exact hCm m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) t k hk ht
  have hpow : ‖t‖ * ‖t‖ ^ (-((N + 1 : ℕ) : ℝ)) = ‖t‖ ^ (-(N : ℝ)) := by
    rw [Nat.cast_succ, neg_add, Real.rpow_add ht0, Real.rpow_neg_one, mul_comm, mul_assoc,
      inv_mul_cancel₀ ht0.ne', mul_one]
  calc ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords 𝕜) (diagOneMulCoords t k)‖
      ≤ c * max 1 ‖diagOneMulCoords t k‖ * derivSum (j + 1) F (diagOneMulCoords t k) := hc F hF _ hp
    _ ≤ c * ‖t‖ * ((∑ m ∈ Finset.range (j + 1 + 1), Cm m) * ‖t‖ ^ (-((N + 1 : ℕ) : ℝ))) := by gcongr
    _ = c * (∑ m ∈ Finset.range (j + 1 + 1), Cm m) * (‖t‖ * ‖t‖ ^ (-((N + 1 : ℕ) : ℝ))) := by ring
    _ = c * (∑ m ∈ Finset.range (j + 1 + 1), Cm m) * ‖t‖ ^ (-(N : ℝ)) := by rw [hpow]

private theorem decay_zero_rightDeriv (X : Matrix (Fin 2) (Fin 2) 𝕜) (j : ℕ)
    {F : (Fin 2 → Fin 2 → 𝕜) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜))
    (hdec : ∀ m ≤ j + 1, ∃ C σ : ℝ, ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜),
      k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → t ≠ 0 → ‖t‖ ≤ 1 →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords 𝕜) (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^ (-σ)) :
    ∃ C σ : ℝ, ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜), k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → t ≠ 0 →
        ‖t‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords 𝕜)
          (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^ (-σ) := by
  obtain ⟨c, hc0, hc⟩ := norm_iteratedFDerivWithin_rightDeriv_le X j
  choose! Cm σm hCm using hdec
  refine ⟨c * ∑ m ∈ Finset.range (j + 1 + 1), max 0 (Cm m), ∑ m ∈ Finset.range (j + 1 + 1), |σm m|,
    fun t k hk ht ht1 => ?_⟩
  have ht0 : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hp : diagOneMulCoords t k ∈ invertibleCoords 𝕜 := diagOneMulCoords_mem t k hk ht
  have hmax : max 1 ‖diagOneMulCoords t k‖ ≤ 1 :=
    max_le le_rfl ((norm_diagOneMulCoords_le t hk).trans (max_le le_rfl ht1))
  have hσm : ∀ m ∈ Finset.range (j + 1 + 1), σm m ≤ ∑ m ∈ Finset.range
      (j + 1 + 1), |σm m| := fun m hm =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun m => |σm m|) (fun i _ => abs_nonneg _) hm)
  have hd0 : 0 ≤ derivSum (j + 1) F (diagOneMulCoords t k) := derivSum_nonneg _ _ _
  have hsum : derivSum (j + 1) F (diagOneMulCoords t k)
      ≤ (∑ m ∈ Finset.range (j + 1 + 1), max 0 (Cm m)) * ‖t‖ ^
          (-(∑ m ∈ Finset.range (j + 1 + 1), |σm m|)) := by
    unfold derivSum
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm' : m ≤ j + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    calc ‖iteratedFDerivWithin ℝ m F (invertibleCoords 𝕜) (diagOneMulCoords t k)‖
        ≤ Cm m * ‖t‖ ^ (-σm m) := hCm m hm' t k hk ht ht1
      _ ≤ max 0 (Cm m) * ‖t‖ ^ (-σm m) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht0.le _)
      _ ≤ max 0 (Cm m) * ‖t‖ ^ (-(∑ m ∈ Finset.range (j + 1 + 1), |σm m|)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht0 ht1
              (neg_le_neg (hσm m hm)))
            (le_max_left _ _)
  calc ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords 𝕜) (diagOneMulCoords t k)‖
      ≤ c * max 1 ‖diagOneMulCoords t k‖ * derivSum (j + 1) F (diagOneMulCoords t k) := hc F hF _ hp
    _ ≤ c * 1 * ((∑ m ∈ Finset.range (j + 1 + 1), max 0 (Cm m)) *
          ‖t‖ ^ (-(∑ m ∈ Finset.range (j + 1 + 1), |σm m|))) := by gcongr
    _ = c * (∑ m ∈ Finset.range (j + 1 + 1), max 0 (Cm m)) *
          ‖t‖ ^ (-(∑ m ∈ Finset.range (j + 1 + 1), |σm m|)) := by ring

private theorem decay_top_rightDeriv_real (X : Matrix (Fin 2) (Fin 2) ℝ) (j : ℕ)
    {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords ℝ))
    (hdec : ∀ m ≤ j + 1, ∀ N : ℕ, ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
      k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → 1 ≤ |y| →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords ℝ) (diagOneMulCoords y k)‖ ≤ C * |y| ^
            (-(N : ℝ)))
    (N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
        1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords ℝ) (diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-(N : ℝ)) := by
  have hdec' : ∀ m ≤ j + 1, ∀ N : ℕ, ∃ C : ℝ, ∀ (t : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
      k ∈ Matrix.unitaryGroup (Fin 2) ℝ → 1 ≤ ‖t‖ →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords ℝ) (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^
            (-(N : ℝ)) :=
    fun m hm N => (hdec m hm N).imp fun C hC t k hk ht => by
      simpa [Real.norm_eq_abs] using hC t k hk (by simpa [Real.norm_eq_abs] using ht)
  obtain ⟨C, hC⟩ := decay_top_rightDeriv X j hF hdec' N
  exact ⟨C, fun y k hk hy => by
    simpa [Real.norm_eq_abs] using hC y k hk (by simpa [Real.norm_eq_abs] using hy)⟩

private theorem decay_zero_rightDeriv_real (X : Matrix (Fin 2) (Fin 2) ℝ) (j : ℕ)
    {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords ℝ))
    (hdec : ∀ m ≤ j + 1, ∃ C σ : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
      k ∈ Matrix.orthogonalGroup (Fin 2) ℝ → y ≠ 0 → |y| ≤ 1 →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords ℝ) (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ)) :
    ∃ C σ : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
        y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (rightDeriv X F) (invertibleCoords ℝ)
          (diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ) := by
  have hdec' : ∀ m ≤ j + 1, ∃ C σ : ℝ, ∀ (t : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ),
      k ∈ Matrix.unitaryGroup (Fin 2) ℝ → t ≠ 0 → ‖t‖ ≤ 1 →
        ‖iteratedFDerivWithin ℝ m F (invertibleCoords ℝ) (diagOneMulCoords t k)‖ ≤ C * ‖t‖ ^ (-σ) :=
    fun m hm => by
      obtain ⟨C, σ, hC⟩ := hdec m hm
      exact ⟨C, σ, fun t k hk ht ht1 => by
        simpa [Real.norm_eq_abs] using hC t k hk ht (by simpa [Real.norm_eq_abs] using ht1)⟩
  obtain ⟨C, σ, hC⟩ := decay_zero_rightDeriv X j hF hdec'
  exact ⟨C, σ, fun y k hk hy hy1 => by
    simpa [Real.norm_eq_abs] using hC y k hk hy (by simpa [Real.norm_eq_abs] using hy1)⟩

end ArchWhittakerGrowth

end
end SpanEnvelope

section SpanGroupR
set_option autoImplicit false

noncomputable section

open Complex
open scoped Matrix
open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth

namespace GroupR

private theorem isK_iff {k : Matrix (Fin 2) (Fin 2) ℝ} : ArchR.IsK k ↔ k * kᵀ = 1 := by
  unfold ArchR.IsK
  exact Matrix.mem_orthogonalGroup_iff (n := Fin 2) (R := ℝ)

private theorem isK_mul_transpose {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k) : k * kᵀ = 1 := isK_iff.1 hk

private theorem isK_det_sq {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : k.det ^ 2 = 1 := by
  have h := congrArg Matrix.det (isK_mul_transpose hk)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rw [sq]
  exact h

private theorem isK_abs_det {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : |k.det| = 1 := by
  have h1 : |k.det| ^ 2 = 1 := by rw [sq_abs]; exact isK_det_sq hk
  have h0 : 0 ≤ |k.det| := abs_nonneg _
  nlinarith [h1, h0, sq_nonneg (|k.det| - 1), sq_nonneg (|k.det| + 1)]

private theorem isK_det_ne_zero {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : k.det ≠ 0 := by
  intro h
  have := isK_abs_det hk
  rw [h, abs_zero] at this
  exact zero_ne_one this

private theorem isK_row_sq {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (i : Fin 2) :
    k i 0 ^ 2 + k i 1 ^ 2 = 1 := by
  have h := congrFun (congrFun (isK_mul_transpose hk) i) i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  simpa [sq] using h

private theorem isK_abs_entry_le_one {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k)
    (i j : Fin 2) :
    |k i j| ≤ 1 := by
  have h := isK_row_sq hk i
  revert j
  rw [Fin.forall_fin_two]
  exact ⟨(sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (k i 1)]),
    (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (k i 0)])⟩

private theorem det_diagOne (y : ℝ) : (ArchR.diagOne y).det = y := by
  simp [ArchR.diagOne, Matrix.det_fin_two_of]

private theorem det_unip (x : ℝ) : (ArchR.unip x).det = 1 := by
  simp [ArchR.unip, Matrix.det_fin_two_of]

private theorem det_weyl : (ArchR.weyl).det = 1 := by
  simp [ArchR.weyl, Matrix.det_fin_two_of]

private theorem diagOne_mul_diagOne (y t : ℝ) : ArchR.diagOne y * ArchR.diagOne t = ArchR.diagOne
    (y * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_unip (y x : ℝ) : ArchR.diagOne y * ArchR.unip x = ArchR.unip
    (y * x) * ArchR.diagOne y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, ArchR.unip, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem abs_diagOne_mul_le {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (y : ℝ)
    (i j : Fin 2) :
    |(ArchR.diagOne y * k) i j| ≤ max 1 |y| := by
  have hent := isK_abs_entry_le_one hk
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · have : (ArchR.diagOne y * k) 0 j = y * k 0 j := by
      simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this, abs_mul]
    calc |y| * |k 0 j| ≤ |y| * 1 := by gcongr; exact hent 0 j
      _ ≤ max 1 |y| := by rw [mul_one]; exact le_max_right _ _
  · have : (ArchR.diagOne y * k) 1 j = k 1 j := by
      simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this]
    exact (hent 1 j).trans (le_max_left _ _)

private def rowSq (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g 1 0 ^ 2 + g 1 1 ^ 2

private def rowNorm (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt (rowSq g)

private def iwX (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (g 0 0 * g 1 0 + g 0 1 * g 1 1) / rowSq g

private def iwT (g : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := g.det / rowSq g

private def rot (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2)
    (Fin 2) ℝ := !![g 1 1, -(g 1 0); g 1 0, g 1 1]

private def kPart (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (rowNorm g)⁻¹ • rot g

private theorem rowSq_nonneg (g : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ rowSq g := by
  unfold rowSq; positivity

private theorem rowSq_pos {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : 0 < rowSq g := by
  by_contra h
  have h0 : rowSq g = 0 := le_antisymm (not_lt.1 h) (rowSq_nonneg g)
  unfold rowSq at h0
  have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
  apply hg
  rw [Matrix.det_fin_two, h10, h11]
  ring

private theorem rowNorm_pos {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : 0 < rowNorm g :=
  Real.sqrt_pos.2 (rowSq_pos hg)

private theorem rowNorm_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : rowNorm g ^ 2 = rowSq g :=
  Real.sq_sqrt (rowSq_nonneg g)

private theorem iwasawa {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    g = ArchR.unip (iwX g) * (ArchR.diagOne (iwT g) * rot g) := by
  have hq : rowSq g ≠ 0 := (rowSq_pos hg).ne'
  have h00 : g 0 0 = iwT g * g 1 1 + iwX g * g 1 0 := by
    unfold iwT iwX
    rw [Matrix.det_fin_two]
    field_simp
    unfold rowSq
    ring
  have h01 : g 0 1 = iwT g * (-(g 1 0)) + iwX g * g 1 1 := by
    unfold iwT iwX
    rw [Matrix.det_fin_two]
    field_simp
    unfold rowSq
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [ArchR.unip, ArchR.diagOne, rot, Matrix.mul_apply, Fin.sum_univ_two] using h00
  · simpa [ArchR.unip, ArchR.diagOne, rot, Matrix.mul_apply, Fin.sum_univ_two] using h01
  · simp [ArchR.unip, ArchR.diagOne, rot, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [ArchR.unip, ArchR.diagOne, rot, Matrix.mul_apply, Fin.sum_univ_two]

private theorem rot_eq_smul_kPart {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0) : rot g = rowNorm g • kPart g := by
  unfold kPart
  rw [smul_smul, mul_inv_cancel₀ (rowNorm_pos hg).ne', one_smul]

private theorem iwasawa' {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    g = ArchR.unip (iwX g) * (rowNorm g • (ArchR.diagOne (iwT g) * kPart g)) := by
  rw [← Matrix.mul_smul, ← rot_eq_smul_kPart hg]
  exact iwasawa hg

private theorem diagOne_mul_iwasawa {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (y : ℝ) :
    ArchR.diagOne y * g =
      ArchR.unip (y * iwX g) * (rowNorm g • (ArchR.diagOne (y * iwT g) * kPart g)) := by
  conv_lhs => rw [iwasawa' hg]
  rw [← Matrix.mul_assoc, diagOne_mul_unip, Matrix.mul_assoc, Matrix.mul_smul, ← Matrix.mul_assoc,
    diagOne_mul_diagOne]

private theorem rot_mul_transpose (g : Matrix (Fin 2) (Fin 2) ℝ) :
    rot g * (rot g)ᵀ = rowSq g • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, rowSq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem isK_kPart {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) : ArchR.IsK
    (kPart g) := by
  rw [isK_iff]
  unfold kPart
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, rot_mul_transpose,
      smul_smul]
  have hb : rowNorm g ≠ 0 := (rowNorm_pos hg).ne'
  have : (rowNorm g)⁻¹ * (rowNorm g)⁻¹ * rowSq g = 1 := by
    rw [← rowNorm_sq g]
    field_simp
  rw [this, one_smul]

private structure LeftLaws (P : RealArchParam) (G : Matrix (Fin 2) (Fin 2) ℝ → ℂ) : Prop where
  unip : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), G (ArchR.unip x * g) = ArchR.psi x * G g
  central : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), z ≠ 0 →
    G (z • g) = ArchR.centralChar P z * ((|z| : ℝ) : ℂ) * G g

private theorem leftLaws_datum {P : RealArchParam} (d : ArchDatumR P) : LeftLaws P d.W :=
  ⟨d.unip_law, d.central_law⟩

private theorem LeftLaws.reduce {P : RealArchParam} {G : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hG : LeftLaws P G) (x : ℝ)
    {b : ℝ} (hb : b ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    G (ArchR.unip x * (b • M)) = ArchR.psi x * (ArchR.centralChar P b * ((|b| : ℝ) : ℂ)) * G M := by
  rw [hG.unip, hG.central b M hb]
  ring

private theorem LeftLaws.diagOne_mul {P : RealArchParam} {G : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hG : LeftLaws P G)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (y : ℝ) :
    G (ArchR.diagOne y * g) = ArchR.psi (y * iwX g) *
      (ArchR.centralChar P (rowNorm g) * ((|rowNorm g| : ℝ) : ℂ)) * G
          (ArchR.diagOne (y * iwT g) * kPart g) := by
  rw [diagOne_mul_iwasawa hg y, hG.reduce _ (rowNorm_pos hg).ne']

private theorem norm_psi (x : ℝ) : ‖ArchR.psi x‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold ArchR.psi
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_centralChar (P : RealArchParam) {z : ℝ} (hz : z ≠ 0) :
    ‖ArchR.centralChar P z‖ = |z| ^ P.centralExponent.re := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hz)]
  have h1 : ‖(if P.centralSign = 0 then (1 : ℂ) else ((SignType.sign z : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · simp
    · rcases hz.lt_or_gt with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]
  rw [h1, mul_one]

private theorem norm_reduce_factor (P : RealArchParam) (x : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ‖ArchR.psi x * (ArchR.centralChar P b * ((|b| : ℝ) : ℂ))‖ = |b| ^ P.centralExponent.re
        * |b| := by
  rw [norm_mul, norm_psi, one_mul, norm_mul, norm_centralChar P hb, Complex.norm_real,
      Real.norm_eq_abs, abs_abs]

end GroupR

end ArchWhittakerGrowth

end
end SpanGroupR

section SpanDerivR
set_option autoImplicit false

noncomputable section

open Complex
open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth

namespace DerivR

open GroupR

private theorem glSet_eq : ArchR.glSet = invertibleCoords ℝ := rfl

private theorem mem_glSet_iff {p : Fin 2 → Fin 2 → ℝ} : p ∈ ArchR.glSet ↔
    (Matrix.of p).det ≠ 0 := Iff.rfl

private theorem of_symm_mem_glSet_iff {g : Matrix (Fin 2) (Fin 2) ℝ} : Matrix.of.symm g ∈
    ArchR.glSet ↔ g.det ≠ 0 :=
  Iff.rfl

private theorem isOpen_glSet : IsOpen ArchR.glSet := isOpen_invertibleCoords

private theorem asPi_apply (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (p : Fin 2 → Fin 2 → ℝ) :
    ArchR.asPi W p = W (Matrix.of p) := rfl

private theorem asPi_of_symm (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ArchR.asPi W (Matrix.of.symm g) = W g := rfl

private def _root_.ArchWhittakerGrowth.DerivR.derivW (X : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  if g.det ≠ 0 then rightDeriv X (ArchR.asPi W) (Matrix.of.symm g) else 0

private theorem derivW_of_det_ne_zero (X : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    derivW X W g = rightDeriv X (ArchR.asPi W) (Matrix.of.symm g) := ite_eq_left hg

private theorem derivW_of_det_eq_zero (X : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 0) : derivW X W g = 0 := by
  simp [derivW, hg]

private theorem asPi_derivW_eqOn (X : Matrix (Fin 2) (Fin 2) ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    Set.EqOn (ArchR.asPi (derivW X W)) (rightDeriv X (ArchR.asPi W)) ArchR.glSet := by
  intro p hp
  rw [asPi_apply, derivW_of_det_ne_zero X W (mem_glSet_iff.1 hp)]
  rfl

private theorem rightDeriv_eq_fderiv (X : Matrix (Fin 2) (Fin 2) ℝ) (F : (Fin 2 → Fin 2 → ℝ) → ℂ)
    {p : Fin 2 → Fin 2 → ℝ} (hp : p ∈ ArchR.glSet) :
    rightDeriv X F p = fderiv ℝ F p (Matrix.of.symm (Matrix.of p * X)) := by
  unfold rightDeriv
  rw [← glSet_eq, fderivWithin_of_isOpen isOpen_glSet hp]

private theorem derivW_eq_fderiv (X : Matrix (Fin 2) (Fin 2) ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    derivW X W g = fderiv ℝ (ArchR.asPi W) (Matrix.of.symm g) (Matrix.of.symm (g * X)) := by
  rw [derivW_of_det_ne_zero X W hg, rightDeriv_eq_fderiv X _ (of_symm_mem_glSet_iff.2 hg)]
  rfl

private theorem differentiableAt_of_smooth {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F ArchR.glSet)
    {p : Fin 2 → Fin 2 → ℝ} (hp : p ∈ ArchR.glSet) : DifferentiableAt ℝ F p :=
  (hF.differentiableOn (by simp) p hp).differentiableAt (isOpen_glSet.mem_nhds hp)

private theorem fderiv_transport {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    {L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ)}
    {c : ℂ} (h : ∀ q, F (L q) = c * F q) {p : Fin 2 → Fin 2 → ℝ} (hF : DifferentiableAt ℝ F p)
    (hFL : DifferentiableAt ℝ F (L p)) (v : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ F (L p) (L v) = c * fderiv ℝ F p v := by
  have hfun : F ∘ L = c • F := by
    funext q
    simp [Function.comp, h q, smul_eq_mul]
  have hcomp : fderiv ℝ (F ∘ L) p = (fderiv ℝ F (L p)).comp L := by
    rw [fderiv_comp p hFL L.differentiableAt, ContinuousLinearMap.fderiv]
  have happ := congrArg (fun φ : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ => φ v) hcomp
  simp only [ContinuousLinearMap.comp_apply] at happ
  rw [← happ, hfun, fderiv_const_smul hF c, smul_apply, smul_eq_mul]

private def leftMul (n : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ]
    (Fin 2 → Fin 2 → ℝ) :=
  mulCoords ℝ (Matrix.of.symm n)

@[local simp] private theorem leftMul_apply (n : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Fin 2 → Fin 2 → ℝ) :
    leftMul n q = Matrix.of.symm (n * Matrix.of q) := by
  simp [leftMul, mulCoords_apply, -Matrix.symm_of]

private theorem leftMul_of_symm (n g : Matrix (Fin 2) (Fin 2) ℝ) : leftMul n
    (Matrix.of.symm g) = Matrix.of.symm (n * g) := by
  simp [-Matrix.symm_of]

private theorem derivW_unip_law {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hW : ∀ (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ),
      W (ArchR.unip x * g) = ArchR.psi x * W g) (hWs : ContDiffOn ℝ (⊤ : ℕ∞)
          (ArchR.asPi W) ArchR.glSet)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    derivW X W (ArchR.unip x * g) = ArchR.psi x * derivW X W g := by
  by_cases hg : g.det ≠ 0
  · have hng : (ArchR.unip x * g).det ≠ 0 := by rwa [Matrix.det_mul, det_unip, one_mul]
    have hp : Matrix.of.symm g ∈ ArchR.glSet := of_symm_mem_glSet_iff.2 hg
    have hnp : Matrix.of.symm (ArchR.unip x * g) ∈ ArchR.glSet := of_symm_mem_glSet_iff.2 hng
    have hlaw : ∀ q, ArchR.asPi W (leftMul (ArchR.unip x) q) = ArchR.psi x * ArchR.asPi W q := by
      intro q
      rw [leftMul_apply, asPi_of_symm, asPi_apply, hW]
    have hpt : leftMul (ArchR.unip x) (Matrix.of.symm g) = Matrix.of.symm
        (ArchR.unip x * g) := leftMul_of_symm _ _
    have hvec : leftMul (ArchR.unip x) (Matrix.of.symm (g * X)) = Matrix.of.symm
        (ArchR.unip x * g * X) := by
      rw [leftMul_of_symm, Matrix.mul_assoc]
    rw [derivW_eq_fderiv X W hng, derivW_eq_fderiv X W hg, ← hpt, ← hvec]
    exact fderiv_transport hlaw (differentiableAt_of_smooth hWs hp)
      (by rw [hpt]; exact differentiableAt_of_smooth hWs hnp) _
  · rw [not_ne_iff] at hg
    have hng : (ArchR.unip x * g).det = 0 := by rw [Matrix.det_mul, det_unip, one_mul, hg]
    rw [derivW_of_det_eq_zero X W hg, derivW_of_det_eq_zero X W hng, mul_zero]

private theorem derivW_central_law {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hW : ∀ (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ), z ≠ 0 →
      W (z • g) = ArchR.centralChar P z * ((|z| : ℝ) : ℂ) * W g)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (hz : z ≠ 0) :
    derivW X W (z • g) = ArchR.centralChar P z * ((|z| : ℝ) : ℂ) * derivW X W g := by
  by_cases hg : g.det ≠ 0
  · have hzg : (z • g).det ≠ 0 := by
      rw [Matrix.det_smul, Fintype.card_fin]
      exact mul_ne_zero (pow_ne_zero _ hz) hg
    have hp : Matrix.of.symm g ∈ ArchR.glSet := of_symm_mem_glSet_iff.2 hg
    have hzp : Matrix.of.symm (z • g) ∈ ArchR.glSet := of_symm_mem_glSet_iff.2 hzg
    have hlaw : ∀ q, ArchR.asPi W (leftMul (z • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q) =
        (ArchR.centralChar P z * ((|z| : ℝ) : ℂ)) * ArchR.asPi W q := by
      intro q
      rw [leftMul_apply, Matrix.smul_mul, Matrix.one_mul, asPi_of_symm, asPi_apply, hW z _ hz]
    have hpt : leftMul (z • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.of.symm g) = Matrix.of.symm
        (z • g) := by
      rw [leftMul_of_symm, Matrix.smul_mul, Matrix.one_mul]
    have hvec : leftMul (z • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (Matrix.of.symm (g * X)) =
        Matrix.of.symm (z • g * X) := by
      rw [leftMul_of_symm, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [derivW_eq_fderiv X W hzg, derivW_eq_fderiv X W hg, ← hpt, ← hvec]
    exact fderiv_transport hlaw (differentiableAt_of_smooth hWs hp)
      (by rw [hpt]; exact differentiableAt_of_smooth hWs hzp) _
  · rw [not_ne_iff] at hg
    have hzg : (z • g).det = 0 := by rw [Matrix.det_smul, hg, mul_zero]
    rw [derivW_of_det_eq_zero X W hg, derivW_of_det_eq_zero X W hzg, mul_zero]

private theorem leftLaws_derivW {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    LeftLaws P (derivW X W) :=
  ⟨derivW_unip_law hL.unip hWs X, fun z g hz => derivW_central_law hL.central hWs X z g hz⟩

private theorem fderiv_asPi_apply_eq_derivW (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0) (v : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (ArchR.asPi W) (Matrix.of.symm g) v = derivW (g⁻¹ * Matrix.of v) W g := by
  rw [derivW_eq_fderiv _ W hg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hg),
      Matrix.one_mul]
  rfl

private def unitMat (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single i j (1 : ℝ)

private theorem hasDerivAt_asPi_line (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (M V : Matrix (Fin 2) (Fin 2) ℝ) {t : ℝ} (ht : (M + t • V).det ≠ 0) :
    HasDerivAt (fun τ : ℝ => W (M + τ • V)) (derivW ((M + t • V)⁻¹ * V) W (M + t • V)) t := by
  have hpath : HasDerivAt (fun τ : ℝ => Matrix.of.symm (M + τ • V)) (Matrix.of.symm V) t := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • Matrix.of.symm V) ((1 : ℝ) • Matrix.of.symm V) t :=
      (hasDerivAt_id t).smul_const _
    rw [one_smul] at h1
    have h2 := h1.const_add (Matrix.of.symm M)
    convert h2 using 1
    rfl
  have hp : Matrix.of.symm (M + t • V) ∈ ArchR.glSet := of_symm_mem_glSet_iff.2 ht
  have hF : HasFDerivAt (ArchR.asPi W) (fderiv ℝ (ArchR.asPi W) (Matrix.of.symm (M + t • V)))
      (Matrix.of.symm (M + t • V)) := (differentiableAt_of_smooth hWs hp).hasFDerivAt
  have hcomp := hF.comp_hasDerivAt t hpath
  rw [fderiv_asPi_apply_eq_derivW W ht] at hcomp
  exact hcomp

end DerivR

end ArchWhittakerGrowth

end
end SpanDerivR

section SpanOrbitR
set_option autoImplicit false

noncomputable section

open Complex
open scoped Matrix
open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth

namespace OrbitR

open GroupR DerivR

private theorem diagOne_eq_add_smul (y : ℝ) :
    ArchR.diagOne y = ArchR.diagOne 0 + y • unitMat 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, unitMat, Matrix.single]

private theorem diagOne_mul_eq_line (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    ArchR.diagOne y * k = ArchR.diagOne 0 * k + y • (unitMat 0 0 * k) := by
  rw [diagOne_eq_add_smul y, Matrix.add_mul, Matrix.smul_mul]

end OrbitR

end ArchWhittakerGrowth

end
end SpanOrbitR

section SpanIntegralR
set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Matrix
open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth

namespace IntegralR

open GroupR DerivR OrbitR

private def env (σ N y : ℝ) : ℝ := if |y| ≤ 1 then |y| ^ (-σ) else |y| ^ (-N)

private theorem env_of_le {σ N y : ℝ} (h : |y| ≤ 1) : env σ N y = |y| ^ (-σ) :=
  ite_eq_left h

private theorem env_of_lt {σ N y : ℝ} (h : 1 < |y|) : env σ N y = |y| ^ (-N) :=
  ite_eq_right (not_le.2 h)

private theorem env_nonneg (σ N y : ℝ) : 0 ≤ env σ N y := by
  unfold env
  split_ifs <;> exact Real.rpow_nonneg (abs_nonneg y) _

private theorem one_le_env_of_le {σ N y : ℝ} (hσ : 0 ≤ σ) (hy : y ≠ 0)
    (h : |y| ≤ 1) : 1 ≤ env σ N y := by
  rw [env_of_le h]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.2 hy) h (by linarith)

private theorem env_mono {σ σ' N N' y : ℝ} (hy : y ≠ 0) (hσ : σ ≤ σ')
    (hN : N' ≤ N) : env σ N y ≤ env σ' N' y := by
  unfold env
  split_ifs with h
  · exact Real.rpow_le_rpow_of_exponent_ge (abs_pos.2 hy) h (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le (not_le.1 h).le (by linarith)

private theorem env_rescale {σ N τ₀ : ℝ} (hσ : 0 ≤ σ) (hN : 0 ≤ N) (h0 : 0 < τ₀) (h1 : τ₀ ≤ 1)
    {t : ℝ} (ht : τ₀ ≤ |t|)
    {y : ℝ} (hy : y ≠ 0) : env σ N (y * t) ≤ τ₀ ^ (-(σ + N)) * env σ N y := by
  have htpos : 0 < |t| := lt_of_lt_of_le h0 ht
  have hypos : 0 < |y| := abs_pos.2 hy
  have habs : |y * t| = |y| * |t| := abs_mul y t
  have hc1 : 1 ≤ τ₀ ^ (-(σ + N)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith)
  have hcσ : τ₀ ^ (-σ) ≤ τ₀ ^ (-(σ + N)) := Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)
  have hcN : τ₀ ^ (-N) ≤ τ₀ ^ (-(σ + N)) := Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)
  have hsplit : τ₀ ^ (-(σ + N)) = τ₀ ^ (-σ) * τ₀ ^ (-N) := by
    rw [show -(σ + N) = -σ + -N by ring, Real.rpow_add h0]
  have henv := env_nonneg σ N y
  have htσ : |t| ^ (-σ) ≤ τ₀ ^ (-σ) := Real.rpow_le_rpow_of_nonpos h0 ht (by linarith)
  have htN : |t| ^ (-N) ≤ τ₀ ^ (-N) := Real.rpow_le_rpow_of_nonpos h0 ht (by linarith)
  by_cases hyt : |y * t| ≤ 1
  · rw [env_of_le hyt, habs, Real.mul_rpow hypos.le htpos.le]
    by_cases hyle : |y| ≤ 1
    · rw [env_of_le hyle]
      calc |y| ^ (-σ) * |t| ^ (-σ) ≤ |y| ^ (-σ) * τ₀ ^ (-(σ + N)) :=
            mul_le_mul_of_nonneg_left (htσ.trans hcσ) (Real.rpow_nonneg hypos.le _)
        _ = τ₀ ^ (-(σ + N)) * |y| ^ (-σ) := mul_comm _ _
    · have hylt : 1 < |y| := not_le.1 hyle
      rw [env_of_lt hylt]
      have hbase : τ₀ ≤ |y| * |t| := by nlinarith
      have h1' : |y| ^ (-σ) * |t| ^ (-σ) ≤ τ₀ ^ (-σ) := by
        rw [← Real.mul_rpow hypos.le htpos.le]
        exact Real.rpow_le_rpow_of_nonpos h0 hbase (by linarith)
      have hyub : |y| * τ₀ ≤ 1 := by
        rw [habs] at hyt
        nlinarith
      have h2' : 1 ≤ τ₀ ^ (-N) * |y| ^ (-N) := by
        rw [← Real.mul_rpow h0.le hypos.le, mul_comm]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) hyub (by linarith)
      calc |y| ^ (-σ) * |t| ^ (-σ) ≤ τ₀ ^ (-σ) * 1 := by rw [mul_one]; exact h1'
        _ ≤ τ₀ ^ (-σ) * (τ₀ ^ (-N) * |y| ^ (-N)) :=
            mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg h0.le _)
        _ = τ₀ ^ (-(σ + N)) * |y| ^ (-N) := by rw [hsplit, mul_assoc]
  · have hytlt : 1 < |y * t| := not_le.1 hyt
    rw [env_of_lt hytlt, habs, Real.mul_rpow hypos.le htpos.le]
    by_cases hyle : |y| ≤ 1
    · have hle1 : |y| ^ (-N) * |t| ^ (-N) ≤ 1 := by
        rw [← Real.mul_rpow hypos.le htpos.le, ← habs]
        exact Real.rpow_le_one_of_one_le_of_nonpos hytlt.le (by linarith)
      have hge1 : 1 ≤ env σ N y := one_le_env_of_le hσ hy hyle
      calc |y| ^ (-N) * |t| ^ (-N) ≤ 1 := hle1
        _ ≤ τ₀ ^ (-(σ + N)) * env σ N y := by nlinarith
    · have hylt : 1 < |y| := not_le.1 hyle
      rw [env_of_lt hylt]
      calc |y| ^ (-N) * |t| ^ (-N) ≤ |y| ^ (-N) * τ₀ ^ (-(σ + N)) :=
            mul_le_mul_of_nonneg_left (htN.trans hcN) (Real.rpow_nonneg hypos.le _)
        _ = τ₀ ^ (-(σ + N)) * |y| ^ (-N) := mul_comm _ _

private theorem env_mul_rpow_eqOn_Ioc {σ N α : ℝ} :
    EqOn (fun y : ℝ => env σ N y * |y| ^ α) (fun y => y ^ (α - σ)) (Ioc 0 1) := by
  intro y hy
  have hy0 : 0 < y := hy.1
  simp only
  rw [env_of_le (by rw [abs_of_pos hy0]; exact hy.2), abs_of_pos hy0, ← Real.rpow_add hy0]
  ring_nf

private theorem env_mul_rpow_eqOn_Ioi {σ N α : ℝ} :
    EqOn (fun y : ℝ => env σ N y * |y| ^ α) (fun y => y ^ (α - N)) (Ioi 1) := by
  intro y hy
  have hy1 : 1 < y := hy
  have hy0 : 0 < y := by linarith
  simp only
  rw [env_of_lt (by rw [abs_of_pos hy0]; exact hy1), abs_of_pos hy0, ← Real.rpow_add hy0]
  ring_nf

private theorem integrableOn_env_mul_rpow_Ioi {σ N α : ℝ} (h0 : -1 < α - σ) (h1 : α - N < -1) :
    IntegrableOn (fun y : ℝ => env σ N y * |y| ^ α) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h := (intervalIntegral.intervalIntegrable_rpow' h0 (a := 0) (b := 1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact h.congr_fun env_mul_rpow_eqOn_Ioc.symm measurableSet_Ioc
  · exact (integrableOn_Ioi_rpow_of_lt h1 zero_lt_one).congr_fun env_mul_rpow_eqOn_Ioi.symm
      measurableSet_Ioi

private theorem env_mul_rpow_even {σ N α : ℝ} (y : ℝ) : env σ N
    (-y) * |(-y)| ^ α = env σ N y * |y| ^ α := by
  simp [env, abs_neg]

private theorem integrable_env_mul_rpow {σ N α : ℝ} (h0 : -1 < α - σ) (h1 : α - N < -1) :
    Integrable (fun y : ℝ => env σ N y * |y| ^ α) := by
  have hIoi := integrableOn_env_mul_rpow_Ioi (N := N) h0 h1
  have hIio : IntegrableOn (fun y : ℝ => env σ N y * |y| ^ α) (Iio 0) := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg
        volume
    have hme : MeasurableEmbedding (Neg.neg : ℝ → ℝ) := (MeasurableEquiv.neg ℝ).measurableEmbedding
    have key := (hmp.integrableOn_comp_preimage hme (f := fun y : ℝ => env σ N y * |y| ^ α)
        (s := Ioi 0)).2 hIoi
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by
      ext y; simp
    rw [hpre] at key
    refine key.congr_fun (fun y _ => ?_) measurableSet_Iio
    simp only [Function.comp_apply]
    exact env_mul_rpow_even y
  have hunion : IntegrableOn (fun y : ℝ => env σ N y * |y| ^ α) (Iio 0 ∪ Ioi 0) := hIio.union hIoi
  have hae : (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) =ᵐ[volume] (univ : Set ℝ) := by
    have : (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) = {0}ᶜ := by
      ext y
      simp only [mem_union, mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]
      exact lt_or_lt_iff_ne
    rw [this]
    exact (ae_eq_univ.2 (by simp))
  rw [← integrableOn_univ]
  exact hunion.congr_set_ae hae.symm

private theorem env_mul_max_pow_le {σ N y : ℝ} (m : ℕ) :
    env σ N y * max 1 |y| ^ m ≤ env σ (N - m) y := by
  unfold env
  split_ifs with h
  · rw [max_eq_left h, one_pow, mul_one]
  · have hlt : 1 < |y| := not_le.1 h
    rw [max_eq_right hlt.le, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    ring_nf
    rfl

private theorem orbitEnvelope_of {F : (Fin 2 → Fin 2 → ℝ) → ℂ} {j N : ℕ} {Ct Cz σ : ℝ}
    (htop : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j F ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ Ct * |y| ^ (-(N : ℝ)))
    (hzero : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j F ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ Cz * |y| ^ (-σ))
    {y : ℝ} {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (hy : y ≠ 0) :
    ‖iteratedFDerivWithin ℝ j F ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ max Ct Cz * env σ N
        y := by
  by_cases h : |y| ≤ 1
  · rw [env_of_le h]
    exact (hzero y k hk hy h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (abs_nonneg _) _))
  · rw [env_of_lt (not_le.1 h)]
    exact (htop y k hk (not_le.1 h).le).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))

private theorem norm_diagOneMulCoords_le {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (y : ℝ) :
    ‖ArchR.diagOneMulCoords y k‖ ≤ max 1 |y| := by
  have h0 : (0 : ℝ) ≤ max 1 |y| := le_trans zero_le_one (le_max_left _ _)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_diagOne_mul_le hk y i j

private theorem diagOneMulCoords_mem {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) {y : ℝ}
    (hy : y ≠ 0) :
    ArchR.diagOneMulCoords y k ∈ ArchR.glSet := by
  change (Matrix.of (Matrix.of.symm (ArchR.diagOne y * k))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_mul, det_diagOne]
  exact mul_ne_zero hy (isK_det_ne_zero hk)

private theorem norm_orbit_eq (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (y : ℝ)
    (k : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖W (ArchR.diagOne y * k)‖ =
      ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ := by
  rw [norm_iteratedFDerivWithin_zero]
  rfl

private theorem norm_derivW_orbit_le (Y : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) {y : ℝ} (hy : y ≠ 0) :
    ‖derivW Y W (ArchR.diagOne y * k)‖ ≤
      ‖iteratedFDerivWithin ℝ 1 (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ *
        (‖mulCoords ℝ‖ * max 1 |y| * ‖(Matrix.of.symm Y : Fin 2 → Fin 2 → ℝ)‖) := by
  have hdet : (ArchR.diagOne y * k).det ≠ 0 := by
    rw [Matrix.det_mul, det_diagOne]; exact mul_ne_zero hy (isK_det_ne_zero hk)
  have hp : ArchR.diagOneMulCoords y k ∈ ArchR.glSet := diagOneMulCoords_mem hk hy
  rw [derivW_of_det_ne_zero Y W hdet]
  unfold rightDeriv
  rw [← glSet_eq, norm_iteratedFDerivWithin_one _ (isOpen_glSet.uniqueDiffOn _ hp)]
  have hvec : (Matrix.of.symm (Matrix.of (Matrix.of.symm (ArchR.diagOne y * k)) * Y) : Fin 2 →
      Fin 2 → ℝ) =
      mulCoords ℝ (ArchR.diagOneMulCoords y k) (Matrix.of.symm Y) := by
    rw [mulCoords_apply]
    rfl
  rw [hvec]
  calc ‖fderivWithin ℝ (ArchR.asPi W) ArchR.glSet (Matrix.of.symm (ArchR.diagOne y * k))
          (mulCoords ℝ (ArchR.diagOneMulCoords y k) (Matrix.of.symm Y))‖
        ≤ ‖fderivWithin ℝ (ArchR.asPi W) ArchR.glSet (Matrix.of.symm (ArchR.diagOne y * k))‖ *
            ‖mulCoords ℝ (ArchR.diagOneMulCoords y k)
                (Matrix.of.symm Y)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderivWithin ℝ (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ *
            (‖mulCoords ℝ‖ * max 1 |y| * ‖(Matrix.of.symm Y : Fin 2 → Fin 2 → ℝ)‖) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          calc ‖mulCoords ℝ (ArchR.diagOneMulCoords y k) (Matrix.of.symm Y)‖
                ≤ ‖mulCoords ℝ‖ * ‖ArchR.diagOneMulCoords y k‖ *
                    ‖(Matrix.of.symm Y : Fin 2 → Fin 2 → ℝ)‖ :=
                  (mulCoords ℝ).le_opNorm₂ _ _
            _ ≤ ‖mulCoords ℝ‖ * max 1 |y| * ‖(Matrix.of.symm Y : Fin 2 → Fin 2 → ℝ)‖ := by
                  gcongr
                  exact norm_diagOneMulCoords_le hk y

private def defo (g X : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := g *
    (1 + τ • X)

private theorem defo_zero (g X : Matrix (Fin 2) (Fin 2) ℝ) : defo g X 0 = g := by simp [defo]

private theorem diagOne_mul_defo (y : ℝ) (g X : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ) :
    ArchR.diagOne y * defo g X τ = ArchR.diagOne y * g + τ • (ArchR.diagOne y * g * X) := by
  simp only [defo, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_assoc]

private theorem det_defo (g X : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ) : (defo g X τ).det = g.det *
    (1 + τ • X).det :=
  Matrix.det_mul _ _

private theorem continuous_det_one_add_smul (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun τ : ℝ => (1 + τ • X).det := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

private theorem exists_defo_interval (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det := by
  have hc := continuous_det_one_add_smul X
  have h0 : (1 + (0 : ℝ) • X).det = 1 := by simp
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), (1 / 2 : ℝ) < (1 + τ • X).det := by
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt, h0] at this
    exact this.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min (ε / 2) 1, by positivity, min_le_right _ _, fun τ hτ => ?_⟩
  have hτε : τ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact lt_of_le_of_lt (hτ.trans (min_le_left _ _)) (by linarith)
  exact (hball τ hτε).le

private theorem det_defo_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    {X : Matrix (Fin 2) (Fin 2) ℝ} {t₀ τ : ℝ}
    (ht₀ : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) (hτ : |τ| ≤ t₀) :
        (defo g X τ).det ≠ 0 := by
  rw [det_defo]
  exact mul_ne_zero hg (by linarith [ht₀ τ hτ])

private theorem det_one_add_smul_ne_zero {X : Matrix (Fin 2) (Fin 2) ℝ} {t₀ τ : ℝ}
    (ht₀ : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) (hτ : |τ| ≤ t₀) :
        (1 + τ • X).det ≠ 0 := by
  linarith [ht₀ τ hτ]

private def defoDir (X : Matrix (Fin 2) (Fin 2) ℝ) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
    (1 + τ • X)⁻¹ * X

private theorem defoDir_zero (X : Matrix (Fin 2) (Fin 2) ℝ) : defoDir X 0 = X := by simp [defoDir]

private theorem inv_mul_dir {g X : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {y : ℝ} (τ : ℝ)
    (hy : y ≠ 0) :
    (ArchR.diagOne y * defo g X τ)⁻¹ * (ArchR.diagOne y * g * X) = defoDir X τ := by
  have hdy : IsUnit (ArchR.diagOne y).det := by rw [det_diagOne]; exact hy.isUnit
  unfold defo defoDir
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc
      (ArchR.diagOne y) g X,
    Matrix.nonsing_inv_mul_cancel_left _ _ hdy, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hg.isUnit]

private def dirDeriv (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g X : Matrix (Fin 2) (Fin 2) ℝ)
    (τ y : ℝ) : ℂ :=
  fderiv ℝ (ArchR.asPi W) (Matrix.of.symm (ArchR.diagOne y * defo g X τ))
      (Matrix.of.symm (ArchR.diagOne y * g * X))

private theorem hasDerivAt_defo (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {y τ : ℝ}
        (hy : y ≠ 0)
    (h1 : (1 + τ • X).det ≠ 0) :
    HasDerivAt (fun t : ℝ => W (ArchR.diagOne y * defo g X t)) (dirDeriv W g X τ y) τ := by
  have hdet : (ArchR.diagOne y * g + τ • (ArchR.diagOne y * g * X)).det ≠ 0 := by
    rw [← diagOne_mul_defo, Matrix.det_mul, det_diagOne, det_defo]
    exact mul_ne_zero hy (mul_ne_zero hg h1)
  have h := hasDerivAt_asPi_line W hWs (ArchR.diagOne y * g) (ArchR.diagOne y * g * X) hdet
  have hfun : (fun t : ℝ => W (ArchR.diagOne y * g + t • (ArchR.diagOne y * g * X))) =
      fun t => W (ArchR.diagOne y * defo g X t) := by
    funext t; rw [diagOne_mul_defo]
  rw [hfun, ← diagOne_mul_defo] at h
  convert h using 1
  unfold dirDeriv
  have hdet' : (ArchR.diagOne y * defo g X τ).det ≠ 0 := by rwa [diagOne_mul_defo]
  rw [fderiv_asPi_apply_eq_derivW W hdet']
  rfl

private theorem dirDeriv_eq_derivW (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) {y τ : ℝ} (hy : y ≠ 0) (h1 : (1 + τ • X).det ≠ 0) :
    dirDeriv W g X τ y = derivW (defoDir X τ) W (ArchR.diagOne y * defo g X τ) := by
  have hdet : (ArchR.diagOne y * defo g X τ).det ≠ 0 := by
    rw [Matrix.det_mul, det_diagOne, det_defo]; exact mul_ne_zero hy (mul_ne_zero hg h1)
  unfold dirDeriv
  rw [fderiv_asPi_apply_eq_derivW W hdet]
  congr 1
  rw [show Matrix.of (Matrix.of.symm (ArchR.diagOne y * g * X)) = ArchR.diagOne y * g * X from rfl]
  exact inv_mul_dir hg τ hy

private theorem dirDeriv_zero (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) {y : ℝ} (hy : y ≠ 0) : dirDeriv W g X 0 y = derivW X W
        (ArchR.diagOne y * g) := by
  rw [dirDeriv_eq_derivW W hg X hy (by simp), defoDir_zero, defo_zero]

private theorem norm_dirDeriv_le {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) {C₁ σ N : ℝ} (hC₁ : 0 ≤ C₁)
        (hσ : 0 ≤ σ) (hN : 0 ≤ N)
    (henv : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ 1 (ArchR.asPi W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C₁ * env σ N y)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {τ : ℝ}
    (h1 : (1 + τ • X).det ≠ 0) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (hτ₀1 : τ₀ ≤ 1)
        (hT : τ₀ ≤ |iwT (defo g X τ)|)
    {τ₁ : ℝ} (hT' : |iwT (defo g X τ)| ≤ τ₁) {y : ℝ} (hy : y ≠ 0) :
    ‖dirDeriv W g X τ y‖ ≤
      (|rowNorm (defo g X τ)| ^ P.centralExponent.re * |rowNorm (defo g X τ)|) *
        (C₁ * τ₀ ^ (-(σ + N)) * (‖mulCoords ℝ‖ * max 1 τ₁ *
            ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖)) *
        env σ (N - 1) y := by
  set gτ := defo g X τ with hgτ
  have hgτdet : gτ.det ≠ 0 := by rw [hgτ, det_defo]; exact mul_ne_zero hg h1
  have hrn : rowNorm gτ ≠ 0 := (rowNorm_pos hgτdet).ne'
  have hK : ArchR.IsK (kPart gτ) := isK_kPart hgτdet
  have hLd : LeftLaws P (derivW (defoDir X τ) W) := leftLaws_derivW hL hWs _
  have hyT : y * iwT gτ ≠ 0 := mul_ne_zero hy (fun h => by
    rw [h, abs_zero] at hT; exact absurd hT (not_le.2 hτ₀))
  rw [dirDeriv_eq_derivW W hg X hy h1, ← hgτ, hLd.diagOne_mul hgτdet y, norm_mul,
      norm_reduce_factor P _ hrn]
  have horb := norm_derivW_orbit_le (defoDir X τ) W hK hyT
  have henv1 := henv (y * iwT gτ) (kPart gτ) hK hyT
  have hresc : env σ N (y * iwT gτ) ≤ τ₀ ^ (-(σ + N)) * env σ N y := env_rescale hσ hN hτ₀ hτ₀1 hT
      hy
  have hmax : max 1 |y * iwT gτ| ≤ max 1 τ₁ * max 1 |y| := by
    rw [abs_mul]
    refine max_le ?_ ?_
    · nlinarith [le_max_left 1 τ₁, le_max_left 1 |y|]
    · calc |y| * |iwT gτ| ≤ max 1 |y| * max 1 τ₁ :=
            mul_le_mul (le_max_right _ _) (hT'.trans (le_max_right _ _)) (abs_nonneg _)
                (by positivity)
        _ = max 1 τ₁ * max 1 |y| := mul_comm _ _
  have hfac : 0 ≤ |rowNorm gτ| ^ P.centralExponent.re * |rowNorm gτ| := by positivity
  set K := C₁ * τ₀ ^ (-(σ + N)) * (‖mulCoords ℝ‖ * max 1 τ₁ *
      ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖)
    with hK
  have hτpow : 0 ≤ τ₀ ^ (-(σ + N)) := Real.rpow_nonneg hτ₀.le _
  have hD : ‖derivW (defoDir X τ) W (ArchR.diagOne (y * iwT gτ) * kPart gτ)‖ ≤ K * env σ
      (N - 1) y := by
    have hA : C₁ * env σ N (y * iwT gτ) ≤ C₁ * (τ₀ ^ (-(σ + N)) * env σ N y) :=
      mul_le_mul_of_nonneg_left hresc hC₁
    have hB : ‖mulCoords ℝ‖ * max 1 |y * iwT gτ| *
        ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖ ≤
        ‖mulCoords ℝ‖ * (max 1 τ₁ * max 1 |y|) * ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 →
            ℝ)‖ := by
      gcongr
    calc ‖derivW (defoDir X τ) W (ArchR.diagOne (y * iwT gτ) * kPart gτ)‖
          ≤ (C₁ * env σ N (y * iwT gτ)) *
              (‖mulCoords ℝ‖ * max 1 |y * iwT gτ| *
                  ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖) :=
            horb.trans (mul_le_mul_of_nonneg_right henv1 (by positivity))
      _ ≤ (C₁ * (τ₀ ^ (-(σ + N)) * env σ N y)) *
              (‖mulCoords ℝ‖ * (max 1 τ₁ * max 1 |y|) *
                  ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖) :=
            mul_le_mul hA hB (by positivity) (mul_nonneg hC₁ (mul_nonneg hτpow (env_nonneg _ _ _)))
      _ = K * (env σ N y * max 1 |y| ^ 1) := by rw [hK]; ring
      _ ≤ K * env σ (N - 1) y := by
            apply mul_le_mul_of_nonneg_left _ (by rw [hK]; positivity)
            have := env_mul_max_pow_le (σ := σ) (N := N) (y := y) 1
            simpa using this
  calc |rowNorm gτ| ^ P.centralExponent.re * |rowNorm gτ| *
          ‖derivW (defoDir X τ) W (ArchR.diagOne (y * iwT gτ) * kPart gτ)‖
        ≤ |rowNorm gτ| ^ P.centralExponent.re * |rowNorm gτ| * (K * env σ (N - 1) y) :=
          mul_le_mul_of_nonneg_left hD hfac
    _ = |rowNorm gτ| ^ P.centralExponent.re * |rowNorm gτ| * K * env σ (N - 1) y := by ring

private theorem continuousAt_dirDeriv (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {y τ : ℝ}
        (hy : y ≠ 0)
    (h1 : (1 + τ • X).det ≠ 0) : ContinuousAt (fun t : ℝ => dirDeriv W g X t y) τ := by
  have hpath : Continuous fun t : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X t) : Fin 2 →
      Fin 2 → ℝ) := by
    have : (fun t : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X t) : Fin 2 → Fin 2 → ℝ)) =
        fun t => Matrix.of.symm (ArchR.diagOne y * g) + t • Matrix.of.symm
            (ArchR.diagOne y * g * X) := by
      funext t; rw [diagOne_mul_defo]; rfl
    rw [this]
    fun_prop
  have hp : Matrix.of.symm (ArchR.diagOne y * defo g X τ) ∈ ArchR.glSet := by
    change (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul, det_diagOne, det_defo]
    exact mul_ne_zero hy (mul_ne_zero hg h1)
  have hcont : ContinuousOn (fderiv ℝ (ArchR.asPi W)) ArchR.glSet :=
    hWs.continuousOn_fderiv_of_isOpen isOpen_glSet (by simp)
  have hcat : ContinuousAt (fderiv ℝ (ArchR.asPi W))
      (Matrix.of.symm (ArchR.diagOne y * defo g X τ)) :=
    hcont.continuousAt (isOpen_glSet.mem_nhds hp)
  have hcomp : ContinuousAt (fun t : ℝ => fderiv ℝ (ArchR.asPi W)
      (Matrix.of.symm (ArchR.diagOne y * defo g X t))) τ :=
    ContinuousAt.comp (g := fderiv ℝ (ArchR.asPi W)) hcat hpath.continuousAt
  exact (ContinuousLinearMap.apply ℝ ℂ (Matrix.of.symm
      (ArchR.diagOne y * g * X))).continuous.continuousAt.comp hcomp

private theorem aestronglyMeasurable_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f {0}ᶜ) : AEStronglyMeasurable f volume := by
  have h := hf.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
  have hrest : (volume : Measure ℝ).restrict ({0}ᶜ : Set ℝ) = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (measure_singleton (0 : ℝ)))
  rwa [hrest] at h

private theorem ae_ne_zero : ∀ᵐ y : ℝ ∂volume, y ≠ 0 :=
  compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))

private def zw (u : ℂ) (a : ZMod 2) (s : ℂ) (y : ℝ) : ℂ :=
  ArchR.quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹

private theorem zetaIntegrand_eq (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2)
    (s : ℂ) (y : ℝ) : ArchR.zetaIntegrand W g u a s y = W (ArchR.diagOne y * g) * zw u a s y := by
  simp only [ArchR.zetaIntegrand, zw, mul_assoc]

private theorem norm_quasiChar (u : ℂ) (a : ZMod 2) {y : ℝ}
    (hy : y ≠ 0) : ‖ArchR.quasiChar u a y‖ = |y| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
  have h1 : ‖(if a = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · simp
    · rcases hy.lt_or_gt with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]
  rw [h1, mul_one]

private theorem norm_zw (u : ℂ) (a : ZMod 2) (s : ℂ) {y : ℝ} (hy : y ≠ 0) : ‖zw u a s y‖ = |y| ^
    (u.re + s.re - 2) := by
  have hy' : 0 < |y| := abs_pos.2 hy
  unfold zw
  rw [norm_mul, norm_mul, norm_quasiChar u a hy, Complex.norm_cpow_eq_rpow_re_of_pos hy', norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_abs, Complex.sub_re, Complex.one_re,
        ← Real.rpow_neg_one,
    ← Real.rpow_add hy', ← Real.rpow_add hy']
  ring_nf

private theorem continuousOn_zw (u : ℂ) (a : ZMod 2) (s : ℂ) : ContinuousOn (zw u a s) {0}ᶜ := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  apply ContinuousAt.continuousWithinAt
  unfold zw ArchR.quasiChar
  have habs : ContinuousAt (fun t : ℝ => ((|t| : ℝ) : ℂ)) y :=
    (Complex.continuous_ofReal.comp continuous_abs).continuousAt
  have hcpow : ∀ e : ℂ, ContinuousAt (fun t : ℝ => ((|t| : ℝ) : ℂ) ^ e) y := fun e =>
    (continuousAt_ofReal_cpow_const |y| e (Or.inr (abs_ne_zero.2 hy0))).comp
        continuous_abs.continuousAt
  have hsgn : ContinuousAt (fun t : ℝ => (if a = 0 then (1 : ℂ) else ((SignType.sign t : ℝ) : ℂ)))
      y := by
    split_ifs
    · exact continuousAt_const
    · exact ((Complex.continuous_ofReal.comp continuous_of_discreteTopology).continuousAt).comp
        (continuousAt_sign_of_ne_zero hy0)
  have hinv : ContinuousAt (fun t : ℝ => (((|t| : ℝ) : ℂ))⁻¹) y :=
    habs.inv₀ (by exact_mod_cast abs_ne_zero.2 hy0)
  exact (((hcpow u).mul hsgn).mul (hcpow (s - 1))).mul hinv

private theorem continuousOn_defo_value (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {τ : ℝ}
        (h1 : (1 + τ • X).det ≠ 0) :
    ContinuousOn (fun y : ℝ => W (ArchR.diagOne y * defo g X τ)) {0}ᶜ := by
  have hp : Continuous fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 →
      ℝ) := by
    have : (fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 → ℝ)) =
        fun y =>
        Matrix.of.symm (ArchR.diagOne 0 * defo g X τ) + y • Matrix.of.symm
            (unitMat 0 0 * defo g X τ) := by
      funext y; rw [diagOne_mul_eq_line]; rfl
    rw [this]; fun_prop
  have hmaps : MapsTo (fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 →
      ℝ)) {0}ᶜ
      ArchR.glSet := by
    intro y hy
    change (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul, det_diagOne, det_defo]
    exact mul_ne_zero hy (mul_ne_zero hg h1)
  exact hWs.continuousOn.comp hp.continuousOn hmaps

private theorem continuousOn_dirDeriv_height (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) {g : Matrix (Fin 2) (Fin 2) ℝ}
        (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) {τ : ℝ} (h1 : (1 + τ • X).det ≠ 0) :
    ContinuousOn (fun y : ℝ => dirDeriv W g X τ y) {0}ᶜ := by
  have hp : Continuous fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 →
      ℝ) := by
    have : (fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 → ℝ)) =
        fun y =>
        Matrix.of.symm (ArchR.diagOne 0 * defo g X τ) + y • Matrix.of.symm
            (unitMat 0 0 * defo g X τ) := by
      funext y; rw [diagOne_mul_eq_line]; rfl
    rw [this]; fun_prop
  have hv : Continuous fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * g * X) : Fin 2 → Fin 2 →
      ℝ) := by
    have : (fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * g * X) : Fin 2 → Fin 2 → ℝ)) = fun y =>
        Matrix.of.symm (ArchR.diagOne 0 * g * X) + y • Matrix.of.symm (unitMat 0 0 * g * X) := by
      funext y; rw [diagOne_mul_eq_line, Matrix.add_mul, Matrix.smul_mul]; rfl
    rw [this]; fun_prop
  have hmaps : MapsTo (fun y : ℝ => (Matrix.of.symm (ArchR.diagOne y * defo g X τ) : Fin 2 → Fin 2 →
      ℝ)) {0}ᶜ
      ArchR.glSet := by
    intro y hy
    change (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul, det_diagOne, det_defo]
    exact mul_ne_zero hy (mul_ne_zero hg h1)
  have hcont : ContinuousOn (fderiv ℝ (ArchR.asPi W)) ArchR.glSet :=
    hWs.continuousOn_fderiv_of_isOpen isOpen_glSet (by simp)
  exact (hcont.comp hp.continuousOn hmaps).clm_apply hv.continuousOn

private theorem continuous_defo (g X : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (defo g X) := by
  unfold defo
  exact continuous_const.matrix_mul (continuous_const.add (continuous_id.smul continuous_const))

private theorem abs_le_iff_mem_Icc {t₀ τ : ℝ} : |τ| ≤ t₀ ↔ τ ∈ Icc (-t₀) t₀ := by
  rw [mem_Icc, abs_le]

private theorem exists_iwT_bounds {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (hdet : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) :
    ∃ τlo τhi : ℝ, 0 < τlo ∧ τlo ≤ 1 ∧ ∀ τ : ℝ, |τ| ≤ t₀ → τlo ≤ |iwT (defo g X τ)| ∧ |iwT
        (defo g X τ)| ≤ τhi := by
  have hdetτ : ∀ τ ∈ Icc (-t₀) t₀, (defo g X τ).det ≠ 0 := fun τ hτ =>
    det_defo_ne_zero hg hdet (abs_le_iff_mem_Icc.2 hτ)
  have hcont : ContinuousOn (fun τ : ℝ => |iwT (defo g X τ)|) (Icc (-t₀) t₀) := by
    have hrow : Continuous fun τ : ℝ => rowSq (defo g X τ) := by
      unfold rowSq
      exact (((continuous_defo g X).matrix_elem 1 0).pow 2).add
          (((continuous_defo g X).matrix_elem 1 1).pow 2)
    have hdc : Continuous fun τ : ℝ => (defo g X τ).det := (continuous_defo g X).matrix_det
    refine ContinuousOn.abs ?_
    unfold iwT
    exact hdc.continuousOn.div hrow.continuousOn fun τ hτ => (rowSq_pos (hdetτ τ hτ)).ne'
  have hK : IsCompact (Icc (-t₀) t₀) := isCompact_Icc
  have hne : (Icc (-t₀) t₀).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨τm, hτm, hmin⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨τM, hτM, hmax⟩ := hK.exists_isMaxOn hne hcont
  have hpos : 0 < |iwT (defo g X τm)| := by
    rw [abs_pos]
    unfold iwT
    exact div_ne_zero (hdetτ τm hτm) (rowSq_pos (hdetτ τm hτm)).ne'
  refine ⟨min |iwT (defo g X τm)| 1, |iwT (defo g X τM)|, lt_min hpos one_pos, min_le_right _ _,
      fun τ hτ => ?_⟩
  have hτ' := abs_le_iff_mem_Icc.1 hτ
  exact ⟨(min_le_left _ _).trans (hmin hτ'), hmax hτ'⟩

private theorem exists_factor_bound (P : RealArchParam) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀)
        (hdet : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, |τ| ≤ t₀ →
      |rowNorm (defo g X τ)| ^ P.centralExponent.re * |rowNorm (defo g X τ)| ≤ B := by
  have hdetτ : ∀ τ ∈ Icc (-t₀) t₀, (defo g X τ).det ≠ 0 := fun τ hτ =>
    det_defo_ne_zero hg hdet (abs_le_iff_mem_Icc.2 hτ)
  have hrn : Continuous fun τ : ℝ => |rowNorm (defo g X τ)| := by
    unfold rowNorm rowSq
    exact (Real.continuous_sqrt.comp ((((continuous_defo g X).matrix_elem 1 0).pow 2).add
      (((continuous_defo g X).matrix_elem 1 1).pow 2))).abs
  have hcont : ContinuousOn (fun τ : ℝ => |rowNorm (defo g X τ)| ^ P.centralExponent.re * |rowNorm
      (defo g X τ)|)
      (Icc (-t₀) t₀) := by
    refine ContinuousOn.mul (hrn.continuousOn.rpow_const fun τ hτ => Or.inl ?_) hrn.continuousOn
    rw [abs_ne_zero]
    exact (rowNorm_pos (hdetτ τ hτ)).ne'
  have hne : (Icc (-t₀) t₀).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨τM, hτM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨max (|rowNorm (defo g X τM)| ^ P.centralExponent.re * |rowNorm (defo g X τM)|) 0,
      le_max_right _ _,
    fun τ hτ => (hmax (abs_le_iff_mem_Icc.1 hτ)).trans (le_max_left _ _)⟩

private theorem exists_dir_bound (X : Matrix (Fin 2) (Fin 2) ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hdet : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, |τ| ≤ t₀ → ‖(Matrix.of.symm (defoDir X τ) : Fin 2 → Fin 2 → ℝ)‖ ≤
        B := by
  have hcontAt : ∀ τ ∈ Icc (-t₀) t₀,
      ContinuousAt (fun t : ℝ => (Matrix.of.symm (defoDir X t) : Fin 2 → Fin 2 → ℝ)) τ := by
    intro τ hτ
    have hd : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet (abs_le_iff_mem_Icc.2 hτ)
    have haff : Continuous fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • X :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hRi : ContinuousAt Ring.inverse ((1 : Matrix (Fin 2) (Fin 2) ℝ) + τ • X).det := by
      simpa using NormedRing.inverse_continuousAt (Units.mk0 _ hd)
    have hinv : ContinuousAt (fun t : ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℝ) + t • X)⁻¹) τ :=
      ContinuousAt.comp (f := fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • X) (g := Inv.inv)
        (continuousAt_matrix_inv _ hRi) (haff.continuousAt (x := τ))
    have hmat : ContinuousAt (fun t : ℝ => defoDir X t) τ := by
      unfold defoDir
      exact hinv.mul continuousAt_const
    have hsymm : Continuous (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
        (Matrix.of.symm M : Fin 2 → Fin 2 → ℝ)) :=
      continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
    exact hsymm.continuousAt.comp hmat
  have hcont : ContinuousOn (fun t : ℝ => ‖(Matrix.of.symm (defoDir X t) : Fin 2 → Fin 2 → ℝ)‖)
      (Icc (-t₀) t₀) :=
    fun τ hτ => (hcontAt τ hτ).norm.continuousWithinAt
  have hne : (Icc (-t₀) t₀).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨τM, hτM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  exact ⟨‖(Matrix.of.symm (defoDir X τM) : Fin 2 → Fin 2 → ℝ)‖, norm_nonneg _,
    fun τ hτ => hmax (abs_le_iff_mem_Icc.1 hτ)⟩

private theorem exists_value_domination {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    {C₀ σ N : ℝ} (hC₀ : 0 ≤ C₀) (hσ : 0 ≤ σ) (hN : 0 ≤ N)
    (henv0 : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C₀ * env σ N y)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {t₀ : ℝ}
        (ht₀ : 0 < t₀)
    (hdet : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ τ : ℝ, |τ| ≤ t₀ → ∀ y : ℝ, y ≠ 0 → ‖W
        (ArchR.diagOne y * defo g X τ)‖ ≤ K₀ * env σ N y := by
  obtain ⟨τlo, τhi, hlo, hlo1, hT⟩ := exists_iwT_bounds hg X ht₀ hdet
  obtain ⟨B, hB, hfac⟩ := exists_factor_bound P hg X ht₀ hdet
  refine ⟨B * (C₀ * τlo ^ (-(σ + N))), by positivity, fun τ hτ y hy => ?_⟩
  have hgτ : (defo g X τ).det ≠ 0 := det_defo_ne_zero hg hdet hτ
  have hrn : rowNorm (defo g X τ) ≠ 0 := (rowNorm_pos hgτ).ne'
  have hK : ArchR.IsK (kPart (defo g X τ)) := isK_kPart hgτ
  have hyT : y * iwT (defo g X τ) ≠ 0 := mul_ne_zero hy (fun h => by
    have := (hT τ hτ).1; rw [h, abs_zero] at this; exact absurd this (not_le.2 hlo))
  rw [hL.diagOne_mul hgτ y, norm_mul, norm_reduce_factor P _ hrn, norm_orbit_eq]
  have h0 := henv0 (y * iwT (defo g X τ)) (kPart (defo g X τ)) hK hyT
  have hres : env σ N (y * iwT (defo g X τ)) ≤ τlo ^ (-(σ + N)) * env σ N y :=
    env_rescale hσ hN hlo hlo1 (hT τ hτ).1 hy
  calc |rowNorm (defo g X τ)| ^ P.centralExponent.re * |rowNorm (defo g X τ)| *
        ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet
            (ArchR.diagOneMulCoords (y * iwT (defo g X τ))
          (kPart (defo g X τ)))‖
        ≤ B * (C₀ * (τlo ^ (-(σ + N)) * env σ N y)) :=
          mul_le_mul (hfac τ hτ) (h0.trans (mul_le_mul_of_nonneg_left hres hC₀)) (norm_nonneg _) hB
    _ = B * (C₀ * τlo ^ (-(σ + N))) * env σ N y := by ring

private theorem exists_dirDeriv_domination {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) {C₁ σ N : ℝ} (hC₁ : 0 ≤ C₁)
        (hσ : 0 ≤ σ) (hN : 0 ≤ N)
    (henv1 : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ 1 (ArchR.asPi W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C₁ * env σ N y)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) {t₀ : ℝ}
        (ht₀ : 0 < t₀)
    (hdet : ∀ τ : ℝ, |τ| ≤ t₀ → (1 / 2 : ℝ) ≤ (1 + τ • X).det) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ τ : ℝ, |τ| ≤ t₀ → ∀ y : ℝ, y ≠ 0 → ‖dirDeriv W g X τ y‖ ≤ K₁ * env σ
        (N - 1) y := by
  obtain ⟨τlo, τhi, hlo, hlo1, hT⟩ := exists_iwT_bounds hg X ht₀ hdet
  obtain ⟨B, hB, hfac⟩ := exists_factor_bound P hg X ht₀ hdet
  obtain ⟨BY, hBY, hdir⟩ := exists_dir_bound X ht₀ hdet
  refine ⟨B * (C₁ * τlo ^ (-(σ + N)) * (‖mulCoords ℝ‖ * max 1 τhi * BY)), by positivity,
      fun τ hτ y hy => ?_⟩
  have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet hτ
  have hmain := norm_dirDeriv_le hL hWs hC₁ hσ hN henv1 hg X h1 hlo hlo1 (hT τ hτ).1 (hT τ hτ).2 hy
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (env_nonneg _ _ _))
  have hτpow : 0 ≤ τlo ^ (-(σ + N)) := Real.rpow_nonneg hlo.le _
  exact mul_le_mul (hfac τ hτ) (by gcongr; exact hdir τ hτ) (by positivity) hB

section Parametric

variable {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}

private theorem zint_package (hL : LeftLaws P W) (hWs : ContDiffOn ℝ (⊤ : ℕ∞)
    (ArchR.asPi W) ArchR.glSet)
    {C₀ C₁ σ N : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hσ : 0 ≤ σ) (hN : 0 ≤ N)
    (henv0 : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C₀ * env σ N y)
    (henv1 : ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ 1 (ArchR.asPi W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C₁ * env σ N y)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
        (a : ZMod 2) (σ₁ : ℝ)
    (hlo : 1 + σ < σ₁ + u.re) (hhi : σ₁ + u.re < N - 1) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      (∀ s : ℂ, s.re = σ₁ →
        Integrable (ArchR.zetaIntegrand (derivW X W) g u a s) ∧
        HasDerivAt (fun τ : ℝ => ∫ y, ArchR.zetaIntegrand W (defo g X τ) u a s y)
          (∫ y, ArchR.zetaIntegrand (derivW X W) g u a s y) 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s.re = σ₁ → ∀ h : ℝ, h ≠ 0 → |h| < δ →
        ‖(h : ℂ)⁻¹ * ((∫ y, ArchR.zetaIntegrand W (defo g X h) u a s y) - ∫ y,
            ArchR.zetaIntegrand W g u a s y) -
            ∫ y, ArchR.zetaIntegrand (derivW X W) g u a s y‖ ≤ ε) := by
  obtain ⟨t₀, ht₀, ht₀1, hdet⟩ := exists_defo_interval X
  obtain ⟨K₀, hK₀, hdom0⟩ := exists_value_domination hL hC₀ hσ hN henv0 hg X ht₀ hdet
  obtain ⟨K₁, hK₁, hdom1⟩ := exists_dirDeriv_domination hL hWs hC₁ hσ hN henv1 hg X ht₀ hdet
  set α : ℝ := u.re + σ₁ - 2 with hα
  have hα0 : -1 < α - σ := by rw [hα]; linarith
  have hα1 : α - N < -1 := by rw [hα]; linarith
  have hα1' : α - (N - 1) < -1 := by rw [hα]; linarith
  have hbd0 : Integrable fun y : ℝ => K₀ * (env σ N y * |y| ^ α) :=
      (integrable_env_mul_rpow hα0 hα1).const_mul K₀
  have hbd1 : Integrable fun y : ℝ => K₁ * (env σ (N - 1) y * |y| ^ α) :=
    (integrable_env_mul_rpow hα0 hα1').const_mul K₁
  have hF_meas : ∀ (s : ℂ) (τ : ℝ), |τ| ≤ t₀ →
      AEStronglyMeasurable (fun y : ℝ => ArchR.zetaIntegrand W (defo g X τ) u a s y) volume := by
    intro s τ hτ
    have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet hτ
    have hc := (continuousOn_defo_value W hWs hg X h1).mul (continuousOn_zw u a s)
    refine aestronglyMeasurable_of_continuousOn (hc.congr fun y _ => ?_)
    exact zetaIntegrand_eq W _ u a s y
  have hF'_meas : ∀ (s : ℂ) (τ : ℝ), |τ| ≤ t₀ →
      AEStronglyMeasurable (fun y : ℝ => dirDeriv W g X τ y * zw u a s y) volume := by
    intro s τ hτ
    have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet hτ
    exact aestronglyMeasurable_of_continuousOn
      ((continuousOn_dirDeriv_height W hWs hg X h1).mul (continuousOn_zw u a s))
  have hnorm_bd0 : ∀ (s : ℂ), s.re = σ₁ → ∀ τ : ℝ, |τ| ≤ t₀ → ∀ᵐ y : ℝ ∂volume,
      ‖ArchR.zetaIntegrand W (defo g X τ) u a s y‖ ≤ K₀ * (env σ N y * |y| ^ α) := by
    intro s hs τ hτ
    filter_upwards [ae_ne_zero] with y hy
    rw [zetaIntegrand_eq, norm_mul, norm_zw u a s hy, hs, show u.re + σ₁ - 2 = α from rfl,
        ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hdom0 τ hτ y hy) (Real.rpow_nonneg (abs_nonneg _) _)
  have hnorm_bd1 : ∀ (s : ℂ), s.re = σ₁ → ∀ τ : ℝ, |τ| ≤ t₀ → ∀ᵐ y : ℝ ∂volume,
      ‖dirDeriv W g X τ y * zw u a s y‖ ≤ K₁ * (env σ (N - 1) y * |y| ^ α) := by
    intro s hs τ hτ
    filter_upwards [ae_ne_zero] with y hy
    rw [norm_mul, norm_zw u a s hy, hs, show u.re + σ₁ - 2 = α from rfl, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hdom1 τ hτ y hy) (Real.rpow_nonneg (abs_nonneg _) _)
  have hderiv : ∀ (s : ℂ), s.re = σ₁ → ∀ τ₁ : ℝ, |τ₁| < t₀ →
      Integrable (fun y : ℝ => dirDeriv W g X τ₁ y * zw u a s y) ∧
      HasDerivAt (fun τ : ℝ => ∫ y, ArchR.zetaIntegrand W (defo g X τ) u a s y)
        (∫ y, dirDeriv W g X τ₁ y * zw u a s y) τ₁ := by
    intro s hs τ₁ hτ₁
    have hI : Ioo (-t₀) t₀ ∈ 𝓝 τ₁ := Ioo_mem_nhds (by linarith [(abs_lt.1 hτ₁).1]) (abs_lt.1 hτ₁).2
    have hIoo : ∀ τ ∈ Ioo (-t₀) t₀, |τ| ≤ t₀ := fun τ hτ => (abs_lt.2 ⟨hτ.1, hτ.2⟩).le
    refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F' := fun τ y => dirDeriv W g X τ y * zw u a s y)
      (bound := fun y => K₁ * (env σ (N - 1) y * |y| ^ α)) hI ?_ ?_
          (hF'_meas s τ₁ hτ₁.le) ?_ hbd1 ?_
    · exact Filter.eventually_of_mem hI fun τ hτ => hF_meas s τ (hIoo τ hτ)
    · refine Integrable.mono' hbd0 (hF_meas s τ₁ hτ₁.le) (hnorm_bd0 s hs τ₁ hτ₁.le)
    · filter_upwards [ae_ne_zero] with y hy τ hτ
      rw [norm_mul, norm_zw u a s hy, hs, show u.re + σ₁ - 2 = α from rfl, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdom1 τ (hIoo τ hτ) y hy)
          (Real.rpow_nonneg (abs_nonneg _) _)
    · filter_upwards [ae_ne_zero] with y hy τ hτ
      have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet (hIoo τ hτ)
      have hd := (hasDerivAt_defo W hWs hg X hy h1).mul_const (zw u a s y)
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      exact zetaIntegrand_eq W _ u a s y
  have hcontD : ∀ (s : ℂ), s.re = σ₁ →
      ContinuousOn (fun τ : ℝ => ∫ y, dirDeriv W g X τ y * zw u a s y) (Ioo (-t₀) t₀) := by
    intro s hs
    have hIoo : ∀ τ ∈ Ioo (-t₀) t₀, |τ| ≤ t₀ := fun τ hτ => (abs_lt.2 ⟨hτ.1, hτ.2⟩).le
    refine continuousOn_of_dominated (bound := fun y => K₁ * (env σ (N - 1) y * |y| ^ α))
      (fun τ hτ => hF'_meas s τ (hIoo τ hτ)) (fun τ hτ => hnorm_bd1 s hs τ (hIoo τ hτ)) hbd1 ?_
    filter_upwards [ae_ne_zero] with y hy
    intro τ hτ
    have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet (hIoo τ hτ)
    exact ((continuousAt_dirDeriv W hWs hg X hy h1).mul continuousAt_const).continuousWithinAt
  have hIt₀ : Ioo (-t₀) t₀ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) ht₀
  have hIoo : ∀ τ ∈ Ioo (-t₀) t₀, |τ| ≤ t₀ := fun τ hτ => (abs_lt.2 ⟨hτ.1, hτ.2⟩).le
  have h10 : (1 + (0 : ℝ) • X).det ≠ 0 := by simp
  have hmod : Tendsto (fun τ : ℝ => ∫ y, ‖dirDeriv W g X τ y - dirDeriv W g X 0 y‖ * |y| ^ α) (𝓝 0)
      (𝓝 0) := by
    have hbd2 : Integrable fun y : ℝ => (K₁ + K₁) * (env σ (N - 1) y * |y| ^ α) :=
      (integrable_env_mul_rpow hα0 hα1').const_mul (K₁ + K₁)
    have hlim := tendsto_integral_filter_of_dominated_convergence (l := 𝓝 (0 : ℝ))
        (μ := (volume : Measure ℝ))
      (F := fun (τ : ℝ) (y : ℝ) => ‖dirDeriv W g X τ y - dirDeriv W g X 0 y‖ * |y| ^ α)
      (f := fun _ => (0 : ℝ)) (fun y => (K₁ + K₁) * (env σ (N - 1) y * |y| ^ α)) ?_ ?_ hbd2 ?_
    · simpa using hlim
    · filter_upwards [hIt₀] with τ hτ
      have h1 : (1 + τ • X).det ≠ 0 := det_one_add_smul_ne_zero hdet (hIoo τ hτ)
      refine aestronglyMeasurable_of_continuousOn ?_
      refine (((continuousOn_dirDeriv_height W hWs hg X h1).sub
        (continuousOn_dirDeriv_height W hWs hg X h10)).norm).mul ?_
      exact continuous_abs.continuousOn.rpow_const fun y hy => Or.inl (abs_ne_zero.2 hy)
    · filter_upwards [hIt₀] with τ hτ
      filter_upwards [ae_ne_zero] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hτb := hdom1 τ (hIoo τ hτ) y hy
      have h0b := hdom1 0 (by rw [abs_zero]; exact ht₀.le) y hy
      have hpow : 0 ≤ |y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
      calc ‖dirDeriv W g X τ y - dirDeriv W g X 0 y‖ * |y| ^ α
          ≤ (‖dirDeriv W g X τ y‖ + ‖dirDeriv W g X 0 y‖) * |y| ^ α :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) hpow
        _ ≤ (K₁ * env σ (N - 1) y + K₁ * env σ (N - 1) y) * |y| ^ α := by gcongr
        _ = (K₁ + K₁) * (env σ (N - 1) y * |y| ^ α) := by ring
    · filter_upwards [ae_ne_zero] with y hy
      have hc : ContinuousAt (fun τ : ℝ => ‖dirDeriv W g X τ y - dirDeriv W g X 0 y‖ * |y| ^ α) 0 :=
        (((continuousAt_dirDeriv W hWs hg X hy h10).sub continuousAt_const).norm).mul
            continuousAt_const
      have := hc.tendsto
      simpa using this
  have hdiff : ∀ (s : ℂ), s.re = σ₁ → ∀ τ : ℝ, |τ| < t₀ →
      ‖(∫ y, dirDeriv W g X τ y * zw u a s y) - ∫ y, dirDeriv W g X 0 y * zw u a s y‖ ≤
        ∫ y, ‖dirDeriv W g X τ y - dirDeriv W g X 0 y‖ * |y| ^ α := by
    intro s hs τ hτ
    have hi := (hderiv s hs τ hτ).1
    have hi0 := (hderiv s hs 0 (by rw [abs_zero]; exact ht₀)).1
    rw [← integral_sub hi hi0]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae ?_))
    filter_upwards [ae_ne_zero] with y hy
    rw [← sub_mul, norm_mul, norm_zw u a s hy, hs]
  have hzero : ∀ s : ℂ, (fun y : ℝ => dirDeriv W g X 0 y * zw u a s y) =ᵐ[volume]
      ArchR.zetaIntegrand (derivW X W) g u a s := by
    intro s
    filter_upwards [ae_ne_zero] with y hy
    rw [dirDeriv_zero W hg X hy, zetaIntegrand_eq]
  refine ⟨t₀, ht₀, fun s hs => ?_, fun ε hε => ?_⟩
  · have h0 := hderiv s hs 0 (by rw [abs_zero]; exact ht₀)
    refine ⟨h0.1.congr (hzero s), ?_⟩
    rw [← integral_congr_ae (hzero s)]
    exact h0.2
  · obtain ⟨δ₁, hδ₁, hη⟩ := Metric.tendsto_nhds_nhds.1 hmod ε hε
    refine ⟨min δ₁ t₀, lt_min hδ₁ ht₀, fun s hs h hh hhδ => ?_⟩
    have hht₀ : |h| < t₀ := lt_of_lt_of_le hhδ (min_le_right _ _)
    have hhδ₁ : |h| < δ₁ := lt_of_lt_of_le hhδ (min_le_left _ _)
    set F : ℝ → ℂ := fun τ => ∫ y, ArchR.zetaIntegrand W (defo g X τ) u a s y with hF
    set D : ℝ → ℂ := fun τ => ∫ y, dirDeriv W g X τ y * zw u a s y with hD
    have huIcc : ∀ τ ∈ uIcc 0 h, |τ| ≤ |h| := fun τ hτ => by
      rcases le_total 0 h with h0 | h0
      · rw [uIcc_of_le h0] at hτ; rw [abs_of_nonneg hτ.1, abs_of_nonneg h0]; exact hτ.2
      · rw [uIcc_of_ge h0] at hτ; rw [abs_of_nonpos hτ.2, abs_of_nonpos h0]; linarith [hτ.1]
    have hderiv' : ∀ τ ∈ uIcc 0 h, HasDerivAt F (D τ) τ := fun τ hτ =>
      (hderiv s hs τ (lt_of_le_of_lt (huIcc τ hτ) hht₀)).2
    have hsub : uIcc 0 h ⊆ Ioo (-t₀) t₀ := fun τ hτ => by
      have := lt_of_le_of_lt (huIcc τ hτ) hht₀
      exact ⟨by linarith [(abs_lt.1 this).1], (abs_lt.1 this).2⟩
    have hcontD' : ContinuousOn D (uIcc 0 h) := (hcontD s hs).mono hsub
    have hint : IntervalIntegrable D volume 0 h := hcontD'.intervalIntegrable
    have hFTC : ∫ τ in (0 : ℝ)..h, D τ = F h - F 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
        hderiv' hint
    have hconst : ∫ _ in (0 : ℝ)..h, D 0 = (h : ℂ) * D 0 := by
      rw [intervalIntegral.integral_const, sub_zero]
      exact Complex.real_smul
    have hkey : (h : ℂ)⁻¹ * (F h - F 0) - D 0 = (h : ℂ)⁻¹ * ∫ τ in (0 : ℝ)..h, (D τ - D 0) := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hFTC, hconst, mul_sub
          (h : ℂ)⁻¹ (F h - F 0),
        ← mul_assoc (h : ℂ)⁻¹ (h : ℂ) (D 0), inv_mul_cancel₀ (by exact_mod_cast hh), one_mul]
    have hbound : ∀ τ ∈ Set.uIoc (0 : ℝ) h, ‖D τ - D 0‖ ≤ ε := by
      intro τ hτ
      have hτh : |τ| ≤ |h| := huIcc τ (uIoc_subset_uIcc hτ)
      have hτδ : |τ| < δ₁ := lt_of_le_of_lt hτh hhδ₁
      have hητ := hη (by rwa [dist_zero_right, Real.norm_eq_abs])
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => by positivity)]
          at hητ
      exact ((hdiff s hs τ (lt_of_le_of_lt hτh hht₀)).trans hητ.le)
    have hD0 : D 0 = ∫ y, ArchR.zetaIntegrand (derivW X W) g u a s y := integral_congr_ae (hzero s)
    have hFh : (∫ y, ArchR.zetaIntegrand W (defo g X h) u a s y) = F h := rfl
    have hF0 : (∫ y, ArchR.zetaIntegrand W g u a s y) = F 0 := by
      simp only [hF, defo_zero]
    rw [← hD0, hFh, hF0, hkey, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |h|⁻¹ * ‖∫ τ in (0 : ℝ)..h, (D τ - D 0)‖ ≤ |h|⁻¹ * (ε * |h - 0|) :=
          mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const hbound)
              (by positivity)
      _ = ε := by rw [sub_zero]; field_simp

end Parametric

end IntegralR

end ArchWhittakerGrowth

end
end SpanIntegralR

section SpanZetaR
set_option autoImplicit false

noncomputable section

open Complex
open LanglandsTunnell LanglandsTunnell.Converse
open ArchWhittakerGrowth.LShift

namespace ArchWhittakerGrowth
namespace ZetaR

private theorem archFactor_eq (Q : RealArchParam) (s : ℂ) : Q.archFactor s = gammaFactor Q.gammaR
    Q.gammaC s := rfl

private theorem epsilonFactor_ne_zero (Q : RealArchParam) : Q.epsilonFactor ≠ 0 := by
  cases Q with
  | principal u₁ a₁ u₂ a₂ =>
    rw [RealArchParam.epsilonFactor_principal]
    refine mul_ne_zero ?_ ?_ <;> unfold signEpsilon <;> split_ifs <;> simp [I_ne_zero]
  | discrete u k hk =>
    rw [RealArchParam.epsilonFactor_discrete]
    exact pow_ne_zero _ I_ne_zero

private def signReal (a : ZMod 2) : ℝ := if a = 0 then 0 else 1

private theorem signShift_eq_signReal (a : ZMod 2) : signShift a = ((signReal a : ℝ) : ℂ) := by
  unfold signShift signReal
  split_ifs <;> simp

private theorem signReal_nonneg (a : ZMod 2) : 0 ≤ signReal a := by
  unfold signReal; split_ifs <;> norm_num

private theorem zmod_sign_left (a a₁ a₂ : ZMod 2) : a₂ + (a + (a₁ + a₂)) = a₁ + a := by
  fin_cases a <;> fin_cases a₁ <;> fin_cases a₂ <;> decide

private theorem zmod_sign_right (a a₁ a₂ : ZMod 2) : a₁ + (a + (a₁ + a₂)) = a₂ + a := by
  fin_cases a <;> fin_cases a₁ <;> fin_cases a₂ <;> decide

private theorem paired_of_sum {μ μ' : ℂ} (h : μ + μ' = 0) (b : ZMod 2) : Paired (μ + signShift b)
    (μ' + signShift b) := by
  refine ⟨2 * signReal b, by linarith [signReal_nonneg b], ?_⟩
  rw [signShift_eq_signReal]
  push_cast
  linear_combination h

private theorem rel_gammaR (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    Multiset.Rel Paired (P.twist u a).gammaR
      (P.twist (-(u + P.centralExponent)) (a + P.centralSign)).gammaR := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp only [RealArchParam.twist, RealArchParam.gammaR, RealArchParam.centralExponent,
      RealArchParam.centralSign]
    rw [zmod_sign_right a a₁ a₂, zmod_sign_left a a₁ a₂, Multiset.pair_comm]
    exact Multiset.Rel.cons (paired_of_sum (by ring) (a₂ + a))
      (Multiset.Rel.cons (paired_of_sum (by ring) (a₁ + a)) Multiset.Rel.zero)
  | discrete u k hk =>
    simp only [RealArchParam.twist, RealArchParam.gammaR]
    exact Multiset.Rel.zero

private theorem rel_gammaC (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    Multiset.Rel Paired (P.twist u a).gammaC
      (P.twist (-(u + P.centralExponent)) (a + P.centralSign)).gammaC := by
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp only [RealArchParam.twist, RealArchParam.gammaC]
    exact Multiset.Rel.zero
  | discrete u k hk =>
    simp only [RealArchParam.twist, RealArchParam.gammaC, RealArchParam.centralExponent]
    refine Multiset.Rel.cons ⟨(k : ℝ), Nat.cast_nonneg k, ?_⟩ Multiset.Rel.zero
    push_cast
    ring

end ArchWhittakerGrowth.ZetaR

end
end SpanZetaR

section SpanZetaInt
set_option autoImplicit false

noncomputable section

open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth

namespace ZetaInt

open DerivR

variable {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}

private theorem iteratedFDerivWithin_asPi_derivW (X : Matrix (Fin 2) (Fin 2) ℝ) (j : ℕ)
    {p : Fin 2 → Fin 2 → ℝ}
    (hp : p ∈ ArchR.glSet) :
    iteratedFDerivWithin ℝ j (ArchR.asPi (derivW X W)) ArchR.glSet p
      = iteratedFDerivWithin ℝ j (rightDeriv X (ArchR.asPi W)) ArchR.glSet p :=
  iteratedFDerivWithin_congr (asPi_derivW_eqOn X W) hp j

private theorem diagOneMulCoords_mem_glSet {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k) :
    ArchR.diagOneMulCoords y k ∈ ArchR.glSet :=
  diagOneMulCoords_mem y k hk hy

private theorem smooth_derivW (hW : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi (derivW X W)) ArchR.glSet :=
  (contDiffOn_rightDeriv X hW).congr (asPi_derivW_eqOn X W)

private theorem decay_top_derivW (hW : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (hdec : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^
          (-(N : ℝ)))
    (X : Matrix (Fin 2) (Fin 2) ℝ) (j N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (derivW X W)) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-(N : ℝ)) := by
  obtain ⟨C, hC⟩ := decay_top_rightDeriv_real X j hW (fun m _ N' => hdec m N') N
  refine ⟨C, fun y k hk hy => ?_⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    norm_num at hy
  rw [iteratedFDerivWithin_asPi_derivW X j (diagOneMulCoords_mem_glSet hy0 hk)]
  exact hC y k hk hy

private theorem decay_zero_derivW (hW : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    (hblow : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k →
        y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^
          (-σ))
    (X : Matrix (Fin 2) (Fin 2) ℝ) (j : ℕ) :
    ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (derivW X W)) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-σ) := by
  obtain ⟨C, σ, hC⟩ := decay_zero_rightDeriv_real X j hW (fun m _ => hblow m)
  refine ⟨C, σ, fun y k hk hy0 hy1 => ?_⟩
  rw [iteratedFDerivWithin_asPi_derivW X j (diagOneMulCoords_mem_glSet hy0 hk)]
  exact hC y k hk hy0 hy1

open MeasureTheory Set Filter Topology

end ZetaInt

end ArchWhittakerGrowth

end
end SpanZetaInt

section SpanBridgeR
set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology

namespace ArchWhittakerGrowth

namespace BridgeR

open ArchWhittakerGrowth.Strip ArchWhittakerGrowth.LShift

private theorem shiftFactor_ne_zero {R C : Multiset ℂ} {N : ℕ} {A : ℝ} (h : ShiftsPos R C N A)
    {s : ℂ} (hs : A ≤ s.re) :
    shiftFactor R C N s ≠ 0 := by
  unfold shiftFactor
  refine mul_ne_zero (Multiset.prod_ne_zero fun hmem => ?_) (Multiset.prod_ne_zero fun hmem => ?_)
  · obtain ⟨μ, hμ, hzero⟩ := Multiset.mem_map.1 hmem
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_ hzero
    have := h.1 μ hμ
    simp only [add_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
    linarith
  · obtain ⟨ν, hν, hzero⟩ := Multiset.mem_map.1 hmem
    have hre : 0 < (s + ν + N).re := by
      have := h.2 ν hν
      simp only [add_re, natCast_re]
      linarith
    rw [Complex.Gammaℂ_def] at hzero
    refine absurd hzero (mul_ne_zero (mul_ne_zero two_ne_zero ?_)
        (Complex.Gamma_ne_zero_of_re_pos hre))
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne')

private theorem one_add_abs_pow_le_exp (t : ℝ) (n : ℕ) : (1 + |t|) ^ n ≤ Real.exp (n * |t|) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |t|]) n

private theorem norm_le_of_edges {R C R' C' : Multiset ℂ} (hrelR : Multiset.Rel Paired R R')
    (hrelC : Multiset.Rel Paired C C') {A B : ℝ} (hAB : A < B) (hA : OffPoleAbscissae R C A)
        (hfar : FarLeft R C A)
    (hBR : ∀ μ ∈ R, 0 < B + μ.re) (hBC : ∀ ν ∈ C, 0 < B + ν.re) :
    ∃ K D : ℝ, 0 ≤ K ∧ ∀ (Φ : ℂ → ℂ) (M : ℝ), 0 ≤ M → Differentiable ℂ Φ →
      (∃ C₀ D₀ : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖Φ s‖ ≤ C₀ * Real.exp (D₀ * |s.im|)) →
      (∀ s : ℂ, s.re = B → ‖gammaFactor R C s * Φ s‖ ≤ M) →
      (∀ s : ℂ, s.re = A → ‖gammaFactor R' C' (1 - s) * Φ s‖ ≤ M) →
      ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖Φ s‖ ≤ K * M * Real.exp (D * |s.im|) := by
  obtain ⟨Kd, hKd⟩ := exists_norm_gammaFactor_le_dual hrelR hrelC hA hfar
  obtain ⟨N, hN⟩ := exists_shiftsPos R C (A - 1)
  have hN' : ShiftsPos R C N A := shiftsPos_mono hN (by linarith)
  obtain ⟨Ksf, hKsf⟩ := exists_norm_shiftFactor_le (R := R) (C := C) B hN
  obtain ⟨Ki, ci, hKi⟩ := exists_norm_inv_shiftFactor_le R C N A B
  obtain ⟨Kp, hKp⟩ := exists_norm_shiftPoly_le R C N A B
  set deg : ℕ := N * Multiset.card R + N * Multiset.card C with hdeg
  obtain ⟨c, hc, hPL⟩ := strip_bound_of_edges A B hAB deg
  set Ke : ℝ := max 1 Kd * max Kp 0 with hKe
  have hKe0 : 0 ≤ Ke := by positivity
  refine ⟨c * Ke * max Ki 0, (deg : ℝ) + ci, by positivity,
      fun Φ M hM hΦ hapr hright hleft s hsA hsB => ?_⟩
  set G : ℂ → ℂ := fun s => Φ s * shiftFactor R C N s with hG
  have hU : IsOpen {s : ℂ | A - 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGdiff : DifferentiableOn ℂ G {s : ℂ | A - 1 < s.re} :=
    (hΦ.differentiableOn).mul (differentiableOn_shiftFactor hN)
  have hstrip_sub : Complex.re ⁻¹' Ioo A B ⊆ {s : ℂ | A - 1 < s.re} := fun s hs => by
    simp only [mem_preimage, mem_Ioo] at hs; simp only [mem_ofPred_eq]; linarith [hs.1]
  have hclos_sub : closure (Complex.re ⁻¹' Ioo A B) ⊆ {s : ℂ | A - 1 < s.re} := by
    refine (Complex.continuous_re.closure_preimage_subset _).trans fun s hs => ?_
    rw [closure_Ioo hAB.ne, mem_preimage, mem_Icc] at hs
    simp only [mem_ofPred_eq]; linarith [hs.1]
  have hGdc : DiffContOnCl ℂ G (Complex.re ⁻¹' Ioo A B) :=
    ⟨hGdiff.mono hstrip_sub, (hGdiff.continuousOn).mono hclos_sub⟩
  have hGapr : ∃ C₁ D₁ : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖G s‖ ≤ C₁ * Real.exp (D₁ * |s.im|) := by
    obtain ⟨C₀, D₀, h0⟩ := hapr
    refine ⟨C₀ * max Ksf 0, D₀, fun s h1 h2 => ?_⟩
    rw [hG]; simp only
    rw [norm_mul]
    have hsf : ‖shiftFactor R C N s‖ ≤ max Ksf 0 := (hKsf s (by linarith) h2).trans
        (le_max_left _ _)
    have hΦs := h0 s h1 h2
    have hC₀ : 0 ≤ C₀ * Real.exp (D₀ * |s.im|) := (norm_nonneg _).trans hΦs
    calc ‖Φ s‖ * ‖shiftFactor R C N s‖ ≤ (C₀ * Real.exp (D₀ * |s.im|)) * max Ksf 0 :=
          mul_le_mul hΦs hsf (norm_nonneg _) hC₀
      _ = C₀ * max Ksf 0 * Real.exp (D₀ * |s.im|) := by ring
  have hGedge : ∀ s : ℂ, s.re = A ∨ s.re = B → ‖G s‖ ≤ (Ke * M) * (1 + |s.im|) ^ deg := by
    intro s hs
    have hoff : OffPoles R C N s := by
      rcases hs with h | h
      · exact hA.offPoles N h
      · exact offPoles_of_re hBR hBC N h.ge
    have hGs : G s = (gammaFactor R C s * Φ s) * shiftPoly R C N s := by
      rw [hG]; simp only
      rw [← gammaFactor_mul_shiftPoly R C N hoff]; ring
    have hsA' : A ≤ s.re := by
      rcases hs with h | h
      · exact h.ge
      · rw [h]; exact hAB.le
    have hsB' : s.re ≤ B := by
      rcases hs with h | h
      · rw [h]; exact hAB.le
      · exact h.le
    have hpoly : ‖shiftPoly R C N s‖ ≤ max Kp 0 * (1 + |s.im|) ^ deg :=
      (hKp s hsA' hsB').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hγΦ : ‖gammaFactor R C s * Φ s‖ ≤ max 1 Kd * M := by
      rcases hs with h | h
      · rw [norm_mul]
        have hcmp := hKd s h
        have hl := hleft s h
        rw [norm_mul] at hl
        have hγ' : 0 ≤ ‖gammaFactor R' C' (1 - s)‖ := norm_nonneg _
        calc ‖gammaFactor R C s‖ * ‖Φ s‖ ≤ (Kd * ‖gammaFactor R' C' (1 - s)‖) * ‖Φ s‖ :=
              mul_le_mul_of_nonneg_right hcmp (norm_nonneg _)
          _ ≤ (max 1 Kd * ‖gammaFactor R' C' (1 - s)‖) * ‖Φ s‖ := by gcongr; exact le_max_right _ _
          _ = max 1 Kd * (‖gammaFactor R' C' (1 - s)‖ * ‖Φ s‖) := by ring
          _ ≤ max 1 Kd * M := mul_le_mul_of_nonneg_left hl (by positivity)
      · calc ‖gammaFactor R C s * Φ s‖ ≤ M := hright s h
          _ = 1 * M := (one_mul M).symm
          _ ≤ max 1 Kd * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    rw [hGs, norm_mul]
    calc ‖gammaFactor R C s * Φ s‖ * ‖shiftPoly R C N s‖ ≤ (max 1 Kd * M) *
           (max Kp 0 * (1 + |s.im|) ^ deg) :=
          mul_le_mul hγΦ hpoly (norm_nonneg _) (by positivity)
      _ = Ke * M * (1 + |s.im|) ^ deg := by rw [hKe]; ring
  have hGint := hPL G (Ke * M) (by positivity) hGdc hGapr hGedge s hsA hsB
  have hsf0 : shiftFactor R C N s ≠ 0 := shiftFactor_ne_zero hN' hsA
  have hΦeq : Φ s = G s * (shiftFactor R C N s)⁻¹ := by
    rw [hG]; simp only; rw [mul_assoc, mul_inv_cancel₀ hsf0, mul_one]
  have hinv : ‖(shiftFactor R C N s)⁻¹‖ ≤ max Ki 0 * Real.exp (ci * |s.im|) :=
    (hKi s hsA hsB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hpow := one_add_abs_pow_le_exp s.im deg
  rw [hΦeq, norm_mul]
  calc ‖G s‖ * ‖(shiftFactor R C N s)⁻¹‖
      ≤ (c * (Ke * M) * (1 + |s.im|) ^ deg) * (max Ki 0 * Real.exp (ci * |s.im|)) :=
        mul_le_mul hGint hinv (norm_nonneg _) (by positivity)
    _ ≤ (c * (Ke * M) * Real.exp (deg * |s.im|)) * (max Ki 0 * Real.exp (ci * |s.im|)) := by gcongr
    _ = c * Ke * max Ki 0 * M * Real.exp (((deg : ℝ) + ci) * |s.im|) := by
        rw [add_mul, Real.exp_add]; ring

section Datum

open ArchWhittakerGrowth.GroupR ArchWhittakerGrowth.DerivR ArchWhittakerGrowth.IntegralR
    ArchWhittakerGrowth.ZetaR
open LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

variable {P : RealArchParam}

private def dq (d : ArchDatumR P) (g X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (h : ℝ)
    (s : ℂ) : ℂ :=
  (h : ℂ)⁻¹ * (d.zetaEntire (defo g X h) u a s - d.zetaEntire g u a s)

private theorem differentiable_dq (d : ArchDatumR P) (g X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (h : ℝ) :
    Differentiable ℂ (dq d g X u a h) :=
  ((d.zetaEntire_differentiable _ u a).sub (d.zetaEntire_differentiable _ u a)).const_mul _

private theorem dq_finiteOrder (d : ArchDatumR P) (g X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (h : ℝ) (A B : ℝ) :
    ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖dq d g X u a h s‖ ≤ C * Real.exp (D * |s.im|) := by
  obtain ⟨C₁, D₁, h₁⟩ := d.zetaEntire_finiteOrder (defo g X h) u a A B
  obtain ⟨C₂, D₂, h₂⟩ := d.zetaEntire_finiteOrder g u a A B
  refine ⟨‖(h : ℂ)⁻¹‖ * (max C₁ 0 + max C₂ 0), max D₁ D₂, fun s hA hB => ?_⟩
  have e1 : Real.exp (D₁ * |s.im|) ≤ Real.exp (max D₁ D₂ * |s.im|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have e2 : Real.exp (D₂ * |s.im|) ≤ Real.exp (max D₁ D₂ * |s.im|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  have b1 : ‖d.zetaEntire (defo g X h) u a s‖ ≤ max C₁ 0 * Real.exp (max D₁ D₂ * |s.im|) :=
    (h₁ s hA hB).trans (mul_le_mul (le_max_left _ _) e1 (Real.exp_pos _).le (le_max_right _ _))
  have b2 : ‖d.zetaEntire g u a s‖ ≤ max C₂ 0 * Real.exp (max D₁ D₂ * |s.im|) :=
    (h₂ s hA hB).trans (mul_le_mul (le_max_left _ _) e2 (Real.exp_pos _).le (le_max_right _ _))
  unfold dq
  rw [norm_mul]
  calc ‖(h : ℂ)⁻¹‖ * ‖d.zetaEntire (defo g X h) u a s - d.zetaEntire g u a s‖
      ≤ ‖(h : ℂ)⁻¹‖ * (max C₁ 0 * Real.exp (max D₁ D₂ * |s.im|) + max C₂ 0 * Real.exp
          (max D₁ D₂ * |s.im|)) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add b1 b2)) (norm_nonneg _)
    _ = ‖(h : ℂ)⁻¹‖ * (max C₁ 0 + max C₂ 0) * Real.exp (max D₁ D₂ * |s.im|) := by ring

private theorem weyl_mul_defo (g X : Matrix (Fin 2) (Fin 2) ℝ) (h : ℝ) :
    ArchR.weyl * defo g X h = defo (ArchR.weyl * g) X h := by
  simp only [defo, Matrix.mul_assoc]

private theorem dq_fe (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2)
    {h : ℝ} (hg : g.det ≠ 0) (hgh : (defo g X h).det ≠ 0) (s : ℂ) :
    dq d (ArchR.weyl * g) X (-(u + P.centralExponent)) (a + P.centralSign) h (1 - s) =
      (P.twist u a).epsilonFactor * dq d g X u a h s := by
  unfold dq
  rw [← weyl_mul_defo, d.functional_equation _ u a s hgh, d.functional_equation _ u a s hg]
  ring

private theorem exists_envelopes (d : ArchDatumR P) :
    ∃ σ : ℝ, 0 ≤ σ ∧ ∀ N : ℕ, ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
        ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi d.W) ArchR.glSet
            (ArchR.diagOneMulCoords y k)‖ ≤ C₀ * env σ N y) ∧
      (∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
        ‖iteratedFDerivWithin ℝ 1 (ArchR.asPi d.W) ArchR.glSet
            (ArchR.diagOneMulCoords y k)‖ ≤ C₁ * env σ N y) := by
  obtain ⟨Cz0, σ0, hz0⟩ := d.decay_zero 0
  obtain ⟨Cz1, σ1, hz1⟩ := d.decay_zero 1
  refine ⟨max (max σ0 σ1) 0, le_max_right _ _, fun N => ?_⟩
  obtain ⟨Ct0, ht0⟩ := d.decay_top 0 N
  obtain ⟨Ct1, ht1⟩ := d.decay_top 1 N
  refine ⟨max (max Ct0 Cz0) 0, max (max Ct1 Cz1) 0, le_max_right _ _, le_max_right _ _,
    fun y k hk hy => ?_, fun y k hk hy => ?_⟩
  · exact (orbitEnvelope_of ht0 hz0 hk hy).trans (mul_le_mul (le_max_left _ _)
      (env_mono hy ((le_max_left _ _).trans (le_max_left _ _)) le_rfl) (env_nonneg _ _ _)
          (le_max_right _ _))
  · exact (orbitEnvelope_of ht1 hz1 hk hy).trans (mul_le_mul (le_max_left _ _)
      (env_mono hy ((le_max_right _ _).trans (le_max_left _ _)) le_rfl) (env_nonneg _ _ _)
          (le_max_right _ _))

private def derivAbscissa (d : ArchDatumR P) : ℝ := max d.zeta_abscissa
    (2 + Classical.choose (exists_envelopes d))

private theorem derivAbscissa_spec (d : ArchDatumR P) :
    d.zeta_abscissa ≤ derivAbscissa d ∧ 2 + Classical.choose
        (exists_envelopes d) ≤ derivAbscissa d :=
  ⟨le_max_left _ _, le_max_right _ _⟩

private theorem right_edge (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2) (σ₁ : ℝ) (hσ₁ : derivAbscissa d < σ₁ + u.re) :
    (∀ s : ℂ, s.re = σ₁ → Integrable (ArchR.zetaIntegrand (derivW X d.W) g u a s) ∧
      HasDerivAt (fun τ : ℝ => ∫ y, ArchR.zetaIntegrand d.W (defo g X τ) u a s y)
        (∫ y, ArchR.zetaIntegrand (derivW X d.W) g u a s y) 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s.re = σ₁ → ∀ h : ℝ, h ≠ 0 → |h| < δ →
      ‖(P.twist u a).archFactor s * dq d g X u a h s - ∫ y, ArchR.zetaIntegrand
          (derivW X d.W) g u a s y‖ ≤ ε) ∧
    (∃ Mb δ : ℝ, 0 < δ ∧ ∀ s : ℂ, s.re = σ₁ → ∀ h : ℝ, h ≠ 0 → |h| < δ →
      ‖(P.twist u a).archFactor s * dq d g X u a h s‖ ≤ Mb) := by
  obtain ⟨hab, henvσ⟩ := derivAbscissa_spec d
  set σ := Classical.choose (exists_envelopes d) with hσdef
  obtain ⟨hσ0, hall⟩ := Classical.choose_spec (exists_envelopes d)
  obtain ⟨N, hN⟩ := exists_nat_gt (σ₁ + u.re + 1)
  obtain ⟨C₀, C₁, hC₀, hC₁, henv0, henv1⟩ := hall N
  have hlo : 1 + σ < σ₁ + u.re := by rw [hσdef]; linarith
  have hhi : σ₁ + u.re < (N : ℝ) - 1 := by linarith
  obtain ⟨t₀, ht₀, hpack, hmod⟩ := zint_package (leftLaws_datum d) d.smooth hC₀ hC₁ hσ0
      (Nat.cast_nonneg N)
    henv0 henv1 hg X u a σ₁ hlo hhi
  obtain ⟨t₁, ht₁, -, hdet⟩ := exists_defo_interval X
  have hid : ∀ s : ℂ, s.re = σ₁ → ∀ h : ℝ, h ≠ 0 → |h| ≤ t₁ →
      (P.twist u a).archFactor s * dq d g X u a h s =
        (h : ℂ)⁻¹ * ((∫ y, ArchR.zetaIntegrand d.W (defo g X h) u a s y) -
          ∫ y, ArchR.zetaIntegrand d.W g u a s y) := by
    intro s hs h hh hht
    have hgh : (defo g X h).det ≠ 0 := det_defo_ne_zero hg hdet hht
    have habs : d.zeta_abscissa < s.re + u.re := by rw [hs]; linarith
    rw [d.zeta_eq _ u a s hgh habs, d.zeta_eq _ u a s hg habs]
    unfold dq; ring
  refine ⟨fun s hs => hpack s hs, fun ε hε => ?_, ?_⟩
  · obtain ⟨δ, hδ, hm⟩ := hmod ε hε
    refine ⟨min δ t₁, lt_min hδ ht₁, fun s hs h hh hhδ => ?_⟩
    rw [hid s hs h hh (le_of_lt (lt_of_lt_of_le hhδ (min_le_right _ _)))]
    exact hm s hs h hh (lt_of_lt_of_le hhδ (min_le_left _ _))
  · obtain ⟨K₁, hK₁, hdom1⟩ := exists_dirDeriv_domination (leftLaws_datum d) d.smooth hC₁ hσ0
        (Nat.cast_nonneg N) henv1
      hg X ht₁ hdet
    set α : ℝ := u.re + σ₁ - 2 with hα
    have hα0 : -1 < α - σ := by rw [hα]; linarith
    have hα1' : α - ((N : ℝ) - 1) < -1 := by rw [hα]; linarith
    have hbd : Integrable fun y : ℝ => K₁ * (env σ ((N : ℝ) - 1) y * |y| ^ α) :=
      (integrable_env_mul_rpow hα0 hα1').const_mul K₁
    set Ib : ℝ := ∫ y : ℝ, K₁ * (env σ ((N : ℝ) - 1) y * |y| ^ α) with hIb
    have hI : ∀ s : ℂ, s.re = σ₁ → ‖∫ y, ArchR.zetaIntegrand (derivW X d.W) g u a s y‖ ≤ Ib := by
      intro s hs
      refine (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
        norm_nonneg _) hbd ?_)
      filter_upwards [ae_ne_zero] with y hy
      rw [zetaIntegrand_eq, norm_mul, norm_zw u a s hy, hs, show u.re + σ₁ - 2 = α from rfl,
          ← mul_assoc,
        ← dirDeriv_zero d.W hg X hy]
      exact mul_le_mul_of_nonneg_right (hdom1 0 (by rw [abs_zero]; exact ht₁.le) y hy)
        (Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨δ, hδ, hm⟩ := hmod 1 one_pos
    refine ⟨Ib + 1, min δ t₁, lt_min hδ ht₁, fun s hs h hh hhδ => ?_⟩
    have h1 := hm s hs h hh (lt_of_lt_of_le hhδ (min_le_left _ _))
    rw [← hid s hs h hh (le_of_lt (lt_of_lt_of_le hhδ (min_le_right _ _)))] at h1
    calc ‖(P.twist u a).archFactor s * dq d g X u a h s‖
        ≤ ‖(P.twist u a).archFactor s * dq d g X u a h s - ∫ y, ArchR.zetaIntegrand
            (derivW X d.W) g u a s y‖ +
            ‖∫ y, ArchR.zetaIntegrand (derivW X d.W) g u a s y‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + Ib := add_le_add h1 (hI s hs)
      _ = Ib + 1 := add_comm _ _

private theorem dq_strip (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2) (A'' B'' : ℝ) (hAB'' : A'' ≤ B'') :
    ∃ D : ℝ,
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h h' : ℝ, h ≠ 0 → |h| < δ → h' ≠ 0 → |h'| < δ →
        ∀ s : ℂ, A'' ≤ s.re → s.re ≤ B'' → ‖dq d g X u a h s - dq d g X u a h' s‖ ≤ ε * Real.exp
            (D * |s.im|)) ∧
      (∃ K δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
        ∀ s : ℂ, A'' ≤ s.re → s.re ≤ B'' → ‖dq d g X u a h s‖ ≤ K * Real.exp (D * |s.im|)) := by
  set Q := P.twist u a with hQ
  set u' : ℂ := -(u + P.centralExponent) with hu'
  set a' : ZMod 2 := a + P.centralSign with ha'
  set Q' := P.twist u' a' with hQ'
  have hrelR : Multiset.Rel Paired Q.gammaR Q'.gammaR := rel_gammaR P u a
  have hrelC : Multiset.Rel Paired Q.gammaC Q'.gammaC := rel_gammaC P u a
  have hwg : (ArchR.weyl * g).det ≠ 0 := by rw [Matrix.det_mul, det_weyl, one_mul]; exact hg
  obtain ⟨LR, hLR⟩ := exists_le_of_multiset Q.gammaR fun μ => -μ.re
  obtain ⟨LC, hLC⟩ := exists_le_of_multiset Q.gammaC fun ν => -ν.re
  set B : ℝ := max (max B'' (max LR LC + 1)) (derivAbscissa d - u.re + 1) with hB
  have hBB'' : B'' ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hBR : ∀ μ ∈ Q.gammaR, 0 < B + μ.re := fun μ hμ => by
    have := hLR μ hμ; have : max LR LC + 1 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
    linarith [le_max_left LR LC]
  have hBC : ∀ ν ∈ Q.gammaC, 0 < B + ν.re := fun ν hν => by
    have := hLC ν hν; have : max LR LC + 1 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
    linarith [le_max_right LR LC]
  have hBabs : derivAbscissa d < B + u.re := by
    have : derivAbscissa d - u.re + 1 ≤ B := le_max_right _ _
    linarith
  set L₀ : ℝ := min A'' (1 - (derivAbscissa d - u'.re + 1)) with hL₀
  obtain ⟨A, hAL, hA, hfar⟩ := exists_left_edge' Q.gammaR Q.gammaC L₀
  have hAA'' : A < A'' := lt_of_lt_of_le hAL (min_le_left _ _)
  have hAB : A < B := lt_of_lt_of_le hAA'' (hAB''.trans hBB'')
  have hAdual : derivAbscissa d < (1 - A) + u'.re := by
    have : A < 1 - (derivAbscissa d - u'.re + 1) := lt_of_lt_of_le hAL (min_le_right _ _)
    linarith
  obtain ⟨-, hRmod, ⟨MbR, δR, hδR, hRbd⟩⟩ := right_edge d hg X u a B hBabs
  obtain ⟨-, hLmod, ⟨MbL, δL, hδL, hLbd⟩⟩ := right_edge d hwg X u' a' (1 - A) hAdual
  obtain ⟨K, D, hK, hPL⟩ := norm_le_of_edges hrelR hrelC hAB hA hfar hBR hBC
  have hε0 : Q.epsilonFactor ≠ 0 := epsilonFactor_ne_zero Q
  have hεpos : 0 < ‖Q.epsilonFactor‖ := norm_pos_iff.2 hε0
  obtain ⟨t₁, ht₁, -, hdet⟩ := exists_defo_interval X
  have hLfe : ∀ s : ℂ, ∀ h : ℝ, |h| ≤ t₁ →
      gammaFactor Q'.gammaR Q'.gammaC (1 - s) * dq d g X u a h s =
        Q.epsilonFactor⁻¹ * (Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h (1 - s)) := by
    intro s h hh
    have hgh : (defo g X h).det ≠ 0 := det_defo_ne_zero hg hdet hh
    rw [dq_fe d X u a hg hgh s, ← archFactor_eq]
    field_simp
    rw [hQ]
  refine ⟨D, fun ε hε => ?_, ?_⟩
  · set ε' : ℝ := ε / (K + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε (by linarith)
    have hKε : K * ε' ≤ ε := by
      rw [hε', mul_div_assoc']
      rw [div_le_iff₀ (by linarith)]; nlinarith
    obtain ⟨δ₁, hδ₁, hR⟩ := hRmod (ε' / 2) (by positivity)
    obtain ⟨δ₂, hδ₂, hL⟩ := hLmod (ε' / 2 * ‖Q.epsilonFactor‖) (by positivity)
    refine ⟨min (min δ₁ δ₂) t₁, lt_min (lt_min hδ₁ hδ₂) ht₁,
        fun h h' hh hhδ hh' hh'δ s hsA hsB => ?_⟩
    have hhδ₁ : |h| < δ₁ := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_left _ _))
    have hh'δ₁ : |h'| < δ₁ := lt_of_lt_of_le hh'δ ((min_le_left _ _).trans (min_le_left _ _))
    have hhδ₂ : |h| < δ₂ := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
    have hh'δ₂ : |h'| < δ₂ := lt_of_lt_of_le hh'δ ((min_le_left _ _).trans (min_le_right _ _))
    have hht : |h| ≤ t₁ := (lt_of_lt_of_le hhδ (min_le_right _ _)).le
    have hh't : |h'| ≤ t₁ := (lt_of_lt_of_le hh'δ (min_le_right _ _)).le
    have hΦdiff : Differentiable ℂ fun s => dq d g X u a h s - dq d g X u a h' s :=
      (differentiable_dq d g X u a h).sub (differentiable_dq d g X u a h')
    have hΦapr : ∃ C₀ D₀ : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B →
        ‖dq d g X u a h s - dq d g X u a h' s‖ ≤ C₀ * Real.exp (D₀ * |s.im|) := by
      obtain ⟨C₁, D₁, h₁⟩ := dq_finiteOrder d g X u a h A B
      obtain ⟨C₂, D₂, h₂⟩ := dq_finiteOrder d g X u a h' A B
      refine ⟨max C₁ 0 + max C₂ 0, max D₁ D₂, fun s h1 h2 => ?_⟩
      have e1 : Real.exp (D₁ * |s.im|) ≤ Real.exp (max D₁ D₂ * |s.im|) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      have e2 : Real.exp (D₂ * |s.im|) ≤ Real.exp (max D₁ D₂ * |s.im|) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      calc ‖dq d g X u a h s - dq d g X u a h' s‖ ≤ ‖dq d g X u a h s‖ + ‖dq d g X u a h' s‖ :=
             norm_sub_le _ _
        _ ≤ max C₁ 0 * Real.exp (max D₁ D₂ * |s.im|) + max C₂ 0 * Real.exp (max D₁ D₂ * |s.im|) :=
            add_le_add ((h₁ s h1 h2).trans (mul_le_mul (le_max_left _ _) e1 (Real.exp_pos _).le
                (le_max_right _ _)))
              ((h₂ s h1 h2).trans (mul_le_mul (le_max_left _ _) e2 (Real.exp_pos _).le
                  (le_max_right _ _)))
        _ = (max C₁ 0 + max C₂ 0) * Real.exp (max D₁ D₂ * |s.im|) := by ring
    have hright : ∀ s : ℂ, s.re = B →
        ‖gammaFactor Q.gammaR Q.gammaC s * (dq d g X u a h s - dq d g X u a h' s)‖ ≤ ε' := by
      intro s hs
      rw [← archFactor_eq, mul_sub]
      have e1 := hR s hs h hh hhδ₁
      have e2 := hR s hs h' hh' hh'δ₁
      calc ‖Q.archFactor s * dq d g X u a h s - Q.archFactor s * dq d g X u a h' s‖
          ≤ ‖Q.archFactor s * dq d g X u a h s - ∫ y, ArchR.zetaIntegrand
              (derivW X d.W) g u a s y‖ +
            ‖Q.archFactor s * dq d g X u a h' s - ∫ y, ArchR.zetaIntegrand
                (derivW X d.W) g u a s y‖ := by
              rw [← norm_neg (Q.archFactor s * dq d g X u a h' s - _)]
              refine (norm_add_le _ _).trans_eq' ?_
              congr 1; ring
        _ ≤ ε' / 2 + ε' / 2 := add_le_add e1 e2
        _ = ε' := by ring
    have hleft : ∀ s : ℂ, s.re = A →
        ‖gammaFactor Q'.gammaR Q'.gammaC (1 - s) *
            (dq d g X u a h s - dq d g X u a h' s)‖ ≤ ε' := by
      intro s hs
      have hs' : (1 - s).re = 1 - A := by simp [hs]
      rw [mul_sub, hLfe s h hht, hLfe s h' hh't, ← mul_sub, norm_mul, norm_inv]
      have e1 := hL (1 - s) hs' h hh hhδ₂
      have e2 := hL (1 - s) hs' h' hh' hh'δ₂
      have hsum : ‖Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h (1 - s) -
            Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h'
                (1 - s)‖ ≤ ε' * ‖Q.epsilonFactor‖ := by
        calc ‖Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h (1 - s) -
              Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h' (1 - s)‖
            ≤ ‖Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h (1 - s) -
                ∫ y, ArchR.zetaIntegrand (derivW X d.W) (ArchR.weyl * g) u' a' (1 - s) y‖ +
              ‖Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h' (1 - s) -
                ∫ y, ArchR.zetaIntegrand (derivW X d.W) (ArchR.weyl * g) u' a' (1 - s) y‖ := by
                rw [← norm_neg (Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h'
                    (1 - s) - _)]
                refine (norm_add_le _ _).trans_eq' ?_
                congr 1; ring
          _ ≤ ε' / 2 * ‖Q.epsilonFactor‖ + ε' / 2 * ‖Q.epsilonFactor‖ := add_le_add e1 e2
          _ = ε' * ‖Q.epsilonFactor‖ := by ring
      calc ‖Q.epsilonFactor‖⁻¹ * ‖Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h (1 - s) -
            Q'.archFactor (1 - s) * dq d (ArchR.weyl * g) X u' a' h' (1 - s)‖
          ≤ ‖Q.epsilonFactor‖⁻¹ * (ε' * ‖Q.epsilonFactor‖) := mul_le_mul_of_nonneg_left hsum
              (by positivity)
        _ = ε' := by field_simp
    have := hPL (fun s => dq d g X u a h s - dq d g X u a h' s) ε' hε'pos.le hΦdiff hΦapr hright
        hleft s
      (hAA''.le.trans hsA) (hsB.trans hBB'')
    exact this.trans (by
      have hexp : 0 ≤ Real.exp (D * |s.im|) := (Real.exp_pos _).le
      calc K * ε' * Real.exp (D * |s.im|) ≤ ε * Real.exp
             (D * |s.im|) := mul_le_mul_of_nonneg_right hKε hexp)
  · refine ⟨K * max (max MbR (‖Q.epsilonFactor‖⁻¹ * MbL)) 0, min (min δR δL) t₁, lt_min
        (lt_min hδR hδL) ht₁,
      fun h hh hhδ s hsA hsB => ?_⟩
    have hhδR : |h| < δR := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_left _ _))
    have hhδL : |h| < δL := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
    have hht : |h| ≤ t₁ := (lt_of_lt_of_le hhδ (min_le_right _ _)).le
    set M : ℝ := max (max MbR (‖Q.epsilonFactor‖⁻¹ * MbL)) 0 with hM
    have hright : ∀ s : ℂ, s.re = B → ‖gammaFactor Q.gammaR Q.gammaC s * dq d g X u a h s‖ ≤ M :=
        fun s hs => by
      rw [← archFactor_eq]
      exact (hRbd s hs h hh hhδR).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hleft : ∀ s : ℂ, s.re = A → ‖gammaFactor Q'.gammaR Q'.gammaC
        (1 - s) * dq d g X u a h s‖ ≤ M := by
      intro s hs
      have hs' : (1 - s).re = 1 - A := by simp [hs]
      rw [hLfe s h hht, norm_mul, norm_inv]
      exact (mul_le_mul_of_nonneg_left (hLbd (1 - s) hs' h hh hhδL) (by positivity)).trans
        ((le_max_right _ _).trans (le_max_left _ _))
    have := hPL (dq d g X u a h) M (le_max_right _ _) (differentiable_dq d g X u a h)
        (dq_finiteOrder d g X u a h A B)
      hright hleft s (hAA''.le.trans hsA) (hsB.trans hBB'')
    simpa [hM, mul_assoc] using this

private def hseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem hseq_pos (n : ℕ) : 0 < hseq n := by unfold hseq; positivity

private theorem hseq_ne_zero (n : ℕ) : hseq n ≠ 0 := (hseq_pos n).ne'

private theorem tendsto_hseq : Tendsto hseq atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

private theorem eventually_abs_hseq_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n in atTop, |hseq n| < δ := by
  have := (tendsto_hseq.eventually (Metric.ball_mem_nhds 0 hδ))
  filter_upwards [this] with n hn
  simpa [Real.dist_eq] using hn

private def zetaEntire' (d : ArchDatumR P) (X g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2)
    (s : ℂ) : ℂ :=
  if g.det = 0 then 0 else limUnder atTop fun n => dq d g X u a (hseq n) s

private theorem cauchySeq_dq (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2) (s : ℂ) : CauchySeq fun n => dq d g X u a (hseq n) s := by
  obtain ⟨D, hC, -⟩ := dq_strip d hg X u a s.re s.re le_rfl
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  have hw : 0 < Real.exp (D * |s.im|) := Real.exp_pos _
  obtain ⟨δ, hδ, hδC⟩ := hC (ε / 2 / Real.exp (D * |s.im|)) (by positivity)
  obtain ⟨N₀, hN₀⟩ := (eventually_abs_hseq_lt hδ).exists_forall_of_atTop
  refine ⟨N₀, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have := hδC (hseq m) (hseq n) (hseq_ne_zero m) (hN₀ m hm) (hseq_ne_zero n)
      (hN₀ n hn) s le_rfl le_rfl
  calc ‖dq d g X u a (hseq m) s - dq d g X u a (hseq n) s‖ ≤ ε / 2 / Real.exp
         (D * |s.im|) * Real.exp (D * |s.im|) :=
        this
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

private theorem tendsto_dq (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2) (s : ℂ) :
    Tendsto (fun n => dq d g X u a (hseq n) s) atTop (𝓝 (zetaEntire' d X g u a s)) := by
  unfold zetaEntire'
  rw [ite_eq_right hg]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_dq d hg X u a s))

private theorem zetaEntire'_of_det_eq_zero (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det = 0) (u : ℂ) (a : ZMod 2) : zetaEntire' d X g u a = fun _ => 0 := by
  funext s; unfold zetaEntire'; rw [ite_eq_left hg]

private theorem tendstoLocallyUniformlyOn_dq (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) :
    TendstoLocallyUniformlyOn (fun n s => dq d g X u a (hseq n) s)
        (zetaEntire' d X g u a) atTop univ := by
  have hcover : (univ : Set ℂ) = ⋃ m : ℕ, {s : ℂ | |s.re| < m ∧ |s.im| < m} := by
    ext s
    simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]
    obtain ⟨m, hm⟩ := exists_nat_gt (max |s.re| |s.im|)
    exact ⟨m, lt_of_le_of_lt (le_max_left _ _) hm, lt_of_le_of_lt (le_max_right _ _) hm⟩
  rw [hcover]
  refine tendstoLocallyUniformlyOn_iUnion (fun m => ?_) fun m => ?_
  · exact (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  · refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    obtain ⟨D, hC, -⟩ := dq_strip d hg X u a (-(m : ℝ)) m (by linarith)
    have hW : 0 < Real.exp (|D| * m) := Real.exp_pos _
    obtain ⟨δ, hδ, hδC⟩ := hC (ε / 2 / Real.exp (|D| * m)) (by positivity)
    filter_upwards [eventually_abs_hseq_lt hδ] with n hn s hs
    rw [dist_comm, dist_eq_norm]
    have hlim := tendsto_dq d hg X u a s
    have hev : ∀ᶠ k in atTop, ‖dq d g X u a (hseq n) s - dq d g X u a (hseq k) s‖ ≤
        ε / 2 / Real.exp (|D| * m) * Real.exp (D * |s.im|) := by
      filter_upwards [eventually_abs_hseq_lt hδ] with k hk
      exact hδC (hseq n) (hseq k) (hseq_ne_zero n) hn (hseq_ne_zero k) hk s
          (le_of_lt (abs_lt.1 hs.1).1)
        (le_of_lt (abs_lt.1 hs.1).2)
    have hle : ‖dq d g X u a (hseq n) s - zetaEntire' d X g u a s‖ ≤
        ε / 2 / Real.exp (|D| * m) * Real.exp (D * |s.im|) :=
      le_of_tendsto ((tendsto_const_nhds.sub hlim).norm) hev
    have hexp : Real.exp (D * |s.im|) ≤ Real.exp (|D| * m) := Real.exp_le_exp.2 (by
      calc D * |s.im| ≤ |D| * |s.im| := mul_le_mul_of_nonneg_right (le_abs_self D) (abs_nonneg _)
        _ ≤ |D| * m := mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg D))
    calc ‖dq d g X u a (hseq n) s - zetaEntire' d X g u a s‖ ≤ ε / 2 / Real.exp (|D| * m) * Real.exp
           (|D| * m) :=
          hle.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

private theorem differentiable_zetaEntire' (d : ArchDatumR P) (X g : Matrix (Fin 2) (Fin 2) ℝ)
    (u : ℂ) (a : ZMod 2) :
    Differentiable ℂ (zetaEntire' d X g u a) := by
  by_cases hg : g.det = 0
  · rw [zetaEntire'_of_det_eq_zero d X hg]; exact differentiable_const _
  · have h := (tendstoLocallyUniformlyOn_dq d hg X u a).differentiableOn
      (Filter.Eventually.of_forall fun n => (differentiable_dq d g X u a (hseq n)).differentiableOn)
          isOpen_univ
    exact differentiableOn_univ.1 h

private theorem zetaEntire'_finiteOrder (d : ArchDatumR P) (X g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (A B : ℝ) :
    ∃ C D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖zetaEntire' d X g u a s‖ ≤ C * Real.exp
        (D * |s.im|) := by
  by_cases hg : g.det = 0
  · refine ⟨0, 0, fun s _ _ => ?_⟩
    rw [zetaEntire'_of_det_eq_zero d X hg]; simp
  rcases lt_or_ge B A with hBA | hAB
  · exact ⟨0, 0, fun s h1 h2 => absurd (h1.trans h2) (not_le.2 hBA)⟩
  obtain ⟨D, -, ⟨K, δ, hδ, hbd⟩⟩ := dq_strip d hg X u a A B hAB
  refine ⟨K, D, fun s h1 h2 => ?_⟩
  refine le_of_tendsto ((tendsto_dq d hg X u a s).norm) ?_
  filter_upwards [eventually_abs_hseq_lt hδ] with n hn
  exact hbd (hseq n) (hseq_ne_zero n) hn s h1 h2

private theorem zetaEntire'_fe (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (u : ℂ) (a : ZMod 2) (s : ℂ) :
    zetaEntire' d X (ArchR.weyl * g) (-(u + P.centralExponent)) (a + P.centralSign) (1 - s) =
      (P.twist u a).epsilonFactor * zetaEntire' d X g u a s := by
  have hwg : (ArchR.weyl * g).det ≠ 0 := by rw [Matrix.det_mul, det_weyl, one_mul]; exact hg
  obtain ⟨t₁, ht₁, -, hdet⟩ := exists_defo_interval X
  have h1 := tendsto_dq d hwg X (-(u + P.centralExponent)) (a + P.centralSign) (1 - s)
  have h2 := (tendsto_dq d hg X u a s).const_mul (P.twist u a).epsilonFactor
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [eventually_abs_hseq_lt ht₁] with n hn
  exact dq_fe d X u a hg (det_defo_ne_zero hg hdet hn.le) s

private theorem zeta_eq' (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0)
    (u : ℂ) (a : ZMod 2) (s : ℂ) (hs : derivAbscissa d < s.re + u.re) :
    Integrable (ArchR.zetaIntegrand (derivW X d.W) g u a s) ∧
      ∫ y, ArchR.zetaIntegrand (derivW X d.W) g u a s y =
          (P.twist u a).archFactor s * zetaEntire' d X g u a s := by
  obtain ⟨hpack, hmod, -⟩ := right_edge d hg X u a s.re hs
  obtain ⟨hint, -⟩ := hpack s rfl
  refine ⟨hint, ?_⟩
  have h2 : Tendsto (fun n => (P.twist u a).archFactor s * dq d g X u a (hseq n) s) atTop
      (𝓝 ((P.twist u a).archFactor s * zetaEntire' d X g u a s)) :=
          (tendsto_dq d hg X u a s).const_mul _
  have h1 : Tendsto (fun n => (P.twist u a).archFactor s * dq d g X u a (hseq n) s) atTop
      (𝓝 (∫ y, ArchR.zetaIntegrand (derivW X d.W) g u a s y)) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hm⟩ := hmod (ε / 2) (by positivity)
    obtain ⟨N₀, hN₀⟩ := (eventually_abs_hseq_lt hδ).exists_forall_of_atTop
    refine ⟨N₀, fun n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hm s rfl (hseq n) (hseq_ne_zero n) (hN₀ n hn)) (by linarith)
  exact tendsto_nhds_unique h1 h2

end Datum

end BridgeR

end ArchWhittakerGrowth

end
end SpanBridgeR

section SpanDatumR
set_option autoImplicit false

noncomputable section

open Complex

namespace ArchWhittakerGrowth

namespace DatumR

open LanglandsTunnell LanglandsTunnell.Converse
open ArchWhittakerGrowth.DerivR ArchWhittakerGrowth.ZetaInt ArchWhittakerGrowth.BridgeR

variable {P : RealArchParam}

private def derivDatum (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) : ArchDatumR P where
  W := derivW X d.W
  smooth := smooth_derivW d.smooth X
  unip_law := derivW_unip_law d.unip_law d.smooth X
  central_law := fun z g hz => derivW_central_law d.central_law d.smooth X z g hz
  zetaEntire := fun g u a s => zetaEntire' d X g u a s
  zetaEntire_differentiable := fun g u a => differentiable_zetaEntire' d X g u a
  zeta_abscissa := derivAbscissa d
  zeta_integrable := fun _ u a s hg hs => (zeta_eq' d X hg u a s hs).1
  zeta_eq := fun _ u a s hg hs => (zeta_eq' d X hg u a s hs).2
  functional_equation := fun _ u a s hg => zetaEntire'_fe d X hg u a s
  zetaEntire_finiteOrder := fun g u a A B => zetaEntire'_finiteOrder d X g u a A B
  decay_top := fun j N => decay_top_derivW d.smooth d.decay_top X j N
  decay_zero := fun j => decay_zero_derivW d.smooth d.decay_zero X j

@[local simp] private theorem derivDatum_W (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (derivDatum d X).W = derivW X d.W := rfl

private theorem derivDatum_W_apply (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0) :
    (derivDatum d X).W g =
      fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet (Matrix.of.symm g) (Matrix.of.symm (g * X)) := by
  rw [derivDatum_W, derivW_of_det_ne_zero X d.W hg]
  unfold rightDeriv
  rw [glSet_eq]
  simp only [Equiv.apply_symm_apply]

private theorem exists_derivDatum (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * X)) :=
  ⟨derivDatum d X, fun _ hg => derivDatum_W_apply d X hg⟩

end DatumR

end ArchWhittakerGrowth

end
end SpanDatumR

open LanglandsTunnell LanglandsTunnell.Converse in
/-- The right derivative along `X` of the Whittaker function of a real archimedean
Whittaker datum, `g ↦ D W(g) (g X)` on invertible matrices, is the Whittaker function of a
real archimedean Whittaker datum for the same parameter. -/
theorem LanglandsTunnell.Converse.ArchDatumR.exists_W_eq_fderivWithin_mul
    (P : RealArchParam) (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * X)) := by
  exact ArchWhittakerGrowth.DatumR.exists_derivDatum d X
