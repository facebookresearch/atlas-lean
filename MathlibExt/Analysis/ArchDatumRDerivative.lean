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
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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

set_option Elab.async false

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

private theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  have h := norm_Gamma_le_norm_Gamma_re hs
  rwa [Complex.Gamma_ofReal, Complex.norm_of_nonneg (Real.Gamma_nonneg_of_nonneg hs.le)] at h

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

private theorem norm_Gamma_mul_le' {s : ℂ} {x₂ : ℝ} (hs : 0 < s.re) (hx : s.re ≤ x₂) :
    ‖Gamma s‖ * ‖Gamma (x₂ : ℂ)‖ ≤ ‖Gamma (s.re : ℂ)‖ * ‖Gamma (x₂ + s.im * I)‖ := by
  have h := norm_Gamma_mul_le hs hx s.im
  rwa [Complex.re_add_im] at h

private theorem norm_Gamma_le_div_mul' {s : ℂ} {x₂ : ℝ} (hs : 0 < s.re) (hx : s.re ≤ x₂) :
    ‖Gamma s‖ ≤ ‖Gamma (s.re : ℂ)‖ / ‖Gamma (x₂ : ℂ)‖ * ‖Gamma (x₂ + s.im * I)‖ := by
  have h := norm_Gamma_le_div_mul hs hx s.im
  rwa [Complex.re_add_im] at h

private theorem exp_mul_le_of_half_le {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    Real.exp (-(π / 2 * |y|)) * ‖Gamma (x : ℂ)‖ ≤ ‖Gamma (1 / 2 : ℂ)‖ * ‖Gamma (x + y * I)‖ := by
  have hcmp := norm_Gamma_mul_le (by norm_num : (0 : ℝ) < 1 / 2) hx y
  have e : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [e] at hcmp
  exact (mul_le_mul_of_nonneg_right (exp_le_norm_Gamma_half y) (norm_nonneg _)).trans hcmp

private theorem realGamma_le_realGamma {α β : ℝ} (hα : 2 ≤ α) (hαβ : α ≤ β) :
    Real.Gamma α ≤ Real.Gamma β :=
  Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 hα) (Set.mem_Ici.2 (hα.trans hαβ)) hαβ

private theorem norm_Gamma_ofReal_le {α β : ℝ} (hα : 2 ≤ α) (hαβ : α ≤ β) :
    ‖Gamma (α : ℂ)‖ ≤ ‖Gamma (β : ℂ)‖ := by
  have h1 : 0 ≤ Real.Gamma α := Real.Gamma_nonneg_of_nonneg (by linarith)
  have h2 : 0 ≤ Real.Gamma β := Real.Gamma_nonneg_of_nonneg (by linarith)
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.norm_of_nonneg h1,
    Complex.norm_of_nonneg h2]
  exact realGamma_le_realGamma hα hαβ

private theorem norm_Gamma_le_norm_Gamma_of_two_le {x₁ x₂ : ℝ} (hx₁ : 2 ≤ x₁) (hx : x₁ ≤ x₂)
    (y : ℝ) :
    ‖Gamma (x₁ + y * I)‖ ≤ ‖Gamma (x₂ + y * I)‖ := by
  have h₂ : 0 < ‖Gamma (x₂ : ℂ)‖ := norm_Gamma_pos (by rw [Complex.ofReal_re]; linarith)
  refine le_of_mul_le_mul_right ?_ h₂
  calc ‖Gamma (x₁ + y * I)‖ * ‖Gamma (x₂ : ℂ)‖
      ≤ ‖Gamma (x₁ : ℂ)‖ * ‖Gamma (x₂ + y * I)‖ := norm_Gamma_mul_le (by linarith) hx y
    _ ≤ ‖Gamma (x₂ : ℂ)‖ * ‖Gamma (x₂ + y * I)‖ :=
        mul_le_mul_of_nonneg_right (norm_Gamma_ofReal_le hx₁ hx) (norm_nonneg _)
    _ = ‖Gamma (x₂ + y * I)‖ * ‖Gamma (x₂ : ℂ)‖ := mul_comm _ _

private theorem norm_Gamma_le_norm_Gamma_of_two_le' {s : ℂ} {x₂ : ℝ} (hs : 2 ≤ s.re)
    (hx : s.re ≤ x₂) :
    ‖Gamma s‖ ≤ ‖Gamma (x₂ + s.im * I)‖ := by
  have h := norm_Gamma_le_norm_Gamma_of_two_le hs hx s.im
  rwa [Complex.re_add_im] at h

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
    show ‖f w / (w + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ _
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
    show ‖f w / (w + ((1 - a : ℝ) : ℂ)) ^ N‖ ≤ 2 ^ N * M
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

private theorem one_add_pow_le_exp_nat (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1 + u) ^ n ≤ Real.exp
    (n * u) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) n

private theorem strip_decay_of_edges (a b : ℝ) (hab : a < b) (n : ℕ) : ∃ c : ℝ, 0 < c ∧
    ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
      DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
      (∃ C D : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C * Real.exp (D * |s.im|)) →
      (∀ s : ℂ, s.re = a ∨ s.re = b → ‖f s‖ ≤ M / (1 + |s.im|) ^ n) →
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ c * M / (1 + |s.im|) ^ n := by
  obtain ⟨c₀, hc₀, h₀⟩ := strip_bound_of_edges a b hab 0
  have hb1 : 0 < b + 1 - a := by linarith
  refine ⟨c₀ * (b + 1 - a) ^ n * 2 ^ n, by positivity, fun f M hM hf hgrowth hedge s hsa hsb => ?_⟩
  obtain ⟨C, D, hCD⟩ := hgrowth

  set g : ℂ → ℂ := fun w => f w * (w + ((1 - a : ℝ) : ℂ)) ^ n
  have hpow_diff : Differentiable ℂ fun w : ℂ => (w + ((1 - a : ℝ) : ℂ)) ^ n :=
    (differentiable_id.add_const _).pow n
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) :=
    ⟨hf.differentiableOn.mul hpow_diff.differentiableOn,
      hf.continuousOn.mul hpow_diff.continuous.continuousOn⟩
  have hgrowth' : ∃ C' D' : ℝ, ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖g w‖ ≤ C' * Real.exp
      (D' * |w.im|) := by
    refine ⟨max C 0 * (b + 1 - a) ^ n, D + n, fun w hwa hwb => ?_⟩
    show ‖f w * (w + ((1 - a : ℝ) : ℂ)) ^ n‖ ≤ _
    rw [norm_mul]
    have h1 : ‖f w‖ ≤ max C 0 * Real.exp (D * |w.im|) :=
      (hCD w hwa hwb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h2 : ‖(w + ((1 - a : ℝ) : ℂ)) ^ n‖ ≤ (b + 1 - a) ^ n * Real.exp (n * |w.im|) := by
      refine (norm_pow_add_le hab hwa hwb n).trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (one_add_pow_le_exp_nat n (abs_nonneg _)) (by positivity)
    calc ‖f w‖ * ‖(w + ((1 - a : ℝ) : ℂ)) ^ n‖
        ≤ (max C 0 * Real.exp (D * |w.im|)) * ((b + 1 - a) ^ n * Real.exp (n * |w.im|)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = max C 0 * (b + 1 - a) ^ n * (Real.exp (D * |w.im|) * Real.exp (n * |w.im|)) := by ring
      _ = max C 0 * (b + 1 - a) ^ n * Real.exp ((D + n) * |w.im|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hedge' : ∀ w : ℂ, w.re = a ∨ w.re = b → ‖g w‖ ≤ M * (b + 1 - a) ^ n * (1 + |w.im|) ^ 0 := by
    intro w hw
    have hwa : a ≤ w.re := by rcases hw with h | h <;> linarith
    have hwb : w.re ≤ b := by rcases hw with h | h <;> linarith
    have hden : 0 < (1 + |w.im|) ^ n := by positivity
    show ‖f w * (w + ((1 - a : ℝ) : ℂ)) ^ n‖ ≤ _
    rw [norm_mul, pow_zero, mul_one]
    calc ‖f w‖ * ‖(w + ((1 - a : ℝ) : ℂ)) ^ n‖
        ≤ (M / (1 + |w.im|) ^ n) * ((b + 1 - a) * (1 + |w.im|)) ^ n :=
          mul_le_mul (hedge w hw) (norm_pow_add_le hab hwa hwb n) (norm_nonneg _)
            (div_nonneg hM hden.le)
      _ = M * (b + 1 - a) ^ n := by
          rw [mul_pow]; field_simp
  have hPL := h₀ g (M * (b + 1 - a) ^ n) (by positivity) hgd hgrowth' hedge' s hsa hsb

  have hPL' : ‖f s‖ * ‖(s + ((1 - a : ℝ) : ℂ)) ^ n‖ ≤ c₀ * (M * (b + 1 - a) ^ n) := by
    have h : ‖f s * (s + ((1 - a : ℝ) : ℂ)) ^ n‖ ≤ c₀ * (M * (b + 1 - a) ^ n) *
        (1 + |s.im|) ^ 0 := hPL
    rwa [norm_mul, pow_zero, mul_one] at h
  have hden : 0 < (1 + |s.im|) ^ n := by positivity
  have hlow := one_add_abs_im_pow_le hsa n

  rw [le_div_iff₀ hden]
  calc ‖f s‖ * (1 + |s.im|) ^ n
      ≤ ‖f s‖ * (2 ^ n * ‖(s + ((1 - a : ℝ) : ℂ)) ^ n‖) := mul_le_mul_of_nonneg_left hlow
          (norm_nonneg _)
    _ = 2 ^ n * (‖f s‖ * ‖(s + ((1 - a : ℝ) : ℂ)) ^ n‖) := by ring
    _ ≤ 2 ^ n * (c₀ * (M * (b + 1 - a) ^ n)) := mul_le_mul_of_nonneg_left hPL' (by positivity)
    _ = c₀ * (b + 1 - a) ^ n * 2 ^ n * M := by ring

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

private theorem exists_le_norm_prod (R : Multiset ℂ) (F : ℂ → ℂ → ℂ)
    (hF : ∀ μ ∈ R, ∃ κ : ℝ, 0 < κ ∧ ∀ s ∈ S, κ ≤ ‖F μ s‖) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s ∈ S, κ ≤ ‖(R.map fun μ => F μ s).prod‖ := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, fun s _ => by simp⟩
  | cons μ R ih =>
    obtain ⟨κ₁, hκ₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ R)
    obtain ⟨κ₂, hκ₂, h₂⟩ := ih fun μ' hμ' => hF μ' (Multiset.mem_cons_of_mem hμ')
    refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_mul (h₁ s hs) (h₂ s hs) hκ₂.le (norm_nonneg _)

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

private theorem exists_le_norm_polyR {A : ℝ} (μ : ℂ) (hμ : 0 < A + μ.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re → κ ≤ ‖polyR N (s + μ)‖ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  refine ⟨((A + μ.re) / (2 * π)) ^ N, by positivity, fun s hsA => ?_⟩
  unfold polyR
  rw [Complex.norm_prod, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  rw [norm_div]
  have e : ‖(2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hπ.le
  have hre : (s + μ + 2 * (j : ℂ)).re = s.re + μ.re + 2 * j := by simp
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc A + μ.re ≤ (s + μ + 2 * (j : ℂ)).re := by rw [hre]; linarith
    _ ≤ ‖s + μ + 2 * (j : ℂ)‖ := Complex.re_le_norm _

private theorem exists_le_norm_polyC {A : ℝ} (ν : ℂ) (hν : 0 < A + ν.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re → κ ≤ ‖polyC N (s + ν)‖ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  refine ⟨((A + ν.re) / (2 * π)) ^ N, by positivity, fun s hsA => ?_⟩
  unfold polyC
  rw [Complex.norm_prod, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  rw [norm_div]
  have e : ‖(2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [e]
  refine div_le_div_of_nonneg_right ?_ hπ.le
  have hre : (s + ν + (j : ℂ)).re = s.re + ν.re + j := by simp
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc A + ν.re ≤ (s + ν + (j : ℂ)).re := by rw [hre]; linarith
    _ ≤ ‖s + ν + (j : ℂ)‖ := Complex.re_le_norm _

private theorem le_norm_of_re_of_im {w : ℂ} {ρ b T : ℝ} (hρ : 0 < ρ) (hre : ρ ≤ w.re) (hb : 0 ≤ b)
    (him : T - b ≤ |w.im|) : ρ / (ρ + 2 * b + 2) * (1 + T) ≤ ‖w‖ := by
  have h1 : ρ ≤ ‖w‖ := hre.trans (Complex.re_le_norm w)
  have h2 : T - b ≤ ‖w‖ := him.trans (Complex.abs_im_le_norm w)
  have hD : 0 < ρ + 2 * b + 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  rcases le_or_gt T (ρ + 2 * b + 1) with hcase | hcase
  · nlinarith [mul_nonneg hρ.le (sub_nonneg.2 hcase), mul_nonneg hD.le (sub_nonneg.2 h1)]
  · have h2b : (0 : ℝ) ≤ 2 * b + 2 := by positivity
    nlinarith [mul_nonneg hD.le (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hcase.le) h2b,
        mul_nonneg hb hρ.le,
      mul_nonneg hb hb]

private theorem abs_im_sub_le {s μ : ℂ} : |s.im| - |μ.im| ≤ |(s + μ).im| := by
  have h := abs_sub_abs_le_abs_sub s.im (-μ.im)
  rw [abs_neg, sub_neg_eq_add] at h
  simpa using h

private theorem norm_two_pi : ‖(2 * (π : ℂ))‖ = 2 * π := by
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

private theorem exists_le_norm_polyR_pow {A : ℝ} (μ : ℂ) (hμ : 0 < A + μ.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re → κ * (1 + |s.im|) ^ N ≤ ‖polyR N (s + μ)‖ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hD : (0 : ℝ) < A + μ.re + 2 * |μ.im| + 2 := by positivity
  refine ⟨((A + μ.re) / (A + μ.re + 2 * |μ.im| + 2) / (2 * π)) ^ N, by positivity, fun s hsA => ?_⟩
  unfold polyR
  rw [Complex.norm_prod, ← mul_pow, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  rw [norm_div, norm_two_pi, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hπ.le
  have hre : A + μ.re ≤ (s + μ + 2 * (j : ℂ)).re := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.re_ofNat,
      Complex.im_ofNat]
    linarith
  have him : |s.im| - |μ.im| ≤ |(s + μ + 2 * (j : ℂ)).im| := by
    have e : (s + μ + 2 * (j : ℂ)).im = (s + μ).im := by simp
    rw [e]
    exact abs_im_sub_le
  exact le_norm_of_re_of_im hμ hre (abs_nonneg _) him

private theorem exists_le_norm_polyC_pow {A : ℝ} (ν : ℂ) (hν : 0 < A + ν.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re → κ * (1 + |s.im|) ^ N ≤ ‖polyC N (s + ν)‖ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hD : (0 : ℝ) < A + ν.re + 2 * |ν.im| + 2 := by positivity
  refine ⟨((A + ν.re) / (A + ν.re + 2 * |ν.im| + 2) / (2 * π)) ^ N, by positivity, fun s hsA => ?_⟩
  unfold polyC
  rw [Complex.norm_prod, ← mul_pow, ← Finset.card_range N, ← Finset.prod_const, Finset.card_range]
  refine Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
  rw [norm_div, norm_two_pi, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hπ.le
  have hre : A + ν.re ≤ (s + ν + (j : ℂ)).re := by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have him : |s.im| - |ν.im| ≤ |(s + ν + (j : ℂ)).im| := by
    have e : (s + ν + (j : ℂ)).im = (s + ν).im := by simp
    rw [e]
    exact abs_im_sub_le
  exact le_norm_of_re_of_im hν hre (abs_nonneg _) him

private theorem exists_le_norm_prod_pow {S : Set ℂ} (R : Multiset ℂ) (F : ℂ → ℂ → ℂ) (n : ℕ)
    (hF : ∀ μ ∈ R, ∃ κ : ℝ, 0 < κ ∧ ∀ s ∈ S, κ * (1 + |s.im|) ^ n ≤ ‖F μ s‖) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s ∈ S, κ * (1 + |s.im|) ^ (n * Multiset.card R) ≤
        ‖(R.map fun μ => F μ s).prod‖ := by
  induction R using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, fun s _ => by simp⟩
  | cons μ R ih =>
    obtain ⟨κ₁, hκ₁, h₁⟩ := hF μ (Multiset.mem_cons_self μ R)
    obtain ⟨κ₂, hκ₂, h₂⟩ := ih fun μ' hμ' => hF μ' (Multiset.mem_cons_of_mem hμ')
    refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun s hs => ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, Nat.mul_succ, pow_add]
    calc κ₁ * κ₂ * ((1 + |s.im|) ^ (n * Multiset.card R) * (1 + |s.im|) ^ n)
        = (κ₁ * (1 + |s.im|) ^ n) * (κ₂ * (1 + |s.im|) ^ (n * Multiset.card R)) := by ring
      _ ≤ ‖F μ s‖ * ‖(R.map fun μ => F μ s).prod‖ :=
          mul_le_mul (h₁ s hs) (h₂ s hs) (by positivity) (norm_nonneg _)

private theorem exists_le_norm_shiftPoly_pow {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re →
      κ * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C) ≤ ‖shiftPoly R C N s‖ := by
  obtain ⟨κ₁, hκ₁, h₁⟩ := exists_le_norm_prod_pow (S := {s : ℂ | A ≤ s.re}) R
      (fun μ s => polyR N (s + μ)) N
    fun μ hμ => by
      obtain ⟨κ, hκ, hk⟩ := exists_le_norm_polyR_pow μ (hR μ hμ) N
      exact ⟨κ, hκ, fun s hs => hk s hs⟩
  obtain ⟨κ₂, hκ₂, h₂⟩ := exists_le_norm_prod_pow (S := {s : ℂ | A ≤ s.re}) C
      (fun ν s => polyC N (s + ν)) N
    fun ν hν => by
      obtain ⟨κ, hκ, hk⟩ := exists_le_norm_polyC_pow ν (hC ν hν) N
      exact ⟨κ, hκ, fun s hs => hk s hs⟩
  refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun s hsA => ?_⟩
  unfold shiftPoly
  rw [norm_mul, pow_add]
  calc κ₁ * κ₂ * ((1 + |s.im|) ^ (N * Multiset.card R) * (1 + |s.im|) ^ (N * Multiset.card C))
      = (κ₁ * (1 + |s.im|) ^ (N * Multiset.card R)) *
          (κ₂ * (1 + |s.im|) ^ (N * Multiset.card C)) := by ring
    _ ≤ _ := mul_le_mul (h₁ s hsA) (h₂ s hsA) (by positivity) (norm_nonneg _)

private def _root_.ArchWhittakerGrowth.LShift.strip (A B : ℝ) : Set ℂ := {s | A ≤ s.re ∧ s.re ≤ B}

private theorem mem_strip {A B : ℝ} {s : ℂ} : s ∈ strip A B ↔ A ≤ s.re ∧ s.re ≤ B := Iff.rfl

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
      simp only [Set.mem_setOf_eq] at hs
      have := h.1 μ hμ
      simp; linarith
    exact ((differentiableAt_Gammaℝ_of_re_pos hre).comp s
      ((differentiableAt_id.add_const μ).add_const _)).differentiableWithinAt
  · intro s hs
    have hre : 0 < (s + ν + (N : ℂ)).re := by
      simp only [Set.mem_setOf_eq] at hs
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

private theorem exists_le_norm_shiftPoly {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re) (N : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, A ≤ s.re → κ ≤ ‖shiftPoly R C N s‖ := by
  obtain ⟨κ₁, hκ₁, h₁⟩ := exists_le_norm_prod (S := {s : ℂ | A ≤ s.re}) R
      (fun μ s => polyR N (s + μ))
    fun μ hμ => by
      obtain ⟨κ, hκ, hk⟩ := exists_le_norm_polyR μ (hR μ hμ) N
      exact ⟨κ, hκ, fun s hs => hk s hs⟩
  obtain ⟨κ₂, hκ₂, h₂⟩ := exists_le_norm_prod (S := {s : ℂ | A ≤ s.re}) C
      (fun ν s => polyC N (s + ν))
    fun ν hν => by
      obtain ⟨κ, hκ, hk⟩ := exists_le_norm_polyC ν (hC ν hν) N
      exact ⟨κ, hκ, fun s hs => hk s hs⟩
  refine ⟨κ₁ * κ₂, mul_pos hκ₁ hκ₂, fun s hsA => ?_⟩
  unfold shiftPoly
  rw [norm_mul]
  exact mul_le_mul (h₁ s hsA) (h₂ s hsA) hκ₂.le (norm_nonneg _)

private theorem shiftPoly_ne_zero_of_re {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re) (N : ℕ) {s : ℂ} (hs : A ≤ s.re) : shiftPoly R C N s ≠ 0 := by
  obtain ⟨κ, hκ, h⟩ := exists_le_norm_shiftPoly hR hC N
  exact norm_pos_iff.1 (hκ.trans_le (h s hs))

private theorem gammaFactor_eq_div {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re) (N : ℕ) {s : ℂ} (hs : A ≤ s.re) :
    gammaFactor R C s = shiftFactor R C N s / shiftPoly R C N s := by
  rw [eq_div_iff (shiftPoly_ne_zero_of_re hR hC N hs)]
  exact gammaFactor_mul_shiftPoly R C N (offPoles_of_re hR hC N hs)

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

private theorem interior_decay_of_edges (R C : Multiset ℂ) {A c₀ σ₁ : ℝ} (hAc : A < c₀)
    (hcσ : c₀ ≤ σ₁)
    (hR : ∀ μ ∈ R, 0 < c₀ + μ.re) (hC : ∀ ν ∈ C, 0 < c₀ + ν.re) (hA : OffPoleAbscissae R C A)
        (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : ℂ → ℂ) (M : ℝ), 0 ≤ M → Differentiable ℂ Φ →
        (∃ C₀ D : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ σ₁ → ‖Φ s‖ ≤ C₀ * Real.exp (D * |s.im|)) →
        (∀ s : ℂ, s.re = A ∨ s.re = σ₁ → ‖gammaFactor R C s * Φ s‖ ≤ M / (1 + |s.im|) ^ n) →
        ∀ s : ℂ, c₀ ≤ s.re → s.re ≤ σ₁ → ‖gammaFactor R C s * Φ s‖ ≤ c * M / (1 + |s.im|) ^ n := by
  have hAσ : A < σ₁ := hAc.trans_le hcσ
  have hσA : 0 < σ₁ + 1 - A := by linarith
  obtain ⟨N, hN⟩ := exists_shiftsPos R C (A - 1)
  obtain ⟨K, hK⟩ := exists_norm_shiftPoly_le R C N A σ₁
  obtain ⟨K₂, hK₂⟩ := exists_norm_shiftFactor_le σ₁ hN
  obtain ⟨κ, hκ, hκle⟩ := exists_le_norm_shiftPoly_pow hR hC N
  obtain ⟨c₁, hc₁, hstrip⟩ := strip_bound_of_edges A σ₁ hAσ
      (N * Multiset.card R + N * Multiset.card C)
  refine ⟨c₁ * (max K 1 * (σ₁ + 1 - A) ^ n) * 2 ^ n / κ, by positivity,
      fun Φ M hM hΦ hgrowth hedge s hs₀ hs₁ => ?_⟩

  have hGd : DiffContOnCl ℂ (fun w => Φ w * shiftFactor R C N w * (w + ((1 - A : ℝ) : ℂ)) ^ n)
      (Complex.re ⁻¹' Set.Ioo A σ₁) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [Complex.closure_preimage_re, closure_Ioo hAσ.ne]
    refine (hΦ.differentiableOn.mul ((differentiableOn_shiftFactor hN).mono fun w hw => ?_)).mul
      ((differentiable_id.add_const _).pow n).differentiableOn
    have hw1 : A ≤ w.re := hw.1
    show A - 1 < w.re
    linarith
  have hGgrowth : ∃ C₀ D : ℝ, ∀ w : ℂ, A ≤ w.re → w.re ≤ σ₁ →
      ‖Φ w * shiftFactor R C N w * (w + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤ C₀ * Real.exp (D * |w.im|) := by
    obtain ⟨C₀, D, hCD⟩ := hgrowth
    refine ⟨max C₀ 0 * max K₂ 0 * (σ₁ + 1 - A) ^ n, D + n, fun w hwA hwσ => ?_⟩
    rw [norm_mul, norm_mul]
    have h1 : ‖Φ w‖ ≤ max C₀ 0 * Real.exp (D * |w.im|) :=
      (hCD w hwA hwσ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h2 : ‖shiftFactor R C N w‖ ≤ max K₂ 0 := (hK₂ w (by linarith) hwσ).trans (le_max_left _ _)
    have h3 : ‖(w + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤ (σ₁ + 1 - A) ^ n * Real.exp (n * |w.im|) := by
      refine (norm_pow_add_le hAσ hwA hwσ n).trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (one_add_pow_le_exp_nat n (abs_nonneg _)) (by positivity)
    calc ‖Φ w‖ * ‖shiftFactor R C N w‖ * ‖(w + ((1 - A : ℝ) : ℂ)) ^ n‖
        ≤ (max C₀ 0 * Real.exp (D * |w.im|) * max K₂ 0) *
            ((σ₁ + 1 - A) ^ n * Real.exp (n * |w.im|)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
              (by positivity)
      _ = max C₀ 0 * max K₂ 0 * (σ₁ + 1 - A) ^ n *
          (Real.exp (D * |w.im|) * Real.exp (n * |w.im|)) := by ring
      _ = max C₀ 0 * max K₂ 0 * (σ₁ + 1 - A) ^ n * Real.exp ((D + n) * |w.im|) := by
          rw [← Real.exp_add]; congr 2; ring

  have hGedge : ∀ w : ℂ, w.re = A ∨ w.re = σ₁ →
      ‖Φ w * shiftFactor R C N w * (w + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤
        M * (max K 1 * (σ₁ + 1 - A) ^ n) * (1 + |w.im|) ^
            (N * Multiset.card R + N * Multiset.card C) := by
    intro w hw
    have hoff : OffPoles R C N w := by
      rcases hw with h | h
      · exact hA.offPoles N h
      · exact offPoles_of_re hR hC N (by rw [h]; exact hcσ)
    have hwA : A ≤ w.re := by rcases hw with h | h <;> linarith
    have hwσ : w.re ≤ σ₁ := by rcases hw with h | h <;> linarith
    have hsplit : Φ w * shiftFactor R C N w = (gammaFactor R C w * Φ w) * shiftPoly R C N w := by
      rw [← gammaFactor_mul_shiftPoly R C N hoff]; ring
    rw [hsplit, norm_mul, norm_mul]
    have h1 := hedge w hw
    have h2 : ‖shiftPoly R C N w‖ ≤ max K 1 * (1 + |w.im|) ^
        (N * Multiset.card R + N * Multiset.card C) :=
      (hK w hwA hwσ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have h3 : ‖(w + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤ (σ₁ + 1 - A) ^ n * (1 + |w.im|) ^ n := by
      rw [← mul_pow]; exact norm_pow_add_le hAσ hwA hwσ n
    have hpos : (0 : ℝ) < (1 + |w.im|) ^ n := by positivity
    calc ‖gammaFactor R C w * Φ w‖ * ‖shiftPoly R C N w‖ * ‖(w + ((1 - A : ℝ) : ℂ)) ^ n‖
        ≤ (M / (1 + |w.im|) ^ n * (max K 1 * (1 + |w.im|) ^
            (N * Multiset.card R + N * Multiset.card C))) *
            ((σ₁ + 1 - A) ^ n * (1 + |w.im|) ^ n) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hM hpos.le)) h3 (norm_nonneg _)
            (by positivity)
      _ = M * (max K 1 * (σ₁ + 1 - A) ^ n) * (1 + |w.im|) ^
          (N * Multiset.card R + N * Multiset.card C) := by
          field_simp
  have hG := hstrip (fun w => Φ w * shiftFactor R C N w * (w + ((1 - A : ℝ) : ℂ)) ^ n)
    (M * (max K 1 * (σ₁ + 1 - A) ^ n)) (by positivity) hGd hGgrowth hGedge s (by linarith) hs₁

  have hsA : A ≤ s.re := by linarith

  have hoff : OffPoles R C N s := offPoles_of_re hR hC N hs₀
  have hsp := shiftPoly_ne_zero_of_re hR hC N hs₀
  have hG' : ‖gammaFactor R C s * Φ s‖ * ‖shiftPoly R C N s‖ * ‖(s + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤
      c₁ * (M * (max K 1 * (σ₁ + 1 - A) ^ n)) * (1 + |s.im|) ^
          (N * Multiset.card R + N * Multiset.card C) := by
    have hsplit : Φ s * shiftFactor R C N s * (s + ((1 - A : ℝ) : ℂ)) ^ n =
        (gammaFactor R C s * Φ s) * shiftPoly R C N s * (s + ((1 - A : ℝ) : ℂ)) ^ n := by
      rw [← gammaFactor_mul_shiftPoly R C N hoff]; ring
    have h : ‖Φ s * shiftFactor R C N s * (s + ((1 - A : ℝ) : ℂ)) ^ n‖ ≤
        c₁ * (M * (max K 1 * (σ₁ + 1 - A) ^ n)) * (1 + |s.im|) ^
            (N * Multiset.card R + N * Multiset.card C) := hG
    rwa [hsplit, norm_mul, norm_mul] at h

  have hlow₁ := hκle s hs₀
  have hlow₂ := one_add_abs_im_pow_le hsA n
  have hdeg : (0 : ℝ) < (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C) := by positivity
  have hden : (0 : ℝ) < (1 + |s.im|) ^ n := by positivity

  have hmain : ‖gammaFactor R C s * Φ s‖ * (κ * (1 + |s.im|) ^
      (N * Multiset.card R + N * Multiset.card C)) *
      (1 + |s.im|) ^ n ≤
      2 ^ n * (c₁ * (M * (max K 1 * (σ₁ + 1 - A) ^ n)) *
        (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) := by
    calc ‖gammaFactor R C s * Φ s‖ * (κ * (1 + |s.im|) ^
           (N * Multiset.card R + N * Multiset.card C)) *
          (1 + |s.im|) ^ n
        ≤ ‖gammaFactor R C s * Φ s‖ * ‖shiftPoly R C N s‖ *
            (2 ^ n * ‖(s + ((1 - A : ℝ) : ℂ)) ^ n‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlow₁ (norm_nonneg _)) hlow₂ (by positivity)
              (by positivity)
      _ = 2 ^ n * (‖gammaFactor R C s * Φ s‖ * ‖shiftPoly R C N s‖ * ‖(s + ((1 - A : ℝ) : ℂ)) ^
          n‖) := by ring
      _ ≤ 2 ^ n * (c₁ * (M * (max K 1 * (σ₁ + 1 - A) ^ n)) *
            (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) :=
          mul_le_mul_of_nonneg_left hG' (by positivity)

  rw [le_div_iff₀ hden]
  have hκpos : 0 < κ * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C) := by positivity
  have h2 : ‖gammaFactor R C s * Φ s‖ * (1 + |s.im|) ^ n *
      (κ * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) ≤
      (c₁ * (max K 1 * (σ₁ + 1 - A) ^ n) * 2 ^ n / κ * M) *
        (κ * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) := by
    have e : (c₁ * (max K 1 * (σ₁ + 1 - A) ^ n) * 2 ^ n / κ * M) *
        (κ * (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) =
        2 ^ n * (c₁ * (M * (max K 1 * (σ₁ + 1 - A) ^ n)) *
          (1 + |s.im|) ^ (N * Multiset.card R + N * Multiset.card C)) := by
      field_simp
    rw [e]
    calc _ = ‖gammaFactor R C s * Φ s‖ * (κ * (1 + |s.im|) ^
           (N * Multiset.card R + N * Multiset.card C)) *
          (1 + |s.im|) ^ n := by ring
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_right h2 hκpos

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

section packaging

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G]
      [NormedSpace ℝ G]

private def mkLin (f : E → G) (hadd : ∀ a a', f (a + a') = f a + f a')
    (hsmul : ∀ (r : ℝ) (a : E), f (r • a) = r • f a) :
    E →L[ℝ] G :=
  LinearMap.toContinuousLinearMap { toFun := f, map_add' := hadd, map_smul' := hsmul }

@[scoped simp] private theorem mkLin_apply (f : E → G) (hadd : ∀ a a', f (a + a') = f a + f a')
    (hsmul : ∀ (r : ℝ) (a : E), f (r • a) = r • f a) (a : E) : mkLin f hadd hsmul a = f a := by
  simp [mkLin]

private def mkBilin (b : E → F → G) (h₁ : ∀ a a' c, b (a + a') c = b a c + b a' c)
    (h₂ : ∀ (r : ℝ) (a : E) (c : F), b (r • a) c = r • b a c)
        (h₃ : ∀ a c c', b a (c + c') = b a c + b a c')
    (h₄ : ∀ (r : ℝ) (a : E) (c : F), b a (r • c) = r • b a c) : E →L[ℝ] F →L[ℝ] G :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => LinearMap.toContinuousLinearMap (LinearMap.mk₂ ℝ b h₁ h₂ h₃ h₄ a)
      map_add' := fun a a' => by ext c : 1; simp
      map_smul' := fun r a => by ext c : 1; simp }

@[scoped simp] private theorem mkBilin_apply (b : E → F → G)
    (h₁ : ∀ a a' c, b (a + a') c = b a c + b a' c)
    (h₂ : ∀ (r : ℝ) (a : E) (c : F), b (r • a) c = r • b a c)
        (h₃ : ∀ a c c', b a (c + c') = b a c + b a c')
    (h₄ : ∀ (r : ℝ) (a : E) (c : F), b a (r • c) = r • b a c) (a : E) (c : F) :
    mkBilin b h₁ h₂ h₃ h₄ a c = b a c := by
  simp [mkBilin]

end packaging

section constants

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G]

private theorem exists_leibniz {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] F →L[ℝ] G) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (f : (Fin 2 → Fin 2 → 𝕜) → E) (g : (Fin 2 → Fin 2 → 𝕜) → F)
        (s : Set (Fin 2 → Fin 2 → 𝕜)),
      ContDiffOn ℝ (⊤ : ℕ∞) f s → ContDiffOn ℝ (⊤ : ℕ∞) g s → UniqueDiffOn ℝ s → ∀ x ∈ s, ∀ n : ℕ,
        ‖iteratedFDerivWithin ℝ n (fun y => B (f y) (g y)) s x‖ ≤
          b * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
            ‖iteratedFDerivWithin ℝ (n - i) g s x‖ :=
  ⟨‖B‖, B.opNorm_nonneg, fun _ _ _ hf hg hs _ hx _ =>
    B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hs hx (mod_cast le_top)⟩

private theorem exists_comp_left (L : F →L[ℝ] G) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (f : (Fin 2 → Fin 2 → 𝕜) → F) (s : Set (Fin 2 → Fin 2 → 𝕜)), ContDiffOn ℝ
        (⊤ : ℕ∞) f s →
      UniqueDiffOn ℝ s → ∀ x ∈ s, ∀ n : ℕ,
        ‖iteratedFDerivWithin ℝ n (fun y => L (f y)) s x‖ ≤ b * ‖iteratedFDerivWithin ℝ n f s x‖ :=
  ⟨‖L‖, L.opNorm_nonneg, fun _ _ hf hs x hx _ =>
    L.norm_iteratedFDerivWithin_comp_left (hf x hx) hs hx (mod_cast le_top)⟩

end constants

private def invertibleCoords (𝕜 : Type) [RCLike 𝕜] : Set (Fin 2 → Fin 2 → 𝕜) :=
    {A | (Matrix.of A).det ≠ 0}

private theorem mem_invertibleCoords {p : Fin 2 → Fin 2 → 𝕜} : p ∈ invertibleCoords 𝕜 ↔
    (Matrix.of p).det ≠ 0 :=
  Iff.rfl

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

@[scoped simp] private theorem mulCoords_apply (a b : Fin 2 → Fin 2 → 𝕜) :
    mulCoords 𝕜 a b = Matrix.of.symm (Matrix.of a * Matrix.of b) := by
  simp [mulCoords, mulCoordsₗ]

private def invCoords (p : Fin 2 → Fin 2 → 𝕜) : Fin 2 → Fin 2 → 𝕜 := Matrix.of.symm
    ((Matrix.of p)⁻¹)

private theorem invCoords_apply (p : Fin 2 → Fin 2 → 𝕜) (i j : Fin 2) :
    invCoords p i j = ((Matrix.of p).det)⁻¹ * (Matrix.of p).adjugate i j := by
  simp [invCoords, Matrix.inv_def, Ring.inverse_eq_inv]

private theorem mulCoords_invCoords_self {p : Fin 2 → Fin 2 → 𝕜} (hp : p ∈ invertibleCoords 𝕜) :
    mulCoords 𝕜 (invCoords p) p = Matrix.of.symm 1 := by
  have h : IsUnit (Matrix.of p).det := isUnit_iff_ne_zero.2 hp
  simp [invCoords, Matrix.nonsing_inv_mul _ h, -Matrix.symm_of]

private theorem mulCoords_mulCoords_invCoords {p : Fin 2 → Fin 2 → 𝕜} (hp : p ∈ invertibleCoords 𝕜)
    (x : Fin 2 → Fin 2 → 𝕜) : mulCoords 𝕜 (mulCoords 𝕜 x p) (invCoords p) = x := by
  have h : IsUnit (Matrix.of p).det := isUnit_iff_ne_zero.2 hp
  simp [invCoords, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, -Matrix.symm_of]

private theorem mulCoords_self_mulCoords_invCoords {p : Fin 2 → Fin 2 → 𝕜}
    (hp : p ∈ invertibleCoords 𝕜)
    (x : Fin 2 → Fin 2 → 𝕜) : mulCoords 𝕜 p (mulCoords 𝕜 (invCoords p) x) = x := by
  have h : IsUnit (Matrix.of p).det := isUnit_iff_ne_zero.2 hp
  simp [invCoords, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, -Matrix.symm_of]

private theorem contDiffOn_det_inv :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : Fin 2 → Fin 2 → 𝕜 => ((Matrix.of p).det)⁻¹)
        (invertibleCoords 𝕜) := by
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun p : Fin 2 → Fin 2 → 𝕜 => (Matrix.of p).det := by
    simp only [Matrix.det_fin_two, Matrix.of_apply]
    fun_prop
  exact hdet.contDiffOn.inv fun p hp => hp

private theorem contDiffOn_invCoords : ContDiffOn ℝ (⊤ : ℕ∞) (invCoords (𝕜 := 𝕜))
    (invertibleCoords 𝕜) := by
  refine contDiffOn_pi' fun i => contDiffOn_pi' fun j => ?_
  simp only [invCoords_apply, Matrix.adjugate_fin_two, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | exact contDiffOn_det_inv.mul (by fun_prop)
    | exact (contDiffOn_det_inv.mul (by fun_prop)).neg

variable (𝕜) in

private def invQuad :=
  mkBilin (G := (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜))
    (fun a c : Fin 2 → Fin 2 → 𝕜 => -(((mulCoords 𝕜).flip c).comp (mulCoords 𝕜 a)))
    (fun a a' c => by ext w i j; simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]; try abel)
    (fun r a c => by ext w i j; simp [Matrix.mul_apply])
    (fun a c c' => by ext w i j; simp [Matrix.mul_apply]; try abel)
    (fun r a c => by ext w i j; simp [Matrix.mul_apply])

@[scoped simp] private theorem invQuad_apply (a c w : Fin 2 → Fin 2 → 𝕜) :
    invQuad 𝕜 a c w = -(mulCoords 𝕜 (mulCoords 𝕜 a w) c) := by
  simp [invQuad]

private theorem fderivWithin_invCoords {p : Fin 2 → Fin 2 → 𝕜} (hp : p ∈ invertibleCoords 𝕜) :
    fderivWithin ℝ (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p = invQuad 𝕜 (invCoords p)
        (invCoords p) := by
  set f' := fderivWithin ℝ (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p with hf'
  have hinv : HasFDerivWithinAt (invCoords (𝕜 := 𝕜)) f' (invertibleCoords 𝕜) p :=
    ((contDiffOn_invCoords.differentiableOn (by simp)) p hp).hasFDerivWithinAt
  have hprod := (mulCoords 𝕜).hasFDerivWithinAt_of_bilinear hinv
      (hasFDerivWithinAt_id p (invertibleCoords 𝕜))
  have hconst : HasFDerivWithinAt (fun q => mulCoords 𝕜 (invCoords q) q)
      (0 : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] (Fin 2 → Fin 2 → 𝕜)) (invertibleCoords 𝕜) p :=
    (hasFDerivWithinAt_const (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) 𝕜)) p
        (invertibleCoords 𝕜)).congr
      (fun q hq => mulCoords_invCoords_self hq) (mulCoords_invCoords_self hp)
  have hzero := (uniqueDiffOn_invertibleCoords p hp).eq hprod hconst
  ext w : 1
  have hw := congrArg (fun L => L w) hzero
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply,
    id, ContinuousLinearMap.zero_apply] at hw
  have hkey : mulCoords 𝕜 (f' w) p = -(mulCoords 𝕜 (invCoords p) w) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hw
  calc f' w = mulCoords 𝕜 (mulCoords 𝕜 (f' w) p) (invCoords p) :=
         (mulCoords_mulCoords_invCoords hp _).symm
    _ = invQuad 𝕜 (invCoords p) (invCoords p) w := by
        rw [hkey, invQuad_apply, map_neg, ContinuousLinearMap.neg_apply]

private theorem norm_iteratedFDerivWithin_invCoords_le (n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a ≤ n, ∀ p ∈ invertibleCoords 𝕜,
      ‖iteratedFDerivWithin ℝ a (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p‖ ≤ c * ‖invCoords p‖ ^
          (a + 1) := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun a ha p hp => ?_⟩
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    simp [norm_iteratedFDerivWithin_zero]
  | succ n ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    obtain ⟨b, hb0, hb⟩ := exists_leibniz (𝕜 := 𝕜) (invQuad 𝕜)
    refine ⟨max c (b * (c * c) * 2 ^ n), le_max_of_le_left hc0, fun a ha p hp => ?_⟩
    rcases Nat.lt_or_ge a (n + 1) with hlt | hge
    · exact (hc a (Nat.lt_succ_iff.1 hlt) p hp).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · obtain rfl : a = n + 1 := le_antisymm ha hge
      have hS : UniqueDiffOn ℝ (invertibleCoords 𝕜) := uniqueDiffOn_invertibleCoords
      rw [← norm_iteratedFDerivWithin_fderivWithin hS hp]
      have hcongr : Set.EqOn (fderivWithin ℝ (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜))
          (fun q => invQuad 𝕜 (invCoords q) (invCoords q)) (invertibleCoords 𝕜) :=
        fun q hq => fderivWithin_invCoords hq
      rw [iteratedFDerivWithin_congr hcongr hp n]
      refine (hb invCoords invCoords (invertibleCoords 𝕜) contDiffOn_invCoords contDiffOn_invCoords
          hS p hp n).trans ?_
      have hterm : ∀ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (invCoords (𝕜 := 𝕜))
              (invertibleCoords 𝕜) p‖ *
              ‖iteratedFDerivWithin ℝ (n - i) (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p‖
            ≤ (n.choose i : ℝ) * ((c * c) * ‖invCoords p‖ ^ (n + 1 + 1)) := by
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := hc i hi' p hp
        have h2 := hc (n - i) (Nat.sub_le n i) p hp
        calc (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (invCoords (𝕜 := 𝕜))
               (invertibleCoords 𝕜) p‖ *
                ‖iteratedFDerivWithin ℝ (n - i) (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p‖
            ≤ (n.choose i : ℝ) * (c * ‖invCoords p‖ ^ (i + 1)) *
                (c * ‖invCoords p‖ ^ (n - i + 1)) := by
              gcongr
          _ = (n.choose i : ℝ) * ((c * c) * ‖invCoords p‖ ^ (n + 1 + 1)) := by
              have hexp : n + 1 + 1 = i + 1 + (n - i + 1) := by omega
              rw [hexp]; ring
      calc _ ≤ b * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
             ((c * c) * ‖invCoords p‖ ^ (n + 1 + 1)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hb0
        _ = b * (c * c) * 2 ^ n * ‖invCoords p‖ ^ (n + 1 + 1) := by
            rw [← Finset.sum_mul]
            have h2 : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
              exact_mod_cast Nat.sum_range_choose n
            rw [h2]; ring
        _ ≤ max c (b * (c * c) * 2 ^ n) * ‖invCoords p‖ ^ (n + 1 + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

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

private def wordDeriv {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) 𝕜) :
    {j : ℕ} → (Fin j → ι) → ((Fin 2 → Fin 2 → 𝕜) → ℂ) → (Fin 2 → Fin 2 → 𝕜) → ℂ
  | 0, _, G => G
  | j + 1, I, G => wordDeriv E (fun i : Fin j => I i.succ) (rightDeriv (E (I 0)) G)

@[scoped simp] private theorem wordDeriv_zero {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (I : Fin 0 → ι)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) : wordDeriv E I G = G := rfl

@[scoped simp] private theorem wordDeriv_cons {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) 𝕜) {j : ℕ}
    (i : ι) (I : Fin j → ι)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) : wordDeriv E (Fin.cons i I) G = wordDeriv E I
        (rightDeriv (E i) G) := by
  simp [wordDeriv]

private def wordSum {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜) (a : ℕ)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ)
    (p : Fin 2 → Fin 2 → 𝕜) : ℝ :=
  ∑ j ∈ Finset.range (a + 1), ∑ I : Fin j → ι, ‖wordDeriv E I G p‖

private theorem wordSum_nonneg {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜) (a : ℕ)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) (p : Fin 2 → Fin 2 → 𝕜) : 0 ≤ wordSum E a G p :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem wordSum_mono {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜) {a b : ℕ}
    (hab : a ≤ b)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) (p : Fin 2 → Fin 2 → 𝕜) : wordSum E a G p ≤ wordSum E b G p :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    fun _ _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem wordSum_zero {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ)
    (p : Fin 2 → Fin 2 → 𝕜) : wordSum E 0 G p = ‖G p‖ := by
  simp [wordSum]

private theorem sum_pi_fin_succ {ι : Type} [Fintype ι] {j : ℕ} (g : (Fin (j + 1) → ι) → ℝ) :
    ∑ J : Fin (j + 1) → ι, g J = ∑ i : ι, ∑ I : Fin j → ι, g (Fin.cons i I) := by
  have h := (Fin.consEquiv fun _ : Fin (j + 1) => ι).sum_comp g
  rw [← h, Fintype.sum_prod_type]
  rfl

private theorem sum_wordSum_rightDeriv_le {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (n : ℕ)
    (G : (Fin 2 → Fin 2 → 𝕜) → ℂ) (p : Fin 2 → Fin 2 → 𝕜) :
    ∑ i, wordSum E n (rightDeriv (E i) G) p ≤ wordSum E (n + 1) G p := by
  have key : ∀ j : ℕ, ∑ i, ∑ I : Fin j → ι, ‖wordDeriv E I (rightDeriv (E i) G) p‖
      = ∑ J : Fin (j + 1) → ι, ‖wordDeriv E J G p‖ := by
    intro j
    rw [sum_pi_fin_succ]
    simp only [wordDeriv_cons]
  unfold wordSum
  calc ∑ i, ∑ j ∈ Finset.range (n + 1), ∑ I : Fin j → ι, ‖wordDeriv E I (rightDeriv (E i) G) p‖
      = ∑ j ∈ Finset.range (n + 1), ∑ J : Fin (j + 1) → ι, ‖wordDeriv E J G p‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => key j
    _ ≤ ∑ j ∈ Finset.range (n + 1 + 1), ∑ J : Fin j → ι, ‖wordDeriv E J G p‖ := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

private def coeffCLM (c : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) :=
  mkLin (G := (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) (fun m : Fin 2 → Fin 2 → 𝕜 => c.comp (mulCoords 𝕜 m))
    (fun m m' => by
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add])
    (fun r m => by
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul])

@[scoped simp] private theorem coeffCLM_apply (c : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ)
    (m v : Fin 2 → Fin 2 → 𝕜) :
    coeffCLM c m v = c (mulCoords 𝕜 m v) := by
  simp [coeffCLM]

variable (𝕜) in

private def pairing :=
  mkBilin (G := (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℂ)
    (fun (l : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) (z : ℂ) => l.smulRight z)
    (fun l l' z => by ext v; simp [add_smul])
    (fun r l z => by ext v; simp [mul_smul])
    (fun l z z' => by ext v; simp [smul_add])
    (fun r l z => by ext v; simp [mul_left_comm])

@[scoped simp] private theorem pairing_apply (l : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) (z : ℂ)
    (v : Fin 2 → Fin 2 → 𝕜) :
    pairing 𝕜 l z v = l v • z :=
  rfl

private theorem fderivWithin_eq_sum {ι : Type} [Fintype ι] (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (coord : ι → (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ)
    (hE : ∀ v : Fin 2 → Fin 2 → 𝕜, v = ∑ i, coord i v • Matrix.of.symm (E i))
    (F : (Fin 2 → Fin 2 → 𝕜) → ℂ) {p : Fin 2 → Fin 2 → 𝕜} (hp : p ∈ invertibleCoords 𝕜) :
    fderivWithin ℝ F (invertibleCoords 𝕜) p
      = ∑ i, pairing 𝕜 (coeffCLM (coord i) (invCoords p)) (rightDeriv (E i) F p) := by
  ext v
  have hv : v = mulCoords 𝕜 p (mulCoords 𝕜 (invCoords p) v) :=
      (mulCoords_self_mulCoords_invCoords hp v).symm
  have hw := hE (mulCoords 𝕜 (invCoords p) v)
  calc fderivWithin ℝ F (invertibleCoords 𝕜) p v
      = fderivWithin ℝ F (invertibleCoords 𝕜) p
          (mulCoords 𝕜 p (∑ i, coord i (mulCoords 𝕜 (invCoords p) v) • Matrix.of.symm (E i))) := by
        rw [← hw, ← hv]
    _ = ∑ i, coord i (mulCoords 𝕜 (invCoords p) v) • rightDeriv (E i) F p := by
        simp [map_sum, map_smul, rightDeriv, -Matrix.symm_of]
    _ = _ := by simp

private theorem contDiffOn_summand (c : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) (X : Matrix (Fin 2) (Fin 2) 𝕜)
    {F : (Fin 2 → Fin 2 → 𝕜) → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => pairing 𝕜 (coeffCLM c (invCoords q)) (rightDeriv X F q))
      (invertibleCoords 𝕜) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => coeffCLM c (invCoords q)) (invertibleCoords 𝕜) :=
    (coeffCLM c).contDiff.comp_contDiffOn contDiffOn_invCoords
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => pairing 𝕜 (coeffCLM c (invCoords q)))
      (invertibleCoords 𝕜) :=
    (pairing 𝕜).contDiff.comp_contDiffOn h1
  exact h2.clm_apply (contDiffOn_rightDeriv X hF)

private theorem norm_iteratedFDerivWithin_coeff_le (c : (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b ≤ n, ∀ p ∈ invertibleCoords 𝕜,
      ‖iteratedFDerivWithin ℝ b (fun q => coeffCLM c (invCoords q)) (invertibleCoords 𝕜) p‖
        ≤ K * max 1 ‖invCoords p‖ ^ (b + 1) := by
  obtain ⟨k, hk0, hk⟩ := norm_iteratedFDerivWithin_invCoords_le (𝕜 := 𝕜) n
  obtain ⟨l, hl0, hl⟩ := exists_comp_left (𝕜 := 𝕜) (coeffCLM c)
  refine ⟨l * k, by positivity, fun b hb p hp => ?_⟩
  calc ‖iteratedFDerivWithin ℝ b (fun q => coeffCLM c (invCoords q)) (invertibleCoords 𝕜) p‖
      ≤ l * ‖iteratedFDerivWithin ℝ b (invCoords (𝕜 := 𝕜)) (invertibleCoords 𝕜) p‖ :=
        hl invCoords (invertibleCoords 𝕜) contDiffOn_invCoords uniqueDiffOn_invertibleCoords p hp b
    _ ≤ l * (k * ‖invCoords p‖ ^ (b + 1)) := mul_le_mul_of_nonneg_left (hk b hb p hp) hl0
    _ ≤ l * (k * max 1 ‖invCoords p‖ ^ (b + 1)) := by
        gcongr
        exact le_max_right _ _
    _ = l * k * max 1 ‖invCoords p‖ ^ (b + 1) := by ring

private theorem norm_iteratedFDerivWithin_le_wordSum {ι : Type} [Fintype ι]
    (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (coord : ι → (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ)
    (hE : ∀ v : Fin 2 → Fin 2 → 𝕜, v = ∑ i, coord i v • Matrix.of.symm (E i)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ≤ n, ∀ F : (Fin 2 → Fin 2 → 𝕜) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F
        (invertibleCoords 𝕜) →
      ∀ p ∈ invertibleCoords 𝕜,
        ‖iteratedFDerivWithin ℝ a F (invertibleCoords 𝕜) p‖ ≤ C * max 1 ‖invCoords p‖ ^ a * wordSum
            E a F p := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun a ha F _ p _ => ?_⟩
    obtain rfl : a = 0 := Nat.le_zero.1 ha
    simp [norm_iteratedFDerivWithin_zero, wordSum_zero]
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨bP, hbP0, hbP⟩ := exists_leibniz (𝕜 := 𝕜) (pairing 𝕜)
    choose K hK0 hK using fun i => norm_iteratedFDerivWithin_coeff_le (coord i) n
    obtain ⟨KA, hKA0, hKi⟩ : ∃ KA : ℝ, 0 ≤ KA ∧ ∀ i, K i ≤ KA :=
      ⟨∑ i, K i, Finset.sum_nonneg fun i _ => hK0 i,
        fun i => Finset.single_le_sum (fun j _ => hK0 j) (Finset.mem_univ i)⟩
    refine ⟨max C (bP * 2 ^ n * KA * C), le_max_of_le_left hC0, fun a ha F hF p hp => ?_⟩
    have hm1 : (1 : ℝ) ≤ max 1 ‖invCoords p‖ := le_max_left _ _
    have hm0 : (0 : ℝ) ≤ max 1 ‖invCoords p‖ := zero_le_one.trans hm1
    rcases Nat.lt_or_ge a (n + 1) with hlt | hge
    · exact (hC a (Nat.lt_succ_iff.1 hlt) F hF p hp).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (pow_nonneg hm0 a))
          (wordSum_nonneg _ _ _ _))
    · obtain rfl : a = n + 1 := le_antisymm ha hge
      have hS : UniqueDiffOn ℝ (invertibleCoords 𝕜) := uniqueDiffOn_invertibleCoords
      rw [← norm_iteratedFDerivWithin_fderivWithin hS hp]
      have hcongr : Set.EqOn (fderivWithin ℝ F (invertibleCoords 𝕜))
          (∑ i, fun q => pairing 𝕜 (coeffCLM (coord i) (invCoords q)) (rightDeriv (E i) F q))
          (invertibleCoords 𝕜) := by
        intro q hq
        rw [fderivWithin_eq_sum E coord hE F hq, Finset.sum_apply]
      rw [iteratedFDerivWithin_congr hcongr hp n,
        iteratedFDerivWithin_sum_apply hS hp fun i _ =>
          ((contDiffOn_summand (coord i) (E i) hF) p hp).of_le (mod_cast le_top)]
      refine (norm_sum_le _ _).trans ?_
      have hletter : ∀ i ∈ (Finset.univ : Finset ι),
          ‖iteratedFDerivWithin ℝ n (fun q => pairing 𝕜 (coeffCLM (coord i) (invCoords q))
              (rightDeriv (E i) F q))
              (invertibleCoords 𝕜) p‖
            ≤ bP * 2 ^ n * KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n
                (rightDeriv (E i) F) p := by
        intro i _
        have hR : ContDiffOn ℝ (⊤ : ℕ∞) (rightDeriv (E i) F)
            (invertibleCoords 𝕜) := contDiffOn_rightDeriv (E i) hF
        have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => coeffCLM (coord i) (invCoords q))
            (invertibleCoords 𝕜) :=
          (coeffCLM (coord i)).contDiff.comp_contDiffOn contDiffOn_invCoords
        refine (hbP (fun q => coeffCLM (coord i) (invCoords q)) (rightDeriv (E i) F)
            (invertibleCoords 𝕜) hΨ hR hS
          p hp n).trans ?_
        have hterm : ∀ b ∈ Finset.range (n + 1),
            (n.choose b : ℝ) *
                ‖iteratedFDerivWithin ℝ b (fun q => coeffCLM (coord i) (invCoords q))
                    (invertibleCoords 𝕜) p‖ *
                ‖iteratedFDerivWithin ℝ (n - b) (rightDeriv (E i) F) (invertibleCoords 𝕜) p‖
              ≤ (n.choose b : ℝ) * (KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n
                  (rightDeriv (E i) F) p) := by
          intro b hb
          have hb' : b ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
          have h1 : ‖iteratedFDerivWithin ℝ b (fun q => coeffCLM (coord i) (invCoords q))
              (invertibleCoords 𝕜) p‖
              ≤ KA * max 1 ‖invCoords p‖ ^ (b + 1) :=
            (hK i b hb' p hp).trans (mul_le_mul_of_nonneg_right (hKi i) (pow_nonneg hm0 _))
          have h2 : ‖iteratedFDerivWithin ℝ (n - b) (rightDeriv (E i) F) (invertibleCoords 𝕜) p‖
              ≤ C * max 1 ‖invCoords p‖ ^ (n - b) * wordSum E n (rightDeriv (E i) F) p :=
            (hC (n - b) (Nat.sub_le n b) _ hR p hp).trans
              (mul_le_mul_of_nonneg_left (wordSum_mono E (Nat.sub_le n b) _ _)
                (mul_nonneg hC0 (pow_nonneg hm0 _)))
          calc _ ≤ (n.choose b : ℝ) * (KA * max 1 ‖invCoords p‖ ^ (b + 1)) *
                  (C * max 1 ‖invCoords p‖ ^ (n - b) * wordSum E n (rightDeriv (E i) F) p) := by
                gcongr
            _ = (n.choose b : ℝ) *
                  (KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n
                      (rightDeriv (E i) F) p) := by
                have hexp : n + 1 = b + 1 + (n - b) := by omega
                rw [hexp]; ring
        calc _ ≤ bP * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) *
                (KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n (rightDeriv (E i) F) p) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hbP0
          _ = bP * 2 ^ n * KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n
              (rightDeriv (E i) F) p := by
              rw [← Finset.sum_mul]
              have h2 : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ)) = 2 ^ n := by
                exact_mod_cast Nat.sum_range_choose n
              rw [h2]; ring
      calc _ ≤ ∑ i, bP * 2 ^ n * KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E n
             (rightDeriv (E i) F) p :=
            Finset.sum_le_sum hletter
        _ = bP * 2 ^ n * KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * ∑ i, wordSum E n
            (rightDeriv (E i) F) p := by
            rw [Finset.mul_sum]
        _ ≤ bP * 2 ^ n * KA * C * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E (n + 1) F p :=
            mul_le_mul_of_nonneg_left (sum_wordSum_rightDeriv_le E n F p) (by positivity)
        _ = (bP * 2 ^ n * KA * C) * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E (n + 1) F p := by ring
        _ ≤ max C (bP * 2 ^ n * KA * C) * max 1 ‖invCoords p‖ ^ (n + 1) * wordSum E (n + 1) F p :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
                (pow_nonneg hm0 _))
              (wordSum_nonneg _ _ _ _)

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
  show (Matrix.of (Matrix.of.symm (!![t, 0; 0, 1] * k))).det ≠ 0
  rw [Equiv.apply_symm_apply, Matrix.det_mul, Matrix.det_fin_two_of]
  simpa using mul_ne_zero ht (det_ne_zero_of_mem_unitaryGroup hk)

private theorem invCoords_diagOneMulCoords (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜)
    (hk : k ∈ Matrix.unitaryGroup (Fin 2) 𝕜)
    (ht : t ≠ 0) : invCoords (diagOneMulCoords t k) = Matrix.of.symm
        (star k * !![t⁻¹, 0; 0, 1]) := by
  have hks : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  have hd : !![t⁻¹, 0; 0, 1] * !![t, 0; 0, (1 : 𝕜)] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [inv_mul_cancel₀ ht]
  unfold invCoords diagOneMulCoords
  rw [Equiv.apply_symm_apply]
  congr 1
  apply Matrix.inv_eq_left_inv
  calc star k * !![t⁻¹, 0; 0, 1] * (!![t, 0; 0, 1] * k)
      = star k * (!![t⁻¹, 0; 0, 1] * !![t, 0; 0, 1]) * k := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hd, Matrix.mul_one, hks]

private theorem norm_invCoords_diagOneMulCoords_le (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜)
    (hk : k ∈ Matrix.unitaryGroup (Fin 2) 𝕜) (ht : t ≠ 0) (ht1 : ‖t‖ ≤ 1) :
    ‖invCoords (diagOneMulCoords t k)‖ ≤ ‖t‖⁻¹ := by
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hinv0 : 0 ≤ ‖t‖⁻¹ := inv_nonneg.2 hpos.le
  have h1inv : 1 ≤ ‖t‖⁻¹ := (one_le_inv₀ hpos).2 ht1
  have hentry : ∀ i j, ‖k i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hk i j
  rw [invCoords_diagOneMulCoords t k hk ht]
  rw [pi_norm_le_iff_of_nonneg hinv0]
  intro i
  rw [pi_norm_le_iff_of_nonneg hinv0]
  intro j
  fin_cases j
  · simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    simp [norm_mul, norm_inv]
    calc ‖k 0 i‖ * ‖t‖⁻¹ ≤ 1 * ‖t‖⁻¹ := mul_le_mul_of_nonneg_right (hentry 0 i) hinv0
      _ = ‖t‖⁻¹ := one_mul _
  · simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    simp
    exact (hentry 1 i).trans h1inv

private theorem norm_iteratedFDerivWithin_diagOneMulCoords_le {ι : Type} [Fintype ι]
    (E : ι → Matrix (Fin 2) (Fin 2) 𝕜)
    (coord : ι → (Fin 2 → Fin 2 → 𝕜) →L[ℝ] ℝ)
    (hE : ∀ v : Fin 2 → Fin 2 → 𝕜, v = ∑ i, coord i v • Matrix.of.symm (E i)) (M : ℕ) :
    ∃ C : ℝ, ∀ F : (Fin 2 → Fin 2 → 𝕜) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords 𝕜) →
      ∀ (t : 𝕜) (k : Matrix (Fin 2) (Fin 2) 𝕜), k ∈ Matrix.unitaryGroup (Fin 2) 𝕜 → t ≠ 0 →
          ‖t‖ ≤ 1 →
        ‖iteratedFDerivWithin ℝ M F (invertibleCoords 𝕜) (diagOneMulCoords t k)‖
          ≤ C * ‖t‖ ^ (-(M : ℝ)) * wordSum E M F (diagOneMulCoords t k) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDerivWithin_le_wordSum E coord hE M
  refine ⟨C, fun F hF t k hk ht ht1 => ?_⟩
  have hp := diagOneMulCoords_mem t k hk ht
  have hpos : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hmax : max 1 ‖invCoords (diagOneMulCoords t k)‖ ≤ ‖t‖⁻¹ :=
    max_le ((one_le_inv₀ hpos).2 ht1) (norm_invCoords_diagOneMulCoords_le t k hk ht ht1)
  have hpow : max 1 ‖invCoords (diagOneMulCoords t k)‖ ^ M ≤ ‖t‖ ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (le_max_of_le_left zero_le_one) hmax M
  calc _ ≤ C * max 1 ‖invCoords (diagOneMulCoords t k)‖ ^ M * wordSum E M F
         (diagOneMulCoords t k) :=
        hC M le_rfl F hF _ hp
    _ ≤ C * ‖t‖ ^ (-(M : ℝ)) * wordSum E M F (diagOneMulCoords t k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) (wordSum_nonneg _ _ _ _)

private def lettersR (ij : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single ij.1 ij.2 1

private def coordR (ij : Fin 2 × Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj ij.2 : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj ij.1 : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))

private theorem coordR_spec (v : Fin 2 → Fin 2 → ℝ) : v = ∑ ij, coordR ij v • Matrix.of.symm
    (lettersR ij) := by
  ext a b
  simp [coordR, lettersR, Fintype.sum_prod_type, Finset.sum_apply]
  fin_cases a <;> fin_cases b <;> simp

private def lettersC (x : Fin 2 × Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single x.2.1 x.2.2 (if x.1 = 0 then 1 else Complex.I)

private def coordC (x : Fin 2 × Fin 2 × Fin 2) : (Fin 2 → Fin 2 → ℂ) →L[ℝ] ℝ :=
  (if x.1 = 0 then Complex.reCLM else Complex.imCLM).comp
    ((ContinuousLinearMap.proj x.2.2 : (Fin 2 → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj x.2.1 : (Fin 2 → Fin 2 → ℂ) →L[ℝ] (Fin 2 → ℂ)))

private theorem coordC_spec (v : Fin 2 → Fin 2 → ℂ) : v = ∑ x, coordC x v • Matrix.of.symm
    (lettersC x) := by
  ext a b
  simp [coordC, lettersC, Fintype.sum_prod_type, Finset.sum_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

private theorem norm_iteratedFDerivWithin_diagOneMulCoords_le_real (M : ℕ) :
    ∃ C : ℝ, ∀ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords ℝ) →
      ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), k ∈ Matrix.orthogonalGroup (Fin 2) ℝ →
          y ≠ 0 → |y| ≤ 1 →
        ‖iteratedFDerivWithin ℝ M F (invertibleCoords ℝ) (diagOneMulCoords y k)‖
          ≤ C * |y| ^ (-(M : ℝ)) * wordSum lettersR M F (diagOneMulCoords y k) := by
  obtain ⟨C, hC⟩ := norm_iteratedFDerivWithin_diagOneMulCoords_le lettersR coordR coordR_spec M
  refine ⟨C, fun F hF y k hk hy hy1 => ?_⟩
  have hk' : k ∈ Matrix.unitaryGroup (Fin 2) ℝ := hk
  simpa [Real.norm_eq_abs] using hC F hF y k hk' hy (by simpa [Real.norm_eq_abs] using hy1)

private theorem norm_iteratedFDerivWithin_diagOneMulCoords_le_complex (M : ℕ) :
    ∃ C : ℝ, ∀ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (invertibleCoords ℂ) →
      ∀ (z : ℂ) (k : Matrix (Fin 2) (Fin 2) ℂ), k ∈ Matrix.unitaryGroup (Fin 2) ℂ → z ≠ 0 →
          ‖z‖ ≤ 1 →
        ‖iteratedFDerivWithin ℝ M F (invertibleCoords ℂ) (diagOneMulCoords z k)‖
          ≤ C * ‖z‖ ^ (-(M : ℝ)) * wordSum lettersC M F (diagOneMulCoords z k) :=
  norm_iteratedFDerivWithin_diagOneMulCoords_le lettersC coordC coordC_spec M

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

private theorem isK_iff' {k : Matrix (Fin 2) (Fin 2) ℝ} : ArchR.IsK k ↔ kᵀ * k = 1 := by
  unfold ArchR.IsK
  exact Matrix.mem_orthogonalGroup_iff' (n := Fin 2) (R := ℝ)

private theorem isK_mul_transpose {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k) : k * kᵀ = 1 := isK_iff.1 hk

private theorem isK_transpose_mul {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k) : kᵀ * k = 1 := isK_iff'.1 hk

private theorem isK_transpose {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : ArchR.IsK kᵀ := by
  rw [isK_iff, Matrix.transpose_transpose]
  exact isK_transpose_mul hk

private theorem isK_one : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [isK_iff, Matrix.transpose_one, Matrix.mul_one]

private theorem isK_mul {k k' : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (hk' : ArchR.IsK k') :
    ArchR.IsK (k * k') := by
  rw [isK_iff] at hk hk' ⊢
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k', hk', Matrix.one_mul, hk]

private theorem isK_inv_eq_transpose {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : k⁻¹ = kᵀ :=
  Matrix.inv_eq_right_inv (isK_mul_transpose hk)

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

private theorem isK_col_sq {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (j : Fin 2) :
    k 0 j ^ 2 + k 1 j ^ 2 = 1 := by
  have h := congrFun (congrFun (isK_transpose_mul hk) j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  simpa [sq] using h

private theorem isK_row_orth {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) :
    k 0 0 * k 1 0 + k 0 1 * k 1 1 = 0 := by
  have h := congrFun (congrFun (isK_mul_transpose hk) 0) 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at h
  rw [Matrix.one_apply_ne (by decide)] at h
  exact h

private theorem isK_abs_entry_le_one {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k)
    (i j : Fin 2) :
    |k i j| ≤ 1 := by
  have h := isK_row_sq hk i
  revert j
  rw [Fin.forall_fin_two]
  exact ⟨(sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (k i 1)]),
    (sq_le_one_iff_abs_le_one _).1 (by nlinarith [sq_nonneg (k i 0)])⟩

private theorem isK_norm_coords_le_one {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) :
    ‖(Matrix.of.symm k : Fin 2 → Fin 2 → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  rw [Matrix.of_symm_apply, Real.norm_eq_abs]
  exact isK_abs_entry_le_one hk i j

private theorem det_diagOne (y : ℝ) : (ArchR.diagOne y).det = y := by
  simp [ArchR.diagOne, Matrix.det_fin_two_of]

private theorem det_unip (x : ℝ) : (ArchR.unip x).det = 1 := by
  simp [ArchR.unip, Matrix.det_fin_two_of]

private theorem det_weyl : (ArchR.weyl).det = 1 := by
  simp [ArchR.weyl, Matrix.det_fin_two_of]

private theorem diagOne_one : ArchR.diagOne (1 : ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne]

private theorem diagOne_mul_diagOne (y t : ℝ) : ArchR.diagOne y * ArchR.diagOne t = ArchR.diagOne
    (y * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagOne_mul_unip (y x : ℝ) : ArchR.diagOne y * ArchR.unip x = ArchR.unip
    (y * x) * ArchR.diagOne y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, ArchR.unip, Matrix.mul_apply,
      Fin.sum_univ_two]

private theorem diagOne_neg (y : ℝ) : ArchR.diagOne (-y) = ArchR.diagOne y * ArchR.diagOne
    (-1) := by
  rw [diagOne_mul_diagOne, mul_neg_one]

private theorem isK_diagOne_neg_one : ArchR.IsK (ArchR.diagOne (-1 : ℝ)) := by
  rw [isK_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

private theorem isK_weyl : ArchR.IsK ArchR.weyl := by
  rw [isK_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.weyl, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

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

private theorem rowNorm_nonneg (g : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ rowNorm g := Real.sqrt_nonneg _

private theorem rowNorm_sq (g : Matrix (Fin 2) (Fin 2) ℝ) : rowNorm g ^ 2 = rowSq g :=
  Real.sq_sqrt (rowSq_nonneg g)

private theorem abs_rowNorm (g : Matrix (Fin 2) (Fin 2) ℝ) : |rowNorm g| = rowNorm g :=
    abs_of_nonneg (rowNorm_nonneg g)

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
    simp [rot, rowSq, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;> ring

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

private theorem det_rot (g : Matrix (Fin 2) (Fin 2) ℝ) : (rot g).det = rowSq g := by
  simp [rot, rowSq, Matrix.det_fin_two_of]
  ring

private theorem abs_iwT_mul_rowSq {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0) : |iwT g| * rowSq g = |g.det| := by
  unfold iwT
  rw [abs_div, abs_of_pos (rowSq_pos hg), div_mul_cancel₀ _ (rowSq_pos hg).ne']

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

private theorem LeftLaws.apply_eq {P : RealArchParam} {G : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hG : LeftLaws P G)
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) :
    G g = ArchR.psi (iwX g) *
      (ArchR.centralChar P (rowNorm g) * ((|rowNorm g| : ℝ) : ℂ)) * G
          (ArchR.diagOne (iwT g) * kPart g) := by
  have h := hG.diagOne_mul hg 1
  rwa [diagOne_one, Matrix.one_mul, one_mul, one_mul] at h

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
    derivW X W g = rightDeriv X (ArchR.asPi W) (Matrix.of.symm g) := if_pos hg

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
  rw [← happ, hfun, fderiv_const_smul hF c, ContinuousLinearMap.smul_apply, smul_eq_mul]

private def leftMul (n : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ]
    (Fin 2 → Fin 2 → ℝ) :=
  mulCoords ℝ (Matrix.of.symm n)

@[scoped simp] private theorem leftMul_apply (n : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Fin 2 → Fin 2 → ℝ) :
    leftMul n q = Matrix.of.symm (n * Matrix.of q) := by
  simp [leftMul, -Matrix.symm_of]

private theorem leftMul_of_symm (n g : Matrix (Fin 2) (Fin 2) ℝ) : leftMul n
    (Matrix.of.symm g) = Matrix.of.symm (n * g) := by
  simp [-Matrix.symm_of]

private theorem leftMul_smul_one (z : ℝ) (q : Fin 2 → Fin 2 → ℝ) : leftMul
    (z • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q = z • q := by
  rw [leftMul_apply, Matrix.smul_mul, Matrix.one_mul]
  rfl

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

private theorem derivW_reduce {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) (X : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ)
        {b : ℝ}
    (hb : b ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    derivW X W (ArchR.unip x * (b • M)) =
      ArchR.psi x * (ArchR.centralChar P b * ((|b| : ℝ) : ℂ)) * derivW X W M := by
  rw [derivW_unip_law hL.unip hWs, derivW_central_law hL.central hWs X b M hb]
  ring

private theorem leftLaws_derivW {P : RealArchParam} {W : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hL : LeftLaws P W)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    LeftLaws P (derivW X W) :=
  ⟨derivW_unip_law hL.unip hWs X, fun z g hz => derivW_central_law hL.central hWs X z g hz⟩

private theorem rightDeriv_add (X Y : Matrix (Fin 2) (Fin 2) ℝ) (F : (Fin 2 → Fin 2 → ℝ) → ℂ)
    (p : Fin 2 → Fin 2 → ℝ) :
    rightDeriv (X + Y) F p = rightDeriv X F p + rightDeriv Y F p := by
  unfold rightDeriv
  rw [Matrix.mul_add]
  rw [show Matrix.of.symm (Matrix.of p * X + Matrix.of p * Y) =
      Matrix.of.symm (Matrix.of p * X) + Matrix.of.symm (Matrix.of p * Y) from rfl]
  exact map_add _ _ _

private theorem rightDeriv_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) (F : (Fin 2 → Fin 2 → ℝ) → ℂ)
    (p : Fin 2 → Fin 2 → ℝ) : rightDeriv (c • X) F p = (c : ℂ) * rightDeriv X F p := by
  unfold rightDeriv
  rw [Matrix.mul_smul]
  rw [show Matrix.of.symm (c • (Matrix.of p * X)) = c • Matrix.of.symm (Matrix.of p * X) from rfl]
  rw [map_smul, Complex.real_smul]

private theorem derivW_add (X Y : Matrix (Fin 2) (Fin 2) ℝ) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    derivW (X + Y) W g = derivW X W g + derivW Y W g := by
  by_cases hg : g.det ≠ 0
  · rw [derivW_of_det_ne_zero _ W hg, derivW_of_det_ne_zero _ W hg, derivW_of_det_ne_zero _ W hg,
      rightDeriv_add]
  · rw [not_ne_iff] at hg
    simp [derivW_of_det_eq_zero _ W hg]

private theorem derivW_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℝ) : derivW (c • X) W g = (c : ℂ) * derivW X W g := by
  by_cases hg : g.det ≠ 0
  · rw [derivW_of_det_ne_zero _ W hg, derivW_of_det_ne_zero _ W hg, rightDeriv_smul]
  · rw [not_ne_iff] at hg
    simp [derivW_of_det_eq_zero _ W hg]

private theorem derivW_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (X : ι → Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    derivW (∑ i ∈ s, c i • X i) W g = ∑ i ∈ s, (c i : ℂ) * derivW (X i) W g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    by_cases hg : g.det ≠ 0
    · rw [derivW_of_det_ne_zero _ W hg]
      unfold rightDeriv
      rw [Matrix.mul_zero]
      exact map_zero _
    · rw [not_ne_iff] at hg
      exact derivW_of_det_eq_zero _ W hg
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, derivW_add, derivW_smul, ih]

private theorem fderiv_asPi_apply_eq_derivW (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0) (v : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (ArchR.asPi W) (Matrix.of.symm g) v = derivW (g⁻¹ * Matrix.of v) W g := by
  rw [derivW_eq_fderiv _ W hg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hg),
      Matrix.one_mul]
  rfl

private def unitMat (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single i j (1 : ℝ)

private theorem matrix_eq_sum_unitMat (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    Y = ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), Y ij.1 ij.2 • unitMat ij.1 ij.2 := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [unitMat, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem derivW_eq_sum_units (Y : Matrix (Fin 2) (Fin 2) ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    derivW Y W g =
      ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), (Y ij.1 ij.2 : ℂ) * derivW
          (unitMat ij.1 ij.2) W g := by
  conv_lhs => rw [matrix_eq_sum_unitMat Y]
  exact derivW_sum _ _ _ W g

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

private theorem det_diagOne_mul {k : Matrix (Fin 2) (Fin 2) ℝ} (y : ℝ) :
    (ArchR.diagOne y * k).det = y * k.det := by
  rw [Matrix.det_mul, det_diagOne]

private theorem transpose_mul_unitMat_mul (k : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    (kᵀ * unitMat 0 0 * k) i j = k 0 i * k 0 j := by
  simp [unitMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.transpose_apply]

private theorem transpose_mul_unitMat_mul_eq_sum (k : Matrix (Fin 2) (Fin 2) ℝ) :
    kᵀ * unitMat 0 0 * k =
      ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), (k 0 ij.1 * k 0 ij.2) • unitMat ij.1 ij.2 := by
  conv_lhs => rw [matrix_eq_sum_unitMat (kᵀ * unitMat 0 0 * k)]
  simp only [transpose_mul_unitMat_mul]

private theorem inv_mul_unitMat_mul {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) {y : ℝ}
    (hy : y ≠ 0) :
    (ArchR.diagOne y * k)⁻¹ * (unitMat 0 0 * k) = y⁻¹ • (kᵀ * unitMat 0 0 * k) := by
  have hdk : IsUnit k.det := (isK_det_ne_zero hk).isUnit
  have hdy : IsUnit (ArchR.diagOne y).det := by rw [det_diagOne]; exact hy.isUnit
  rw [Matrix.mul_inv_rev, isK_inv_eq_transpose hk]
  have hinv : (ArchR.diagOne y)⁻¹ = ArchR.diagOne y⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [diagOne_mul_diagOne, inv_mul_cancel₀ hy, diagOne_one]
  have hE : ArchR.diagOne y⁻¹ * unitMat 0 0 = y⁻¹ • unitMat 0 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, unitMat, Matrix.single, Matrix.mul_apply]
  rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (ArchR.diagOne y⁻¹), hE, Matrix.smul_mul,
      Matrix.mul_smul,
    Matrix.mul_assoc]

private theorem hasDerivAt_orbit (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWs : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet)
    {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => W (ArchR.diagOne t * k))
      ((y⁻¹ : ℂ) * ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
        ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * derivW (unitMat ij.1 ij.2) W
            (ArchR.diagOne y * k)) y := by
  have hdet : (ArchR.diagOne 0 * k + y • (unitMat 0 0 * k)).det ≠ 0 := by
    rw [← diagOne_mul_eq_line, det_diagOne_mul]
    exact mul_ne_zero hy (isK_det_ne_zero hk)
  have h := hasDerivAt_asPi_line W hWs (ArchR.diagOne 0 * k) (unitMat 0 0 * k) hdet
  have hfun : (fun τ : ℝ => W (ArchR.diagOne 0 * k + τ • (unitMat 0 0 * k))) = fun t => W
      (ArchR.diagOne t * k) := by
    funext τ
    rw [← diagOne_mul_eq_line]
  rw [hfun, ← diagOne_mul_eq_line, inv_mul_unitMat_mul hk hy, derivW_smul,
      transpose_mul_unitMat_mul_eq_sum,
    derivW_sum] at h
  simpa using h

private theorem abs_coeff_le_one {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k)
    (i j : Fin 2) : |k 0 i * k 0 j| ≤ 1 := by
  rw [abs_mul]
  calc |k 0 i| * |k 0 j| ≤ 1 * 1 :=
        mul_le_mul (isK_abs_entry_le_one hk 0 i) (isK_abs_entry_le_one hk 0 j)
            (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem orbit_neg (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ)
    (y : ℝ) :
    W (ArchR.diagOne (-y) * k) = W (ArchR.diagOne y * (ArchR.diagOne (-1) * k)) := by
  rw [diagOne_neg, Matrix.mul_assoc]

private theorem isK_diagOne_neg_one_mul {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) :
    ArchR.IsK (ArchR.diagOne (-1) * k) := isK_mul isK_diagOne_neg_one hk

private theorem isK_weyl_mul {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : ArchR.IsK
    (ArchR.weyl * k) :=
  isK_mul isK_weyl hk

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

private theorem env_of_le {σ N y : ℝ} (h : |y| ≤ 1) : env σ N y = |y| ^ (-σ) := if_pos h

private theorem env_of_lt {σ N y : ℝ} (h : 1 < |y|) : env σ N y = |y| ^ (-N) := if_neg (not_le.2 h)

private theorem env_nonneg (σ N y : ℝ) : 0 ≤ env σ N y := by
  unfold env
  split_ifs <;> exact Real.rpow_nonneg (abs_nonneg y) _

private theorem one_le_env_of_le {σ N y : ℝ} (hσ : 0 ≤ σ) (hy : y ≠ 0)
    (h : |y| ≤ 1) : 1 ≤ env σ N y := by
  rw [env_of_le h]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.2 hy) h (by linarith)

private theorem env_le_one_of_lt {σ N y : ℝ} (hN : 0 ≤ N) (h : 1 < |y|) : env σ N y ≤ 1 := by
  rw [env_of_lt h]
  exact Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)

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

private theorem exists_orbitEnvelope {P : RealArchParam} (d : ArchDatumR P) (j N : ℕ) :
    ∃ C σ : ℝ, 0 ≤ C ∧ 0 ≤ σ ∧ ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi d.W) ArchR.glSet
          (ArchR.diagOneMulCoords y k)‖ ≤ C * env σ N y := by
  obtain ⟨Ct, ht⟩ := d.decay_top j N
  obtain ⟨Cz, σ, hz⟩ := d.decay_zero j
  refine ⟨max (max Ct Cz) 0, max σ 0, le_max_right _ _, le_max_right _ _, fun y k hk hy => ?_⟩
  calc ‖iteratedFDerivWithin ℝ j (ArchR.asPi d.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ max Ct Cz * env σ N y := orbitEnvelope_of ht hz hk hy
    _ ≤ max (max Ct Cz) 0 * env (max σ 0) N y :=
        mul_le_mul (le_max_left _ _) (env_mono hy (le_max_left _ _) le_rfl) (env_nonneg _ _ _)
            (le_max_right _ _)

private theorem norm_diagOneMulCoords_le {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (y : ℝ) :
    ‖ArchR.diagOneMulCoords y k‖ ≤ max 1 |y| := by
  have h0 : (0 : ℝ) ≤ max 1 |y| := le_trans zero_le_one (le_max_left _ _)
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_diagOne_mul_le hk y i j

private theorem diagOneMulCoords_mem {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) {y : ℝ}
    (hy : y ≠ 0) :
    ArchR.diagOneMulCoords y k ∈ ArchR.glSet := by
  show (Matrix.of (Matrix.of.symm (ArchR.diagOne y * k))).det ≠ 0
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
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
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
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
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
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne y * defo g X τ))).det ≠ 0
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
  ·
    obtain ⟨δ₁, hδ₁, hη⟩ := Metric.tendsto_nhds_nhds.1 hmod ε hε
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

section SpanParts
set_option autoImplicit false

open MeasureTheory Set Filter Topology

noncomputable section

namespace ArchWhittakerGrowth

private def signFactor (a : ZMod 2) (y : ℝ) : ℂ := if a = 0 then 1 else ((SignType.sign y : ℝ) : ℂ)

private def kernel (a : ZMod 2) (w : ℂ) (y : ℝ) : ℂ := signFactor a y * ((|y| : ℝ) : ℂ) ^ (w - 1)

private theorem signFactor_of_pos (a : ZMod 2) {y : ℝ} (hy : 0 < y) : signFactor a y = 1 := by
  unfold signFactor
  split_ifs <;> simp [sign_pos hy]

private theorem signFactor_of_neg (a : ZMod 2) {y : ℝ}
    (hy : y < 0) : signFactor a y = if a = 0 then 1 else -1 := by
  unfold signFactor
  split_ifs <;> simp [sign_neg hy]

private theorem signFactor_neg (a : ZMod 2) {y : ℝ} (hy : 0 < y) :
    signFactor a (-y) = (if a = 0 then 1 else -1) * signFactor a y := by
  rw [signFactor_of_neg a (neg_neg_of_pos hy), signFactor_of_pos a hy, mul_one]

private theorem kernel_of_pos (a : ZMod 2) (w : ℂ) {y : ℝ} (hy : 0 < y) : kernel a w y = (y : ℂ) ^
    (w - 1) := by
  rw [kernel, signFactor_of_pos a hy, one_mul, abs_of_pos hy]

private theorem kernel_neg (a : ZMod 2) (w : ℂ) {y : ℝ} (hy : 0 < y) :
    kernel a w (-y) = (if a = 0 then 1 else -1) * (y : ℂ) ^ (w - 1) := by
  rw [kernel, signFactor_neg a hy, signFactor_of_pos a hy, mul_one, abs_neg, abs_of_pos hy]

private theorem norm_signFactor_le (a : ZMod 2) (y : ℝ) : ‖signFactor a y‖ ≤ 1 := by
  unfold signFactor
  split_ifs
  · simp
  · generalize SignType.sign y = σ
    cases σ <;> simp

private theorem norm_kernel_le (a : ZMod 2) (w : ℂ) {y : ℝ} (hy : y ≠ 0) : ‖kernel a w y‖ ≤ |y| ^
    (w.re - 1) := by
  rw [kernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
  simp only [Complex.sub_re, Complex.one_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (abs_nonneg _) _) (norm_signFactor_le a y)

private theorem norm_abs_cpow (w : ℂ) (y : ℝ) (hy : y ≠ 0) : ‖((|y| : ℝ) : ℂ) ^ w‖ = |y| ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy) w

private theorem integral_Ioi_deriv_eq_zero {F F' : ℝ → ℂ}
    (hF : ∀ y : ℝ, 0 < y → HasDerivAt F (F' y) y)
    (hint : IntegrableOn F' (Ioi 0)) (h0 : Tendsto F (𝓝[>] 0) (𝓝 0))
        (htop : Tendsto F atTop (𝓝 0)) :
    ∫ y in Ioi (0 : ℝ), F' y = 0 := by
  set s : ℕ → Set ℝ := fun n => Ioi (1 / ((n : ℝ) + 1)) with hs
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hmono : Monotone s := by
    intro m n hmn
    apply Ioi_subset_Ioi
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hU : (⋃ n, s n) = Ioi 0 := by
    ext y
    simp only [mem_iUnion, hs, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact (hpos n).trans hn
    · intro hy
      exact exists_nat_one_div_lt hy
  have hint' : IntegrableOn F' (⋃ n, s n) := by
    rw [hU]
    exact hint
  have h1 : Tendsto (fun n => ∫ y in s n, F' y) atTop (𝓝 (∫ y in Ioi (0 : ℝ), F' y)) := by
    have h := tendsto_setIntegral_of_monotone (fun n => (measurableSet_Ioi : MeasurableSet (s n)))
        hmono hint'
    rwa [hU] at h
  have h2 : ∀ n : ℕ, ∫ y in s n, F' y = 0 - F (1 / ((n : ℝ) + 1)) := fun n =>
    integral_Ioi_of_hasDerivAt_of_tendsto (hF _ (hpos n)).continuousAt.continuousWithinAt
      (fun y hy => hF y ((hpos n).trans hy)) (hint.mono_set (Ioi_subset_Ioi (hpos n).le)) htop
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hpos⟩
  have h3 : Tendsto (fun n : ℕ => (0 : ℂ) - F (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (0 : ℂ) - F (1 / ((n : ℝ) + 1))) atTop (𝓝 ((0 : ℂ) - 0)) :=
      (tendsto_const_nhds (x := (0 : ℂ))).sub (h0.comp hseq)
    rwa [sub_zero] at h
  have h4 : Tendsto (fun n => ∫ y in s n, F' y) atTop (𝓝 0) := by
    simp_rw [h2]
    exact h3
  exact tendsto_nhds_unique h1 h4

private theorem parts_Ioi {f f' g : ℝ → ℂ} (hf : ∀ y : ℝ, 0 < y → HasDerivAt f (f' y) y)
    (hg : ∀ y : ℝ, 0 < y → (y : ℂ) * f' y = g y) {w : ℂ} (hw : w ≠ 0)
    (hfi : IntegrableOn (fun y : ℝ => f y * (y : ℂ) ^ (w - 1)) (Ioi 0))
    (hgi : IntegrableOn (fun y : ℝ => g y * (y : ℂ) ^ (w - 1)) (Ioi 0))
    (h0 : Tendsto (fun y : ℝ => f y * (y : ℂ) ^ w) (𝓝[>] 0) (𝓝 0))
    (htop : Tendsto (fun y : ℝ => f y * (y : ℂ) ^ w) atTop (𝓝 0)) :
    w * ∫ y in Ioi (0 : ℝ), f y * (y : ℂ) ^ (w - 1) = -∫ y in Ioi (0 : ℝ), g y * (y : ℂ) ^
        (w - 1) := by
  have hderiv : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => f y * (y : ℂ) ^ w)
        (g y * (y : ℂ) ^ (w - 1) + w * (f y * (y : ℂ) ^ (w - 1))) y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    refine ((hf y hy).mul (hasDerivAt_ofReal_cpow_const hy.ne' hw)).congr_deriv ?_
    have hsplit : (y : ℂ) ^ w = (y : ℂ) ^ (w - 1) * (y : ℂ) := by
      conv_lhs => rw [show w = (w - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ hyc, Complex.cpow_one]
    rw [hsplit, ← hg y hy]
    ring
  have hint : IntegrableOn (fun y : ℝ => g y * (y : ℂ) ^ (w - 1) + w * (f y * (y : ℂ) ^ (w - 1)))
      (Ioi 0) :=
    hgi.add (hfi.const_mul w)
  have hzero := integral_Ioi_deriv_eq_zero hderiv hint h0 htop
  rw [integral_add hgi (hfi.const_mul w)] at hzero
  have hc : ∫ y in Ioi (0 : ℝ), w * (f y * (y : ℂ) ^ (w - 1)) = w * ∫ y in Ioi (0 : ℝ), f y *
      (y : ℂ) ^ (w - 1) :=
    integral_const_mul w _
  linear_combination hzero - hc

private theorem parts (a : ZMod 2) {f f' g : ℝ → ℂ} (hf : ∀ y : ℝ, y ≠ 0 → HasDerivAt f (f' y) y)
    (hg : ∀ y : ℝ, y ≠ 0 → (y : ℂ) * f' y = g y) {w : ℂ} (hw : w ≠ 0)
    (hfi : Integrable fun y : ℝ => f y * kernel a w y)
        (hgi : Integrable fun y : ℝ => g y * kernel a w y)
    (h0 : Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) (𝓝[≠] 0) (𝓝 0))
    (hbot : Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) atBot (𝓝 0))
    (htop : Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) atTop (𝓝 0)) :
    w * ∫ y : ℝ, f y * kernel a w y = -∫ y : ℝ, g y * kernel a w y := by

  have hpos_f : ∫ y in Ioi (0 : ℝ), f y * kernel a w y = ∫ y in Ioi (0 : ℝ), f y * (y : ℂ) ^
      (w - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by rw [kernel_of_pos a w hy]
  have hpos_g : ∫ y in Ioi (0 : ℝ), g y * kernel a w y = ∫ y in Ioi (0 : ℝ), g y * (y : ℂ) ^
      (w - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy => by rw [kernel_of_pos a w hy]
  have hfi_on : IntegrableOn (fun y : ℝ => f y * kernel a w y) (Ioi 0) := hfi.integrableOn
  have hgi_on : IntegrableOn (fun y : ℝ => g y * kernel a w y) (Ioi 0) := hgi.integrableOn
  have hfi_pos : IntegrableOn (fun y : ℝ => f y * (y : ℂ) ^ (w - 1)) (Ioi 0) :=
    hfi_on.congr_fun (fun y hy => by beta_reduce; rw [kernel_of_pos a w hy]) measurableSet_Ioi
  have hgi_pos : IntegrableOn (fun y : ℝ => g y * (y : ℂ) ^ (w - 1)) (Ioi 0) :=
    hgi_on.congr_fun (fun y hy => by beta_reduce; rw [kernel_of_pos a w hy]) measurableSet_Ioi
  have h0_pos : Tendsto (fun y : ℝ => f y * (y : ℂ) ^ w) (𝓝[>] 0) (𝓝 0) := by
    refine (h0.mono_left (nhdsWithin_mono _ fun y (hy : y ∈ Ioi 0) =>
      (mem_Ioi.mp hy).ne')).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [abs_of_pos hy]
  have htop_pos : Tendsto (fun y : ℝ => f y * (y : ℂ) ^ w) atTop (𝓝 0) := by
    refine htop.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [abs_of_pos hy]
  have hP := parts_Ioi (fun y hy => hf y hy.ne') (fun y hy => hg y hy.ne') hw hfi_pos hgi_pos h0_pos
      htop_pos

  set ε : ℂ := if a = 0 then 1 else -1 with hε
  have hneg_f : ∫ y in Iic (0 : ℝ), f y * kernel a w y = ε * ∫ y in Ioi (0 : ℝ), f (-y) * (y : ℂ) ^
      (w - 1) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun y => f y * kernel a w y)
    rw [neg_zero] at h
    have hc : ε * ∫ y in Ioi (0 : ℝ), f (-y) * (y : ℂ) ^ (w - 1)
        = ∫ y in Ioi (0 : ℝ), ε * (f (-y) * (y : ℂ) ^ (w - 1)) := (integral_const_mul ε _).symm
    rw [← h, hc]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    show f (-y) * kernel a w (-y) = ε * (f (-y) * (y : ℂ) ^ (w - 1))
    rw [kernel_neg a w hy, ← hε]
    ring
  have hneg_g : ∫ y in Iic (0 : ℝ), g y * kernel a w y = ε * ∫ y in Ioi (0 : ℝ), g (-y) * (y : ℂ) ^
      (w - 1) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun y => g y * kernel a w y)
    rw [neg_zero] at h
    have hc : ε * ∫ y in Ioi (0 : ℝ), g (-y) * (y : ℂ) ^ (w - 1)
        = ∫ y in Ioi (0 : ℝ), ε * (g (-y) * (y : ℂ) ^ (w - 1)) := (integral_const_mul ε _).symm
    rw [← h, hc]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    show g (-y) * kernel a w (-y) = ε * (g (-y) * (y : ℂ) ^ (w - 1))
    rw [kernel_neg a w hy, ← hε]
    ring
  have hfi_neg : IntegrableOn (fun y : ℝ => f (-y) * (y : ℂ) ^ (w - 1)) (Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => f (-y) * kernel a w (-y))
        (Ioi 0) := hfi.comp_neg.integrableOn
    have h2 : IntegrableOn (fun y : ℝ => ε * (f (-y) * kernel a w (-y))) (Ioi 0) := h1.const_mul ε
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    beta_reduce
    rw [kernel_neg a w hy, ← hε]
    have hεε : ε * ε = 1 := by rw [hε]; split_ifs <;> norm_num
    linear_combination (f (-y) * (y : ℂ) ^ (w - 1)) * hεε
  have hgi_neg : IntegrableOn (fun y : ℝ => g (-y) * (y : ℂ) ^ (w - 1)) (Ioi 0) := by
    have h1 : IntegrableOn (fun y : ℝ => g (-y) * kernel a w (-y))
        (Ioi 0) := hgi.comp_neg.integrableOn
    have h2 : IntegrableOn (fun y : ℝ => ε * (g (-y) * kernel a w (-y))) (Ioi 0) := h1.const_mul ε
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    beta_reduce
    rw [kernel_neg a w hy, ← hε]
    have hεε : ε * ε = 1 := by rw [hε]; split_ifs <;> norm_num
    linear_combination (g (-y) * (y : ℂ) ^ (w - 1)) * hεε
  have hf_neg : ∀ y : ℝ, 0 < y → HasDerivAt (fun y : ℝ => f (-y)) (-f' (-y)) y := fun y hy => by
    have h := (hf (-y) (neg_neg_of_pos hy).ne).scomp y (hasDerivAt_neg y)
    simpa [Function.comp_def] using h
  have hg_neg : ∀ y : ℝ, 0 < y → (y : ℂ) * -f' (-y) = g (-y) := fun y hy => by
    have h := hg (-y) (neg_neg_of_pos hy).ne
    push_cast at h
    linear_combination h
  have h0_neg : Tendsto (fun y : ℝ => f (-y) * (y : ℂ) ^ w) (𝓝[>] 0) (𝓝 0) := by
    have hneg : Tendsto (fun y : ℝ => -y) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℝ => -y) (𝓝 0) (𝓝 (-0)) := (continuous_neg.tendsto 0)
        rw [neg_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
        exact (neg_neg_of_pos hy).ne
    refine (h0.comp hneg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp [abs_of_pos hy]
  have htop_neg : Tendsto (fun y : ℝ => f (-y) * (y : ℂ) ^ w) atTop (𝓝 0) := by
    refine (hbot.comp tendsto_neg_atTop_atBot).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp [abs_of_pos hy]
  have hN := parts_Ioi hf_neg hg_neg hw hfi_neg hgi_neg h0_neg htop_neg

  rw [← intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn,
    ← intervalIntegral.integral_Iic_add_Ioi hgi.integrableOn hgi.integrableOn, hpos_f, hpos_g,
        hneg_f, hneg_g]
  linear_combination hP + ε * hN

private theorem norm_integral_mul_kernel_le (a : ZMod 2) (w : ℂ) {f : ℝ → ℂ} {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (h : ∀ y : ℝ, y ≠ 0 → ‖f y‖ * |y| ^ (w.re - 1) ≤ φ y) :
    ‖∫ y : ℝ, f y * kernel a w y‖ ≤ ∫ y : ℝ, φ y := by
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [ae_iff]
    simp
  refine norm_integral_le_of_norm_le hφ ?_
  filter_upwards [hae] with y hy
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_kernel_le a w hy) (norm_nonneg _)).trans (h y hy)

private theorem tendsto_mul_abs_cpow_atTop_atBot {f : ℝ → ℂ} {C : ℝ} {N : ℕ}
    (hdec : ∀ y : ℝ, 1 ≤ |y| → ‖f y‖ ≤ C * |y| ^ (-(N : ℝ))) {w : ℂ} (hw : w.re < N) :
    Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) atTop (𝓝 0) ∧
      Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) atBot (𝓝 0) := by
  have hC : 0 ≤ C := by
    have h1 := hdec 1 (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at h1
    exact (norm_nonneg _).trans h1
  have hbound : ∀ y : ℝ, 1 ≤ |y| →
      ‖f y * ((|y| : ℝ) : ℂ) ^ w‖ ≤ C * |y| ^ (-((N : ℝ) - w.re)) := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      norm_num at hy
    rw [norm_mul, norm_abs_cpow w y hy0]
    calc ‖f y‖ * |y| ^ w.re ≤ C * |y| ^ (-(N : ℝ)) * |y| ^ w.re :=
          mul_le_mul_of_nonneg_right (hdec y hy) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = C * |y| ^ (-((N : ℝ) - w.re)) := by
          rw [mul_assoc, ← Real.rpow_add (abs_pos.2 hy0)]
          ring_nf
  have h1 : Tendsto (fun x : ℝ => x ^ (-((N : ℝ) - w.re))) atTop (𝓝 0) := tendsto_rpow_neg_atTop
      (by linarith)
  have hlim_top : Tendsto (fun y : ℝ => C * |y| ^ (-((N : ℝ) - w.re))) atTop (𝓝 0) := by
    have h := h1.const_mul C
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [abs_of_nonneg hy]
  have hlim_bot : Tendsto (fun y : ℝ => C * |y| ^ (-((N : ℝ) - w.re))) atBot (𝓝 0) := by
    have h := (h1.comp tendsto_neg_atBot_atTop).const_mul C
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with y hy
    simp only [Function.comp_def]
    rw [abs_of_nonpos hy]
  refine ⟨squeeze_zero_norm' ?_ hlim_top, squeeze_zero_norm' ?_ hlim_bot⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact hbound y (le_abs.2 (Or.inl hy))
  · filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
    exact hbound y (le_abs.2 (Or.inr (by linarith)))

private theorem tendsto_mul_abs_cpow_nhds_zero {f : ℝ → ℂ} {C σ : ℝ}
    (hblow : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖f y‖ ≤ C * |y| ^ (-σ)) {w : ℂ} (hw : σ < w.re) :
    Tendsto (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ w) (𝓝[≠] 0) (𝓝 0) := by
  have hC : 0 ≤ C := by
    have h1 := hblow 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at h1
    exact (norm_nonneg _).trans h1
  have hbound : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖f y * ((|y| : ℝ) : ℂ) ^ w‖ ≤ C * |y| ^ (w.re - σ) := by
    intro y hy0 hy1
    rw [norm_mul, norm_abs_cpow w y hy0]
    calc ‖f y‖ * |y| ^ w.re ≤ C * |y| ^ (-σ) * |y| ^ w.re :=
          mul_le_mul_of_nonneg_right (hblow y hy0 hy1) (Real.rpow_nonneg (abs_nonneg _) _)
      _ = C * |y| ^ (w.re - σ) := by
          rw [mul_assoc, ← Real.rpow_add (abs_pos.2 hy0)]
          ring_nf
  have hlim : Tendsto (fun y : ℝ => C * |y| ^ (w.re - σ)) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (w.re - σ)) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (w.re - σ) (Or.inr (by linarith))).tendsto
      rwa [Real.zero_rpow (by linarith)] at this
    have h2 : Tendsto (fun y : ℝ => |y|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun y : ℝ => |y|) (𝓝[≠] (0 : ℝ)) (𝓝 |(0 : ℝ)|) :=
        (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      rwa [abs_zero] at h
    simpa using (h1.comp h2).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  have hsmall : ∀ᶠ y : ℝ in 𝓝[≠] (0 : ℝ), |y| ≤ 1 := by
    have habs : Tendsto (fun y : ℝ => |y|) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have h := continuous_abs.tendsto (0 : ℝ)
      rwa [abs_zero] at h
    have h : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), |y| < 1 := habs.eventually (gt_mem_nhds zero_lt_one)
    exact (h.mono fun y hy => hy.le).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with y hy1 (hy0 : y ≠ 0)
  exact hbound y hy0 hy1

end ArchWhittakerGrowth

end
end SpanParts

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

private theorem pos_of_hc₀R {P : RealArchParam} {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (a : ZMod 2) : ∀ μ ∈ (P.twist 0 a).gammaR, 0 < c₀ + μ.re :=
  fun μ hμ => by linarith [(hc₀ a).1 μ hμ]

private theorem pos_of_hc₀C {P : RealArchParam} {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (a : ZMod 2) : ∀ ν ∈ (P.twist 0 a).gammaC, 0 < c₀ + ν.re :=
  fun ν hν => by linarith [(hc₀ a).2 ν hν]

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

private def EdgeDecay {P : RealArchParam} (d : ArchDatumR P) : Prop :=
  ∀ (u : ℂ) (a : ZMod 2) (m : ℕ), ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → ∃ M : ℝ,
    ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ s : ℂ, s.re = σ →
      ‖(P.twist u a).archFactor s * d.zetaEntire k u a s‖ ≤ M / (1 + |s.im|) ^ m

private theorem strip_decay {P : RealArchParam} (d : ArchDatumR P) (hZ : EdgeDecay d) {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (a : ZMod 2) {σ₁ : ℝ} (hσ₁ : c₀ ≤ σ₁) (n : ℕ) :
    ∃ C : ℝ, ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ s : ℂ, c₀ ≤ s.re → s.re ≤ σ₁ →
      ‖(P.twist 0 a).archFactor s * d.zetaEntire k 0 a s‖ ≤ C / (1 + |s.im|) ^ n := by

  obtain ⟨σR, hσR⟩ := hZ 0 a n
  obtain ⟨σD, hσD⟩ := hZ (-(0 + P.centralExponent)) (a + P.centralSign) n

  obtain ⟨σ₂, hσ₁₂, hRσ₂⟩ : ∃ σ₂ : ℝ, σ₁ ≤ σ₂ ∧ σR ≤ σ₂ :=
      ⟨max σ₁ σR, le_max_left _ _, le_max_right _ _⟩
  have hcσ₂ : c₀ ≤ σ₂ := hσ₁.trans hσ₁₂
  obtain ⟨A, hAlt, hAoff, hAfar⟩ :=
    exists_left_edge' (P.twist 0 a).gammaR (P.twist 0 a).gammaC (min c₀ (1 - σD))
  have hAc : A < c₀ := hAlt.trans_le (min_le_left _ _)
  have hAD : σD ≤ 1 - A := by linarith [hAlt.trans_le (min_le_right c₀ (1 - σD))]

  obtain ⟨c, -, hmachine⟩ := interior_decay_of_edges (P.twist 0 a).gammaR
      (P.twist 0 a).gammaC hAc hcσ₂
    (pos_of_hc₀R hc₀ a) (pos_of_hc₀C hc₀ a) hAoff n

  obtain ⟨MR, hMR⟩ := hσR σ₂ hRσ₂
  obtain ⟨MD, hMD⟩ := hσD (1 - A) hAD
  obtain ⟨K, hK⟩ := exists_norm_gammaFactor_le_dual (rel_gammaR P 0 a)
      (rel_gammaC P 0 a) hAoff hAfar
  have hε : 0 < ‖(P.twist 0 a).epsilonFactor‖ := norm_pos_iff.2 (epsilonFactor_ne_zero _)

  obtain ⟨M, hM0, hMR_le, hMD_le⟩ : ∃ M : ℝ, 0 ≤ M ∧ MR ≤ M ∧
      max K 0 * MD / ‖(P.twist 0 a).epsilonFactor‖ ≤ M :=
    ⟨max (max MR (max K 0 * MD / ‖(P.twist 0 a).epsilonFactor‖)) 0, le_max_right _ _,
      (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _)⟩
  refine ⟨c * M, fun k hk s hs₀ hs₁ => ?_⟩
  have hedge : ∀ w : ℂ, w.re = A ∨ w.re = σ₂ →
      ‖gammaFactor (P.twist 0 a).gammaR (P.twist 0 a).gammaC w * d.zetaEntire k 0 a w‖ ≤
        M / (1 + |w.im|) ^ n := by
    intro w hw
    have hden : (0 : ℝ) < (1 + |w.im|) ^ n := by positivity
    rcases hw with hwA | hwσ
    ·
      have hFE := d.functional_equation k 0 a w (GroupR.isK_det_ne_zero hk)
      have hwk : ArchR.IsK (ArchR.weyl * k) := GroupR.isK_mul GroupR.isK_weyl hk
      have hre : (1 - w).re = 1 - A := by simp [hwA]
      have hdual := hMD (ArchR.weyl * k) hwk (1 - w) hre
      have him : |(1 - w).im| = |w.im| := by simp
      rw [him, archFactor_eq] at hdual
      have hΦ : d.zetaEntire k 0 a w =
          d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign) (1 - w) /
            (P.twist 0 a).epsilonFactor := by
        rw [hFE, mul_div_cancel_left₀ _ (epsilonFactor_ne_zero _)]
      have hL : ‖gammaFactor (P.twist 0 a).gammaR (P.twist 0 a).gammaC w‖ ≤
          max K 0 * ‖gammaFactor (P.twist (-(0 + P.centralExponent)) (a + P.centralSign)).gammaR
            (P.twist (-(0 + P.centralExponent)) (a + P.centralSign)).gammaC (1 - w)‖ :=
        (hK w hwA).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      rw [hΦ, norm_mul, norm_div, ← mul_div_assoc]
      have h1 : ‖gammaFactor (P.twist 0 a).gammaR (P.twist 0 a).gammaC w‖ *
          ‖d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign) (1 - w)‖ ≤
            max K 0 * (MD / (1 + |w.im|) ^ n) := by
        calc ‖gammaFactor (P.twist 0 a).gammaR (P.twist 0 a).gammaC w‖ *
              ‖d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign) (1 - w)‖
            ≤ (max K 0 * ‖gammaFactor (P.twist (-(0 + P.centralExponent))
                (a + P.centralSign)).gammaR
                (P.twist (-(0 + P.centralExponent)) (a + P.centralSign)).gammaC (1 - w)‖) *
              ‖d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign)
                  (1 - w)‖ :=
              mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = max K 0 * ‖gammaFactor (P.twist (-(0 + P.centralExponent)) (a + P.centralSign)).gammaR
                (P.twist (-(0 + P.centralExponent)) (a + P.centralSign)).gammaC (1 - w) *
                d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign)
                    (1 - w)‖ := by
              rw [norm_mul]; ring
          _ ≤ max K 0 * (MD / (1 + |w.im|) ^ n) := mul_le_mul_of_nonneg_left hdual
              (le_max_right _ _)
      calc ‖gammaFactor (P.twist 0 a).gammaR (P.twist 0 a).gammaC w‖ *
            ‖d.zetaEntire (ArchR.weyl * k) (-(0 + P.centralExponent)) (a + P.centralSign) (1 - w)‖ /
              ‖(P.twist 0 a).epsilonFactor‖
          ≤ max K 0 * (MD / (1 + |w.im|) ^ n) / ‖(P.twist 0 a).epsilonFactor‖ :=
            div_le_div_of_nonneg_right h1 hε.le
        _ = max K 0 * MD / ‖(P.twist 0 a).epsilonFactor‖ / (1 + |w.im|) ^ n := by ring
        _ ≤ M / (1 + |w.im|) ^ n := div_le_div_of_nonneg_right hMD_le hden.le
    ·
      have h := hMR k hk w hwσ
      rw [archFactor_eq] at h
      exact h.trans (div_le_div_of_nonneg_right hMR_le hden.le)
  have h := hmachine (d.zetaEntire k 0 a) M hM0 (d.zetaEntire_differentiable k 0 a)
    (d.zetaEntire_finiteOrder k 0 a A σ₂) hedge s hs₀ (hs₁.trans hσ₁₂)
  rw [archFactor_eq]
  exact h

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

private structure Good (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi W) ArchR.glSet
  top : ∀ (j N : ℕ), ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
    ‖iteratedFDerivWithin ℝ j (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^
        (-(N : ℝ))
  zero : ∀ j : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k →
      y ≠ 0 → |y| ≤ 1 →
    ‖iteratedFDerivWithin ℝ j (ArchR.asPi W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^
        (-σ)

private theorem Good.derivW (h : Good W) (X : Matrix (Fin 2) (Fin 2) ℝ) : Good
    (DerivR.derivW X W) :=
  ⟨smooth_derivW h.smooth X, fun j N => decay_top_derivW h.smooth h.top X j N,
    fun j => decay_zero_derivW h.smooth h.zero X j⟩

private theorem Good.of_datum {P : RealArchParam} (d : ArchDatumR P) : Good d.W :=
    ⟨d.smooth, d.decay_top, d.decay_zero⟩

private def orbit (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ) : ℂ := W
    (ArchR.diagOne y * k)

private def zint (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (s : ℂ) : ℂ :=
  ∫ y : ℝ, orbit W k y * kernel a (u + s - 1) y

private theorem re_add_sub_one (u s : ℂ) : (u + s - 1).re = u.re + s.re - 1 := by
  simp [Complex.add_re, Complex.sub_re]

private theorem im_add_sub_one (u s : ℂ) : (u + s - 1).im = u.im + s.im := by
  simp [Complex.add_im, Complex.sub_im]

private theorem Good.norm_orbit_le (h : Good W) (N : ℕ) :
    ∃ C σ : ℝ, ∀ (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → ∀ y : ℝ, y ≠ 0 →
      ‖orbit W k y‖ ≤ C * IntegralR.env σ N y := by
  obtain ⟨Ct, ht⟩ := h.top 0 N
  obtain ⟨Cz, σ, hz⟩ := h.zero 0
  refine ⟨max Ct Cz, σ, fun k hk y hy => ?_⟩
  rw [orbit, IntegralR.norm_orbit_eq]
  exact IntegralR.orbitEnvelope_of ht hz hk hy

private theorem Good.continuousOn_orbit (h : Good W) {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k) :
    ContinuousOn (orbit W k) {0}ᶜ := fun _ hy =>
  (OrbitR.hasDerivAt_orbit W h.smooth hk (Set.mem_compl_singleton_iff.1
      hy)).continuousAt.continuousWithinAt

private theorem zw_eq_kernel (u : ℂ) (a : ZMod 2) (s : ℂ) {y : ℝ} (hy : y ≠ 0) :
    IntegralR.zw u a s y = kernel a (u + s - 1) y := by
  have hx : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hy
  unfold IntegralR.zw ArchR.quasiChar kernel signFactor
  rw [show u + s - 1 - 1 = u + (s - 1) + (-1) by ring, Complex.cpow_add _ _ hx,
      Complex.cpow_add _ _ hx,
    Complex.cpow_neg_one]
  ring

private theorem aestronglyMeasurable_orbit_mul_kernel (h : Good W) {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : ArchR.IsK k)
    (u : ℂ) (a : ZMod 2) (s : ℂ) :
    AEStronglyMeasurable (fun y : ℝ => orbit W k y * kernel a (u + s - 1) y) volume := by
  have h1 : AEStronglyMeasurable (fun y : ℝ => orbit W k y * IntegralR.zw u a s y) volume :=
    IntegralR.aestronglyMeasurable_of_continuousOn
        ((h.continuousOn_orbit hk).mul (IntegralR.continuousOn_zw u a s))
  refine h1.congr ?_
  filter_upwards [IntegralR.ae_ne_zero] with y hy
  rw [zw_eq_kernel u a s hy]

private theorem integral_zetaIntegrand_eq (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (k : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (s : ℂ) : ∫ y : ℝ, ArchR.zetaIntegrand W k u a s y = zint W k u a s := by
  unfold zint
  refine integral_congr_ae ?_
  filter_upwards [IntegralR.ae_ne_zero] with y hy
  rw [IntegralR.zetaIntegrand_eq, zw_eq_kernel u a s hy]
  rfl

private theorem Good.order_zero (h : Good W) (u : ℂ) (a : ZMod 2) :
    ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → ∃ M : ℝ, ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ s : ℂ,
        s.re = σ →
      Integrable (fun y : ℝ => orbit W k y * kernel a (u + s - 1) y) ∧ ‖zint W k u a s‖ ≤ M := by
  obtain ⟨Cz, σz, hz⟩ := h.zero 0
  refine ⟨σz - u.re + 2, fun σ hσ => ?_⟩
  set α : ℝ := u.re + σ - 2 with hα
  set N : ℕ := ⌈u.re + σ⌉₊ + 1 with hN
  have hN' : α - N < -1 := by
    have := Nat.le_ceil (u.re + σ)
    rw [hN]
    push_cast
    linarith
  have hα' : -1 < α - σz := by rw [hα]; linarith
  obtain ⟨Ct, ht⟩ := h.top 0 N
  set C : ℝ := max Ct Cz with hC
  have henv : ∀ (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → ∀ y : ℝ, y ≠ 0 →
      ‖orbit W k y‖ ≤ C * IntegralR.env σz N y := fun k hk y hy => by
    rw [orbit, IntegralR.norm_orbit_eq]
    exact IntegralR.orbitEnvelope_of ht hz hk hy
  have hφ : Integrable fun y : ℝ => C * (IntegralR.env σz N y * |y| ^ α) :=
    (IntegralR.integrable_env_mul_rpow hα' hN').const_mul C
  refine ⟨∫ y : ℝ, C * (IntegralR.env σz N y * |y| ^ α), fun k hk s hs => ?_⟩
  have hre : (u + s - 1).re - 1 = α := by rw [re_add_sub_one, hs, hα]; ring
  have hpt : ∀ y : ℝ, y ≠ 0 →
      ‖orbit W k y‖ * |y| ^ ((u + s - 1).re - 1) ≤ C *
          (IntegralR.env σz N y * |y| ^ α) := fun y hy => by
    rw [hre, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (henv k hk y hy) (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨?_, norm_integral_mul_kernel_le a (u + s - 1) hφ hpt⟩
  refine hφ.mono' (aestronglyMeasurable_orbit_mul_kernel h hk u a s) ?_
  filter_upwards [IntegralR.ae_ne_zero] with y hy
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_kernel_le a _ hy) (norm_nonneg _)).trans (hpt y hy)

private theorem Good.limits (h : Good W) (u : ℂ) :
    ∃ σ₁ : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ s : ℂ, s.re = σ →
      Tendsto (fun y : ℝ => orbit W k y * ((|y| : ℝ) : ℂ) ^ (u + s - 1)) (𝓝[≠] 0) (𝓝 0) ∧
      Tendsto (fun y : ℝ => orbit W k y * ((|y| : ℝ) : ℂ) ^ (u + s - 1)) atBot (𝓝 0) ∧
      Tendsto (fun y : ℝ => orbit W k y * ((|y| : ℝ) : ℂ) ^ (u + s - 1)) atTop (𝓝 0) := by
  obtain ⟨Cz, σz, hz⟩ := h.zero 0
  refine ⟨σz - u.re + 2, fun σ hσ k hk s hs => ?_⟩
  have hre : (u + s - 1).re = u.re + σ - 1 := by rw [re_add_sub_one, hs]
  set N : ℕ := ⌈u.re + σ⌉₊ + 1 with hN
  have hwN : (u + s - 1).re < N := by
    have := Nat.le_ceil (u.re + σ)
    rw [hre, hN]
    push_cast
    linarith
  have hwz : σz < (u + s - 1).re := by rw [hre]; linarith
  obtain ⟨Ct, ht⟩ := h.top 0 N
  have hdec : ∀ y : ℝ, 1 ≤ |y| → ‖orbit W k y‖ ≤ Ct * |y| ^ (-(N : ℝ)) := fun y hy => by
    rw [orbit, IntegralR.norm_orbit_eq]
    exact ht y k hk hy
  have hblow : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖orbit W k y‖ ≤ Cz * |y| ^ (-σz) := fun y hy0 hy1 => by
    rw [orbit, IntegralR.norm_orbit_eq]
    exact hz y k hk hy0 hy1
  obtain ⟨htop, hbot⟩ := tendsto_mul_abs_cpow_atTop_atBot hdec hwN
  exact ⟨tendsto_mul_abs_cpow_nhds_zero hblow hwz, hbot, htop⟩

private theorem le_max_four (f : Fin 2 × Fin 2 → ℝ) (ij : Fin 2 × Fin 2) :
    f ij ≤ max (max (f (0, 0)) (f (0, 1))) (max (f (1, 0)) (f (1, 1))) := by
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j <;> simp

private theorem integral_const_mul' (c : ℂ) (f : ℝ → ℂ) : ∫ y : ℝ, c * f y = c * ∫ y : ℝ,
    f y := integral_const_mul c f

private theorem orbit_derivW_sum (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (k : Matrix (Fin 2) (Fin 2) ℝ)
    (a : ZMod 2) (w : ℂ)
    (y : ℝ) :
    (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
        ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
            (ArchR.diagOne y * k))
        * kernel a w y
      = ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
          ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) *
            (orbit (DerivR.derivW (DerivR.unitMat ij.1 ij.2) W) k y * kernel a w y) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [orbit, mul_assoc]

private theorem one_add_abs_im_le (u s : ℂ) (hre : 1 ≤ (u + s - 1).re) : 1 + |s.im| ≤
    (2 + |u.im|) * ‖u + s - 1‖ := by
  have h1 : 1 ≤ ‖u + s - 1‖ := hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have h2 : |s.im| ≤ ‖u + s - 1‖ + |u.im| := by
    have him : s.im = (u + s - 1).im - u.im := by rw [im_add_sub_one]; ring
    rw [him]
    exact (abs_sub _ _).trans (add_le_add (Complex.abs_im_le_norm _) le_rfl)
  have h3 : |u.im| ≤ |u.im| * ‖u + s - 1‖ := le_mul_of_one_le_right (abs_nonneg _) h1
  nlinarith [abs_nonneg u.im]

private theorem level (m : ℕ) :
    ∀ W : Matrix (Fin 2) (Fin 2) ℝ → ℂ, Good W → ∀ (u : ℂ) (a : ZMod 2), ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
        ∃ M : ℝ,
      ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ s : ℂ, s.re = σ → ‖zint W k u a s‖ ≤ M /
          (1 + |s.im|) ^ m := by
  induction m with
  | zero =>
    intro W hW u a
    obtain ⟨σ₀, h⟩ := hW.order_zero u a
    refine ⟨σ₀, fun σ hσ => ?_⟩
    obtain ⟨M, hM⟩ := h σ hσ
    exact ⟨M, fun k hk s hs => by simpa using (hM k hk s hs).2⟩
  | succ m ih =>
    intro W hW u a
    obtain ⟨σW, hσW⟩ := hW.order_zero u a
    obtain ⟨σL, hσL⟩ := hW.limits u
    have hD : ∀ ij : Fin 2 × Fin 2, Good (DerivR.derivW (DerivR.unitMat ij.1 ij.2) W) := fun ij =>
        hW.derivW _
    choose σD hσD using fun ij => ih _ (hD ij) u a
    choose σI hσI using fun ij => (hD ij).order_zero u a
    refine ⟨max (max σW σL) (max (2 - u.re) (max (max (max (σD (0, 0)) (σD (0, 1)))
        (max (σD (1, 0)) (σD (1, 1))))
      (max (max (σI (0, 0)) (σI (0, 1))) (max (σI (1, 0)) (σI (1, 1)))))), fun σ hσ => ?_⟩
    have hσW' : σW ≤ σ := le_trans (by simp) hσ
    have hσL' : σL ≤ σ := le_trans (by simp) hσ
    have hσu : 2 - u.re ≤ σ := le_trans (le_max_of_le_right (le_max_left _ _)) hσ
    have hσD' : ∀ ij, σD ij ≤ σ := fun ij => le_trans (le_trans (le_max_four σD ij) (by simp)) hσ
    have hσI' : ∀ ij, σI ij ≤ σ := fun ij => le_trans (le_trans (le_max_four σI ij) (by simp)) hσ
    obtain ⟨MW, hMW⟩ := hσW σ hσW'
    choose MD hMD using fun ij => hσD ij σ (hσD' ij)
    choose MI hMI using fun ij => hσI ij σ (hσI' ij)
    refine ⟨(2 + |u.im|) * ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), MD ij,
        fun k hk s hs => ?_⟩
    set w : ℂ := u + s - 1 with hw_def
    have hwre : 1 ≤ w.re := by rw [hw_def, re_add_sub_one, hs]; linarith
    have hw : w ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hwre; linarith

    have hf : ∀ y : ℝ, y ≠ 0 → HasDerivAt (orbit W k)
        (((y : ℂ))⁻¹ * ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
          ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
              (ArchR.diagOne y * k)) y :=
      fun y hy => OrbitR.hasDerivAt_orbit W hW.smooth hk hy
    have hg : ∀ y : ℝ, y ≠ 0 → (y : ℂ) * (((y : ℂ))⁻¹ * ∑ ij ∈
        (Finset.univ : Finset (Fin 2 × Fin 2)),
        ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
            (ArchR.diagOne y * k))
        = ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
            ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
                (ArchR.diagOne y * k) :=
      fun y hy => by
        have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
        rw [← mul_assoc, mul_inv_cancel₀ hyc, one_mul]
    have hfi : Integrable fun y : ℝ => orbit W k y * kernel a w y := (hMW k hk s hs).1
    have hsum_eq : (fun y : ℝ => (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
          ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
              (ArchR.diagOne y * k))
          * kernel a w y)
        = fun y : ℝ => ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
            ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) *
            (orbit (DerivR.derivW (DerivR.unitMat ij.1 ij.2) W) k y * kernel a w y) := by
      funext y
      exact orbit_derivW_sum W k a w y
    have hgi : Integrable fun y : ℝ => (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
        ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
            (ArchR.diagOne y * k))
        * kernel a w y := by
      rw [hsum_eq]
      exact integrable_finsetSum _ fun ij _ => ((hMI ij k hk s hs).1.const_mul _)
    obtain ⟨h0, hbot, htop⟩ := hσL σ hσL' k hk s hs
    have hP := parts a hf hg hw hfi hgi h0 hbot htop

    have hrhs : ‖∫ y : ℝ, (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
          ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
              (ArchR.diagOne y * k))
          * kernel a w y‖
        ≤ (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), MD ij) / (1 + |s.im|) ^ m := by
      rw [hsum_eq, integral_finsetSum _ fun ij _ => ((hMI ij k hk s hs).1.const_mul _)]
      simp_rw [integral_const_mul']
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun ij _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc := OrbitR.abs_coeff_le_one hk ij.1 ij.2
      have hz : ‖zint (DerivR.derivW (DerivR.unitMat ij.1 ij.2) W) k u a s‖ ≤ MD ij /
          (1 + |s.im|) ^ m :=
        hMD ij k hk s hs
      calc |k 0 ij.1 * k 0 ij.2| * ‖∫ y : ℝ, orbit
             (DerivR.derivW (DerivR.unitMat ij.1 ij.2) W) k y * kernel a w y‖
          ≤ 1 * (MD ij / (1 + |s.im|) ^ m) := mul_le_mul hc hz (norm_nonneg _) zero_le_one
        _ = MD ij / (1 + |s.im|) ^ m := one_mul _

    have hzint : ‖zint W k u a s‖ * ‖w‖ = ‖∫ y : ℝ, (∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
        ((k 0 ij.1 * k 0 ij.2 : ℝ) : ℂ) * DerivR.derivW (DerivR.unitMat ij.1 ij.2) W
            (ArchR.diagOne y * k))
        * kernel a w y‖ := by
      rw [mul_comm, ← norm_mul, zint, hP, norm_neg]
    have hpos : 0 < 1 + |s.im| := by positivity
    have hbound : 1 + |s.im| ≤ (2 + |u.im|) * ‖w‖ := one_add_abs_im_le u s hwre
    rw [le_div_iff₀ (pow_pos hpos _)]
    have hrhs' := (le_div_iff₀ (pow_pos hpos m)).1 hrhs
    calc ‖zint W k u a s‖ * (1 + |s.im|) ^ (m + 1)
        = ‖zint W k u a s‖ * (1 + |s.im|) * (1 + |s.im|) ^ m := by ring
      _ ≤ ‖zint W k u a s‖ * ((2 + |u.im|) * ‖w‖) * (1 + |s.im|) ^ m := by gcongr
      _ = (2 + |u.im|) * ((‖zint W k u a s‖ * ‖w‖) * (1 + |s.im|) ^ m) := by ring
      _ ≤ (2 + |u.im|) * ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)), MD ij := by
          rw [hzint]
          exact mul_le_mul_of_nonneg_left hrhs' (by positivity)

private theorem edgeDecay {P : RealArchParam} (d : ArchDatumR P) : ZetaR.EdgeDecay d := by
  intro u a m
  obtain ⟨σ₀, h⟩ := level m d.W (Good.of_datum d) u a
  refine ⟨max σ₀ (d.zeta_abscissa - u.re + 1), fun σ hσ => ?_⟩
  obtain ⟨M, hM⟩ := h σ (le_trans (le_max_left _ _) hσ)
  refine ⟨M, fun k hk s hs => ?_⟩
  have habs : d.zeta_abscissa < s.re + u.re := by
    have := le_trans (le_max_right _ _) hσ
    rw [hs]
    linarith
  rw [← d.zeta_eq k u a s (GroupR.isK_det_ne_zero hk) habs, integral_zetaIntegrand_eq]
  exact hM k hk s hs

end ZetaInt

end ArchWhittakerGrowth

end
end SpanZetaInt

section SpanInversion
set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped Real

namespace ArchWhittakerGrowth
namespace Inversion

private def strip (c σ : ℝ) : Set ℂ := {s : ℂ | c ≤ s.re ∧ s.re ≤ σ}

private theorem mem_strip_line {c σ : ℝ} {a : ℝ} (hca : c ≤ a) (haσ : a ≤ σ) (y : ℝ) :
    ((a : ℂ) + y * I) ∈ strip c σ := by
  simp [strip, hca, haσ]

private theorem one_add_sq_le (y : ℝ) : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
  nlinarith [abs_nonneg y, sq_abs y]

private theorem div_pow_le_mul_inv {B : ℝ} (hB : 0 ≤ B) (y : ℝ) : B / (1 + |y|) ^ 2 ≤ B *
    (1 + y ^ 2)⁻¹ := by
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hB (by positivity) (one_add_sq_le y)

section line

variable {c σ : ℝ} {F : ℂ → ℂ} {B : ℝ}

private theorem continuous_line (hF : ContinuousOn F (strip c σ)) {a : ℝ} (hca : c ≤ a)
    (haσ : a ≤ σ) :
    Continuous fun y : ℝ => F (a + y * I) := by
  refine hF.comp_continuous (by fun_prop) fun y => mem_strip_line hca haσ y

private theorem integrable_line (hF : ContinuousOn F (strip c σ)) (hB : 0 ≤ B)
    (hbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ B / (1 + |s.im|) ^ 2) {a : ℝ} (hca : c ≤ a) (haσ : a ≤ σ) :
    Integrable fun y : ℝ => F (a + y * I) := by
  refine (integrable_inv_one_add_sq.const_mul B).mono'
      (continuous_line hF hca haσ).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h := hbound _ (mem_strip_line hca haσ y)
  have him : ((a : ℂ) + y * I).im = y := by simp
  rw [him] at h
  exact h.trans (div_pow_le_mul_inv hB y)

private theorem norm_horizontal_le (hcσ : c ≤ σ) (hbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ B /
    (1 + |s.im|) ^ 2) (T : ℝ) :
    ‖∫ x : ℝ in c..σ, F (x + T * I)‖ ≤ B / (1 + |T|) ^ 2 * |σ - c| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hcσ] at hx
  have hs : ((x : ℂ) + T * I) ∈ strip c σ := by simp [strip, hx.1.le, hx.2]
  have h := hbound _ hs
  have him : ((x : ℂ) + T * I).im = T := by simp
  rwa [him] at h

private theorem tendsto_horizontal_top (hcσ : c ≤ σ)
    (hbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ B / (1 + |s.im|) ^ 2) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in c..σ, F (x + T * I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => B / (1 + |T|) ^ 2 * |σ - c|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (1 + |T|) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _
          tendsto_abs_atTop_atTop)
    simpa using (h1.const_div_atTop B).mul_const |σ - c|
  refine squeeze_zero_norm (fun T => norm_horizontal_le hcσ hbound T) hlim

private theorem tendsto_horizontal_bot (hcσ : c ≤ σ)
    (hbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ B / (1 + |s.im|) ^ 2) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in c..σ, F (x + (-T : ℝ) * I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => B / (1 + |(-T : ℝ)|) ^ 2 * |σ - c|) atTop (𝓝 0) := by
    simp only [abs_neg]
    have h1 : Tendsto (fun T : ℝ => (1 + |T|) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _
          tendsto_abs_atTop_atTop)
    simpa using (h1.const_div_atTop B).mul_const |σ - c|
  exact squeeze_zero_norm (fun T => norm_horizontal_le hcσ hbound (-T)) hlim

private theorem integral_line_eq (hcσ : c ≤ σ) (hF : DifferentiableOn ℂ F (strip c σ)) (hB : 0 ≤ B)
    (hbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ B / (1 + |s.im|) ^ 2) :
    ∫ y : ℝ, F (σ + y * I) = ∫ y : ℝ, F (c + y * I) := by
  have hFc : ContinuousOn F (strip c σ) := hF.continuousOn
  have hiσ := integrable_line hFc hB hbound hcσ le_rfl
  have hic := integrable_line hFc hB hbound le_rfl hcσ
  have hII : I * I = -1 := I_mul_I

  have rect : ∀ T : ℝ, 0 ≤ T →
      (∫ y : ℝ in (-T)..T, F (σ + y * I)) - (∫ y : ℝ in (-T)..T, F (c + y * I)) =
        I * ((∫ x : ℝ in c..σ, F (x + (-T : ℝ) * I)) - ∫ x : ℝ in c..σ, F (x + T * I)) := by
    intro T hT
    have hsub : Set.uIcc (⟨c, -T⟩ : ℂ).re (⟨σ, T⟩ : ℂ).re ×ℂ Set.uIcc (⟨c, -T⟩ : ℂ).im
        (⟨σ, T⟩ : ℂ).im ⊆
        strip c σ := by
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      have h1 : z.re ∈ Set.uIcc c σ := hz.1
      rw [Set.uIcc_of_le hcσ] at h1
      exact ⟨h1.1, h1.2⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ⟨c, -T⟩ ⟨σ, T⟩
        (hF.mono hsub)
    simp only [smul_eq_mul] at h

    linear_combination (-I) * h +
      ((∫ y : ℝ in (-T)..T, F (σ + y * I)) - ∫ y : ℝ in (-T)..T, F (c + y * I)) * hII
  have hV : Tendsto (fun T : ℝ => (∫ y : ℝ in (-T)..T, F (σ + y * I)) - ∫ y : ℝ in (-T)..T, F
      (c + y * I))
      atTop (𝓝 ((∫ y : ℝ, F (σ + y * I)) - ∫ y : ℝ, F (c + y * I))) :=
    (intervalIntegral_tendsto_integral hiσ tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hic tendsto_neg_atTop_atBot tendsto_id)
  have hH : Tendsto (fun T : ℝ => I * ((∫ x : ℝ in c..σ, F (x + (-T : ℝ) * I)) - ∫ x : ℝ in c..σ, F
      (x + T * I)))
      atTop (𝓝 (I * (0 - 0))) :=
    ((tendsto_horizontal_bot hcσ hbound).sub (tendsto_horizontal_top hcσ hbound)).const_mul I
  have hV' : Tendsto (fun T : ℝ => (∫ y : ℝ in (-T)..T, F (σ + y * I)) - ∫ y : ℝ in (-T)..T, F
      (c + y * I))
      atTop (𝓝 (I * (0 - 0))) :=
    hH.congr' ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => (rect T hT).symm)
  have := tendsto_nhds_unique hV hV'
  rw [sub_zero, mul_zero, sub_eq_zero] at this
  exact this

end line

private def inversionConst : ℝ := (1 / (2 * π)) * ∫ y : ℝ, (1 + y ^ 2)⁻¹

private theorem norm_mellinInv_le {c σ : ℝ} (hcσ : c ≤ σ) {Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (strip c σ)) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ s ∈ strip c σ, ‖Ψ s‖ ≤ B / (1 + |s.im|) ^ 2) {x : ℝ} (hx : 0 < x) :
    ‖mellinInv σ Ψ x‖ ≤ inversionConst * B * x ^ (-c) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'

  set F : ℂ → ℂ := fun s => (x : ℂ) ^ (-s) • Ψ s with hFdef
  have hFd : DifferentiableOn ℂ F (strip c σ) :=
    ((differentiable_neg.const_cpow (Or.inl hx0)).differentiableOn).smul hΨ
  have hnormw : ∀ s : ℂ, ‖(x : ℂ) ^ (-s)‖ = x ^ (-s.re) := fun s => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  have hwle : ∀ s ∈ strip c σ, x ^ (-s.re) ≤ max (x ^ (-c)) (x ^ (-σ)) := by
    intro s hs
    rcases le_total x 1 with hx1 | hx1
    ·
      exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (neg_le_neg hs.2)).trans (le_max_right _ _)
    ·
      exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hs.1)).trans (le_max_left _ _)
  have hFbound : ∀ s ∈ strip c σ, ‖F s‖ ≤ max (x ^ (-c)) (x ^ (-σ)) * B / (1 + |s.im|) ^ 2 := by
    intro s hs
    simp only [hFdef, smul_eq_mul, norm_mul, hnormw]
    rw [mul_div_assoc]
    exact mul_le_mul (hwle s hs) (hbound s hs) (norm_nonneg _) (le_max_of_le_left (by positivity))
  have hB' : 0 ≤ max (x ^ (-c)) (x ^ (-σ)) * B := mul_nonneg (le_max_of_le_left (by positivity)) hB

  have hshift : ∫ y : ℝ, F (σ + y * I) = ∫ y : ℝ, F
      (c + y * I) := integral_line_eq hcσ hFd hB' hFbound
  have hmi : mellinInv σ Ψ x = (1 / (2 * π)) • ∫ y : ℝ, F (c + y * I) := by

    rw [← hshift, hFdef]
    rfl

  have hline : ∀ y : ℝ, ‖F (c + y * I)‖ ≤ x ^ (-c) * B * (1 + y ^ 2)⁻¹ := by
    intro y
    simp only [hFdef, smul_eq_mul, norm_mul, hnormw]
    have hre : ((c : ℂ) + y * I).re = c := by simp
    have him : ((c : ℂ) + y * I).im = y := by simp
    rw [hre]
    have h := hbound _ (mem_strip_line le_rfl hcσ y)
    rw [him] at h
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.trans (div_pow_le_mul_inv hB y)) (by positivity)
  have hint : ‖∫ y : ℝ, F (c + y * I)‖ ≤ x ^ (-c) * B * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        (Eventually.of_forall hline)
  rw [hmi, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (by positivity : (0 : ℝ) ≤ 1 / (2 * π))]
  calc 1 / (2 * π) * ‖∫ y : ℝ, F (c + y * I)‖ ≤ 1 / (2 * π) *
         (x ^ (-c) * B * ∫ y : ℝ, (1 + y ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = inversionConst * B * x ^ (-c) := by unfold inversionConst; ring

private theorem norm_le_of_mellin_strip {c σ : ℝ} (hcσ : c ≤ σ) {g : ℝ → ℂ}
    (hg : MellinConvergent g σ) {Ψ : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (strip c σ)) (hΨg : ∀ y : ℝ, Ψ (σ + y * I) = mellin g (σ + y * I))
        {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ s ∈ strip c σ, ‖Ψ s‖ ≤ B / (1 + |s.im|) ^ 2) {x : ℝ} (hx : 0 < x)
    (hgx : ContinuousAt g x) :
    ‖g x‖ ≤ inversionConst * B * x ^ (-c) := by
  have hvert : VerticalIntegrable (mellin g) σ := by
    refine (integrable_line hΨ.continuousOn hB hbound hcσ le_rfl).congr
        (Eventually.of_forall fun y => ?_)
    exact hΨg y
  have hinv : mellinInv σ (mellin g) x = g x := mellinInv_mellin_eq σ g hx hg hvert hgx
  have hcongr : mellinInv σ (mellin g) x = mellinInv σ Ψ x := by
    unfold mellinInv
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => by simp only [hΨg y])
  rw [← hinv, hcongr]
  exact norm_mellinInv_le hcσ hΨ hB hbound hx

private theorem norm_le_of_parity {f : ℝ → ℂ} {c B₀ B₁ : ℝ}
    (h₀ : ∀ t : ℝ, 0 < t → ‖f t + f (-t)‖ ≤ B₀ * t ^ (-c))
        (h₁ : ∀ t : ℝ, 0 < t → ‖f t - f (-t)‖ ≤ B₁ * t ^ (-c))
    {t : ℝ} (ht : t ≠ 0) : ‖f t‖ ≤ (B₀ + B₁) / 2 * |t| ^ (-c) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  ·
    have hu : 0 < -t := by linarith
    have e : f t = ((f (-t) + f (-(-t))) - (f (-t) - f (-(-t)))) / 2 := by rw [neg_neg]; ring
    rw [e, norm_div, Complex.norm_ofNat, abs_of_neg hneg]
    have := norm_sub_le (f (-t) + f (-(-t))) (f (-t) - f (-(-t)))
    calc ‖f (-t) + f (-(-t)) - (f (-t) - f (-(-t)))‖ / 2
        ≤ (B₀ * (-t) ^ (-c) + B₁ * (-t) ^ (-c)) / 2 := by
          gcongr
          exact this.trans (add_le_add (h₀ _ hu) (h₁ _ hu))
      _ = (B₀ + B₁) / 2 * (-t) ^ (-c) := by ring
  · have e : f t = ((f t + f (-t)) + (f t - f (-t))) / 2 := by ring
    rw [e, norm_div, Complex.norm_ofNat, abs_of_pos hpos]
    have := norm_add_le (f t + f (-t)) (f t - f (-t))
    calc ‖f t + f (-t) + (f t - f (-t))‖ / 2 ≤ (B₀ * t ^ (-c) + B₁ * t ^ (-c)) / 2 := by
          gcongr
          exact this.trans (add_le_add (h₀ _ hpos) (h₁ _ hpos))
      _ = (B₀ + B₁) / 2 * t ^ (-c) := by ring

end ArchWhittakerGrowth.Inversion

end
end SpanInversion

section SpanInversionR
set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open LanglandsTunnell LanglandsTunnell.Converse

namespace ArchWhittakerGrowth
namespace InversionR

open LShift Inversion ZetaR GroupR IntegralR

private def sgn (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

private theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

private theorem sgn_one : sgn 1 = -1 := by simp [sgn]

private theorem quasiChar_zero_of_pos (a : ZMod 2) {t : ℝ}
    (ht : 0 < t) : ArchR.quasiChar 0 a t = 1 := by
  unfold ArchR.quasiChar
  rw [Complex.cpow_zero, one_mul, sign_pos ht]
  split_ifs <;> simp

private theorem quasiChar_zero_of_neg (a : ZMod 2) {t : ℝ}
    (ht : t < 0) : ArchR.quasiChar 0 a t = sgn a := by
  unfold ArchR.quasiChar sgn
  rw [Complex.cpow_zero, one_mul, sign_neg ht]
  split_ifs <;> simp

private theorem zw_zero_of_pos (a : ZMod 2) (s : ℂ) {t : ℝ} (ht : 0 < t) : zw 0 a s t = (t : ℂ) ^
    (s - 1 - 1) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold zw
  rw [quasiChar_zero_of_pos a ht, one_mul, abs_of_pos ht,
    show (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 1) / (t : ℂ) ^
        (1 : ℂ) from Complex.cpow_sub _ _ ht0, Complex.cpow_one,
    div_eq_mul_inv]

private theorem zw_zero_of_neg (a : ZMod 2) (s : ℂ) {t : ℝ} (ht : 0 < t) : zw 0 a s (-t) = sgn a *
    (t : ℂ) ^ (s - 1 - 1) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold zw
  rw [quasiChar_zero_of_neg a (neg_neg_of_pos ht), abs_neg, abs_of_pos ht,
    show (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 1) / (t : ℂ) ^
        (1 : ℂ) from Complex.cpow_sub _ _ ht0, Complex.cpow_one,
    div_eq_mul_inv, mul_assoc]

variable {P : RealArchParam}

private def fold (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) (a : ZMod 2) (t : ℝ) : ℂ :=
  d.W (ArchR.diagOne t * k) + sgn a * d.W (ArchR.diagOne (-t) * k)

private theorem fold_zero_apply (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    fold d k 0 t = d.W (ArchR.diagOne t * k) + d.W (ArchR.diagOne (-t) * k) := by
  rw [fold, sgn_zero, one_mul]

private theorem fold_one_apply (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    fold d k 1 t = d.W (ArchR.diagOne t * k) - d.W (ArchR.diagOne (-t) * k) := by
  rw [fold, sgn_one, neg_one_mul, sub_eq_add_neg]

private theorem zetaIntegrand_neg_add (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) (a : ZMod 2)
    (s : ℂ) {t : ℝ}
    (ht : 0 < t) :
    ArchR.zetaIntegrand d.W k 0 a s (-t) + ArchR.zetaIntegrand d.W k 0 a s t =
      (t : ℂ) ^ (s - 1 - 1) • fold d k a t := by
  rw [zetaIntegrand_eq, zetaIntegrand_eq, zw_zero_of_pos a s ht, zw_zero_of_neg a s ht, fold,
      smul_eq_mul]
  ring

private theorem integral_zetaIntegrand_eq_mellin (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ)
    (a : ZMod 2) (s : ℂ)
    (hi : Integrable (ArchR.zetaIntegrand d.W k 0 a s)) :
    ∫ y : ℝ, ArchR.zetaIntegrand d.W k 0 a s y = mellin (fold d k a) (s - 1) := by
  have hneg : Integrable fun y : ℝ => ArchR.zetaIntegrand d.W k 0 a s (-y) := hi.comp_neg
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hi.integrableOn hi.integrableOn,
      mellin]
  have h1 : ∫ y : ℝ in Iic (0 : ℝ), ArchR.zetaIntegrand d.W k 0 a s y =
      ∫ y : ℝ in Ioi (0 : ℝ), ArchR.zetaIntegrand d.W k 0 a s (-y) := by
    rw [integral_comp_neg_Ioi, neg_zero]
  rw [h1, ← integral_add hneg.integrableOn hi.integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact zetaIntegrand_neg_add d k a s ht

private theorem mellinConvergent_fold (d : ArchDatumR P) {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : k.det ≠ 0) (a : ZMod 2)
    {σ : ℝ} (hσ : d.zeta_abscissa < σ + 1) : MellinConvergent (fold d k a) σ := by
  have habs : d.zeta_abscissa < ((σ : ℂ) + 1).re + (0 : ℂ).re := by simpa using hσ
  have hi := d.zeta_integrable k 0 a ((σ : ℂ) + 1) hk habs
  have hneg : Integrable fun y : ℝ => ArchR.zetaIntegrand d.W k 0 a ((σ : ℂ) + 1)
      (-y) := hi.comp_neg
  refine (hneg.integrableOn.add hi.integrableOn).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have h := zetaIntegrand_neg_add d k a ((σ : ℂ) + 1) (ht : 0 < t)
  rw [add_sub_cancel_right] at h
  exact h

private def lphi (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) (a : ZMod 2) (w : ℂ) : ℂ :=
  (P.twist 0 a).archFactor (w + 1) * d.zetaEntire k 0 a (w + 1)

private theorem lphi_eq_mellin_fold (d : ArchDatumR P) {k : Matrix (Fin 2) (Fin 2) ℝ}
    (hk : k.det ≠ 0) (a : ZMod 2)
    {σ : ℝ} (hσ : d.zeta_abscissa < σ + 1) (y : ℝ) :
    lphi d k a (σ + y * I) = mellin (fold d k a) (σ + y * I) := by
  set w : ℂ := σ + y * I with hw
  have habs : d.zeta_abscissa < (w + 1).re + (0 : ℂ).re := by simp [hw]; linarith
  have hi := d.zeta_integrable k 0 a (w + 1) hk habs
  have heq := d.zeta_eq k 0 a (w + 1) hk habs
  rw [lphi, ← heq, integral_zetaIntegrand_eq_mellin d k a (w + 1) hi, add_sub_cancel_right]

private theorem differentiableOn_gammaFactor {R C : Multiset ℂ} {A : ℝ} (hR : ∀ μ ∈ R, 0 < A + μ.re)
    (hC : ∀ ν ∈ C, 0 < A + ν.re) : DifferentiableOn ℂ (gammaFactor R C) {s : ℂ | A ≤ s.re} := by
  unfold gammaFactor
  refine (differentiableOn_prod _ R (fun μ s => Gammaℝ (s + μ)) fun μ hμ => ?_).mul
    (differentiableOn_prod _ C (fun ν s => Gammaℂ (s + ν)) fun ν hν => ?_)
  · intro s hs
    have hre : 0 < (s + μ).re := by
      simp only [Set.mem_setOf_eq] at hs
      have := hR μ hμ
      simp; linarith
    exact ((differentiableAt_Gammaℝ_of_re_pos hre).comp s
        (differentiableAt_id.add_const μ)).differentiableWithinAt
  · intro s hs
    have hre : 0 < (s + ν).re := by
      simp only [Set.mem_setOf_eq] at hs
      have := hC ν hν
      simp; linarith
    exact ((differentiableAt_Gammaℂ_of_re_pos hre).comp s
        (differentiableAt_id.add_const ν)).differentiableWithinAt

private theorem differentiableOn_lphi (d : ArchDatumR P) (k : Matrix (Fin 2) (Fin 2) ℝ) {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (a : ZMod 2) (σ : ℝ) : DifferentiableOn ℂ (lphi d k a) (Inversion.strip (c₀ - 1) σ) := by
  have hG := differentiableOn_gammaFactor (pos_of_hc₀R hc₀ a) (pos_of_hc₀C hc₀ a)
  have hmaps : MapsTo (fun w : ℂ => w + 1) (Inversion.strip (c₀ - 1) σ) {s : ℂ | c₀ ≤ s.re} := by
    intro w hw
    have h1 : c₀ - 1 ≤ w.re := hw.1
    show c₀ ≤ (w + 1).re
    simp; linarith
  have h1 : DifferentiableOn ℂ (fun w : ℂ => (P.twist 0 a).archFactor (w + 1))
      (Inversion.strip (c₀ - 1) σ) := by
    simp only [archFactor_eq]
    exact hG.comp (differentiable_id.add_const (1 : ℂ)).differentiableOn hmaps
  have h2 : DifferentiableOn ℂ (fun w : ℂ => d.zetaEntire k 0 a (w + 1))
      (Inversion.strip (c₀ - 1) σ) :=
    ((d.zetaEntire_differentiable k 0 a).comp (differentiable_id.add_const
        (1 : ℂ))).differentiableOn
  exact h1.mul h2

private theorem _root_.ArchWhittakerGrowth.InversionR.continuousOn_orbit (d : ArchDatumR P)
    {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : k.det ≠ 0) :
    ContinuousOn (fun t : ℝ => d.W (ArchR.diagOne t * k)) {0}ᶜ := by
  have h := continuousOn_defo_value d.W d.smooth hk (0 : Matrix (Fin 2) (Fin 2) ℝ) (τ := 0)
      (by simp)
  simpa only [defo_zero] using h

private theorem continuousAt_fold (d : ArchDatumR P) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : k.det ≠ 0)
    (a : ZMod 2) {t : ℝ}
    (ht : 0 < t) : ContinuousAt (fold d k a) t := by
  have hW := continuousOn_orbit d hk
  have h1 : ContinuousAt (fun t : ℝ => d.W (ArchR.diagOne t * k)) t :=
    hW.continuousAt (isOpen_compl_singleton.mem_nhds ht.ne')
  have h2 : ContinuousAt (fun t : ℝ => d.W (ArchR.diagOne (-t) * k)) t := by
    have hneg : ContinuousAt (fun t : ℝ => d.W (ArchR.diagOne t * k)) (-t) :=
      hW.continuousAt (isOpen_compl_singleton.mem_nhds (neg_ne_zero.2 ht.ne'))
    exact hneg.comp continuous_neg.continuousAt
  exact h1.add (h2.const_mul _)

private theorem exists_norm_fold_le (d : ArchDatumR P) (hZ : EdgeDecay d) {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (a : ZMod 2) :
    ∃ B : ℝ, ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k → ∀ t : ℝ, 0 < t →
      ‖fold d k a t‖ ≤ B * t ^ (-(c₀ - 1)) := by

  set σ₁ : ℝ := max c₀ (d.zeta_abscissa + 1) with hσ₁def
  have hcσ₁ : c₀ ≤ σ₁ := le_max_left _ _
  have habs : d.zeta_abscissa < (σ₁ - 1) + 1 := by
    have := le_max_right c₀ (d.zeta_abscissa + 1)
    linarith
  obtain ⟨C, hC⟩ := strip_decay d hZ hc₀ a hcσ₁ 2
  refine ⟨inversionConst * max C 0, fun k hk t ht => ?_⟩
  have hdet : k.det ≠ 0 := isK_det_ne_zero hk

  have hbound : ∀ w ∈ Inversion.strip (c₀ - 1) (σ₁ - 1), ‖lphi d k a w‖ ≤ max C 0 /
      (1 + |w.im|) ^ 2 := by
    intro w hw
    have h := hC k hk (w + 1) (by have := hw.1; simp; linarith) (by have := hw.2; simp; linarith)
    have him : (w + 1).im = w.im := by simp
    rw [him] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hconv : MellinConvergent (fold d k a) (σ₁ - 1 : ℝ) := mellinConvergent_fold d hdet a habs
  have hline : ∀ y : ℝ, lphi d k a ((σ₁ - 1 : ℝ) + y * I) = mellin (fold d k a)
      ((σ₁ - 1 : ℝ) + y * I) :=
    fun y => lphi_eq_mellin_fold d hdet a habs y
  exact norm_le_of_mellin_strip (sub_le_sub_right hcσ₁ 1) hconv
      (differentiableOn_lphi d k hc₀ a (σ₁ - 1)) hline
    (le_max_right _ _) hbound ht (continuousAt_fold d hdet a ht)

private theorem norm_W_diagOne_mul_le (d : ArchDatumR P) (hZ : EdgeDecay d) {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀)) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖d.W (ArchR.diagOne y * k)‖ ≤ C * |y| ^ (1 - c₀) := by
  obtain ⟨B₀, hB₀⟩ := exists_norm_fold_le d hZ hc₀ 0
  obtain ⟨B₁, hB₁⟩ := exists_norm_fold_le d hZ hc₀ 1
  refine ⟨(B₀ + B₁) / 2, fun y k hk hy => ?_⟩
  have h := norm_le_of_parity (f := fun t : ℝ => d.W (ArchR.diagOne t * k)) (c := c₀ - 1)
    (fun t ht => by simpa only [fold_zero_apply] using hB₀ k hk t ht)
    (fun t ht => by simpa only [fold_one_apply] using hB₁ k hk t ht) hy
  rwa [neg_sub] at h

end ArchWhittakerGrowth.InversionR

end
end SpanInversionR

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
    simp only [mem_preimage, mem_Ioo] at hs; simp only [mem_setOf_eq]; linarith [hs.1]
  have hclos_sub : closure (Complex.re ⁻¹' Ioo A B) ⊆ {s : ℂ | A - 1 < s.re} := by
    refine (Complex.continuous_re.closure_preimage_subset _).trans fun s hs => ?_
    rw [closure_Ioo hAB.ne, mem_preimage, mem_Icc] at hs
    simp only [mem_setOf_eq]; linarith [hs.1]
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
    have hsA' : A ≤ s.re := by rcases hs with h | h; exact h.ge; rw [h]; exact hAB.le
    have hsB' : s.re ≤ B := by rcases hs with h | h; rw [h]; exact hAB.le; exact h.le
    have hpoly : ‖shiftPoly R C N s‖ ≤ max Kp 0 * (1 + |s.im|) ^ deg :=
      (hKp s hsA' hsB').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hγΦ : ‖gammaFactor R C s * Φ s‖ ≤ max 1 Kd * M := by
      rcases hs with h | h
      ·
        rw [norm_mul]
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
  ·
    obtain ⟨K₁, hK₁, hdom1⟩ := exists_dirDeriv_domination (leftLaws_datum d) d.smooth hC₁ hσ0
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
  ·
    set ε' : ℝ := ε / (K + 1) with hε'
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
  ·
    refine ⟨K * max (max MbR (‖Q.epsilonFactor‖⁻¹ * MbL)) 0, min (min δR δL) t₁, lt_min
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
  rw [if_neg hg]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_dq d hg X u a s))

private theorem zetaEntire'_of_det_eq_zero (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det = 0) (u : ℂ) (a : ZMod 2) : zetaEntire' d X g u a = fun _ => 0 := by
  funext s; unfold zetaEntire'; rw [if_pos hg]

private theorem tendstoLocallyUniformlyOn_dq (d : ArchDatumR P) {g : Matrix (Fin 2) (Fin 2) ℝ}
    (hg : g.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) :
    TendstoLocallyUniformlyOn (fun n s => dq d g X u a (hseq n) s)
        (zetaEntire' d X g u a) atTop univ := by

  have hcover : (univ : Set ℂ) = ⋃ m : ℕ, {s : ℂ | |s.re| < m ∧ |s.im| < m} := by
    ext s
    simp only [mem_univ, mem_iUnion, mem_setOf_eq, true_iff]
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

@[scoped simp] private theorem derivDatum_W (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
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

section SpanWordDatumR
set_option autoImplicit false

noncomputable section

open Complex

namespace ArchWhittakerGrowth

namespace WordDatumR

open LanglandsTunnell LanglandsTunnell.Converse
open ArchWhittakerGrowth.GroupR ArchWhittakerGrowth.DerivR ArchWhittakerGrowth.IntegralR
    ArchWhittakerGrowth.DatumR
open ArchWhittakerGrowth.ZetaInt ArchWhittakerGrowth.InversionR

variable {P : RealArchParam}

private def wordDatum {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) ℝ) : {j : ℕ} → (Fin j → ι) →
    ArchDatumR P → ArchDatumR P
  | 0, _, d => d
  | j + 1, I, d => wordDatum E (fun i : Fin j => I i.succ) (derivDatum d (E (I 0)))

private theorem rightDeriv_congr {F G : (Fin 2 → Fin 2 → ℝ) → ℂ} (h : Set.EqOn F G ArchR.glSet)
    (X : Matrix (Fin 2) (Fin 2) ℝ) : Set.EqOn (rightDeriv X F) (rightDeriv X G) ArchR.glSet := by
  intro p hp
  unfold rightDeriv
  rw [glSet_eq] at h hp
  rw [fderivWithin_congr h (h hp)]

private theorem wordDeriv_congr {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ {j : ℕ} (I : Fin j → ι) {F G : (Fin 2 → Fin 2 → ℝ) → ℂ}, Set.EqOn F G ArchR.glSet →
      Set.EqOn (wordDeriv E I F) (wordDeriv E I G) ArchR.glSet
  | 0, I, F, G, h => by simpa only [wordDeriv_zero] using h
  | j + 1, I, F, G, h => by
      intro p hp
      simp only [wordDeriv]
      exact wordDeriv_congr E (fun i : Fin j => I i.succ) (rightDeriv_congr h (E (I 0))) hp

private theorem wordDeriv_asPi {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ {j : ℕ} (I : Fin j → ι) (d : ArchDatumR P),
      Set.EqOn (wordDeriv E I (ArchR.asPi d.W)) (ArchR.asPi (wordDatum E I d).W) ArchR.glSet
  | 0, I, d => by
      intro p _
      simp only [wordDeriv_zero, wordDatum]
  | j + 1, I, d => by
      intro p hp
      simp only [wordDeriv, wordDatum]
      have h1 : Set.EqOn (rightDeriv (E (I 0)) (ArchR.asPi d.W))
          (ArchR.asPi (derivDatum d (E (I 0))).W)
          ArchR.glSet := fun q hq => by
        rw [derivDatum_W]; exact (asPi_derivW_eqOn (E (I 0)) d.W hq).symm
      rw [wordDeriv_congr E (fun i : Fin j => I i.succ) h1 hp]
      exact wordDeriv_asPi E (fun i : Fin j => I i.succ) (derivDatum d (E (I 0))) hp

private theorem norm_wordDeriv_le {ι : Type} (E : ι → Matrix (Fin 2) (Fin 2) ℝ) {j : ℕ}
    (I : Fin j → ι) (d : ArchDatumR P)
    {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      ‖wordDeriv E I (ArchR.asPi d.W) (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^ (1 - c₀) := by
  obtain ⟨C, hC⟩ := norm_W_diagOne_mul_le (wordDatum E I d) (edgeDecay _) hc₀
  refine ⟨max C 0, le_max_right _ _, fun y k hk hy => ?_⟩
  rw [wordDeriv_asPi E I d (IntegralR.diagOneMulCoords_mem hk hy)]
  calc ‖ArchR.asPi (wordDatum E I d).W (ArchR.diagOneMulCoords y k)‖
      = ‖(wordDatum E I d).W (ArchR.diagOne y * k)‖ := rfl
    _ ≤ C * |y| ^ (1 - c₀) := hC y k hk hy
    _ ≤ max C 0 * |y| ^ (1 - c₀) := mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (abs_nonneg _) _)

private theorem wordSum_le (d : ArchDatumR P) {c₀ : ℝ}
    (hc₀ : ∀ a : ZMod 2, (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧
        (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (M : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 →
      wordSum lettersR M (ArchR.asPi d.W) (ArchR.diagOneMulCoords y k) ≤ C * |y| ^ (1 - c₀) := by
  classical

  have hword : ∀ (j : ℕ) (I : Fin j → Fin 2 × Fin 2), ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ)
      (k : Matrix (Fin 2) (Fin 2) ℝ),
      ArchR.IsK k → y ≠ 0 →
        ‖wordDeriv lettersR I (ArchR.asPi d.W) (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^ (1 - c₀) :=
    fun j I => norm_wordDeriv_le lettersR I d hc₀
  choose Cw hCw0 hCw using hword
  refine ⟨∑ j ∈ Finset.range (M + 1), ∑ I : Fin j → Fin 2 × Fin 2, Cw j I, fun y k hk hy => ?_⟩
  unfold wordSum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun I _ => hCw j I y k hk hy

private theorem main (P : RealArchParam) (d : ArchDatumR P) (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 a).gammaC, -ν.re < c₀))
    (M : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ M (ArchR.asPi d.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (1 - c₀ - (M : ℝ)) := by
  obtain ⟨C₇, hC₇⟩ := norm_iteratedFDerivWithin_diagOneMulCoords_le_real M
  obtain ⟨C₀, hC₀⟩ := wordSum_le d hc₀ M
  refine ⟨max C₇ 0 * C₀, fun y k hk hy hy1 => ?_⟩
  have hface := hC₇ (ArchR.asPi d.W) d.smooth y k hk hy hy1
  have hws := hC₀ y k hk hy
  have hpow : 0 ≤ |y| ^ (-(M : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  have hwsnn : 0 ≤ wordSum lettersR M (ArchR.asPi d.W)
      (ArchR.diagOneMulCoords y k) := wordSum_nonneg _ _ _ _
  have hexp : |y| ^ (-(M : ℝ)) * |y| ^ (1 - c₀) = |y| ^ (1 - c₀ - (M : ℝ)) := by
    rw [← Real.rpow_add (abs_pos.2 hy)]; ring_nf
  calc ‖iteratedFDerivWithin ℝ M (ArchR.asPi d.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
      ≤ C₇ * |y| ^ (-(M : ℝ)) * wordSum lettersR M (ArchR.asPi d.W)
          (ArchR.diagOneMulCoords y k) := hface
    _ ≤ max C₇ 0 * |y| ^ (-(M : ℝ)) * wordSum lettersR M (ArchR.asPi d.W)
        (ArchR.diagOneMulCoords y k) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C₇ 0 * |y| ^ (-(M : ℝ)) * (C₀ * |y| ^ (1 - c₀)) :=
        mul_le_mul_of_nonneg_left hws (mul_nonneg (le_max_right _ _) hpow)
    _ = max C₇ 0 * C₀ * (|y| ^ (-(M : ℝ)) * |y| ^ (1 - c₀)) := by ring
    _ = max C₇ 0 * C₀ * |y| ^ (1 - c₀ - (M : ℝ)) := by rw [hexp]

end WordDatumR

end ArchWhittakerGrowth

end
end SpanWordDatumR

open LanglandsTunnell LanglandsTunnell.Converse in
/-- The right derivative along `X` of the Whittaker function of a real archimedean
Whittaker datum, `g ↦ D W(g) (g X)` on invertible matrices, is the Whittaker function of
another real archimedean Whittaker datum. -/
theorem LanglandsTunnell.Converse.ArchDatumR.exists_W_eq_fderivWithin_mul
    (P : RealArchParam) (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet (Matrix.of.symm g)
          (Matrix.of.symm (g * X)) := by
  exact ArchWhittakerGrowth.DatumR.exists_derivDatum d X
