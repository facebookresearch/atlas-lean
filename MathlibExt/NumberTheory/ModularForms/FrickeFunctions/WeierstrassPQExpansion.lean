/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean`
and
`P2M/Sol/S_WLight_weierstrassP_qExpansion_package.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# q-expansions of the Weierstrass function at torsion points

This file proves Lipschitz-type summation formulas and the q-expansion of the Weierstrass
function of the lattice `ℤτ + ℤ` at torsion points.

## Main statement

* `ModularForm.weierstrassP_qExpansion_package`
-/
namespace FrickeFunctions.WeierstrassPQExpansion

noncomputable section

open Complex Real

namespace Aux

section B1_homogeneity

open PeriodPair

private def smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := LinearIndependent.pair_iff.mpr fun s t hst => by
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have h0 : a * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]; exact hst
    exact (mul_eq_zero.mp h0).resolve_left ha

@[scoped simp] private lemma smulPeriodPair_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₁ = a * L.ω₁ := rfl

@[scoped simp] private lemma smulPeriodPair_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₂ = a * L.ω₂ := rfl

private lemma mem_smulPeriodPair_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {x : ℂ} :
    x ∈ (smulPeriodPair a ha L).lattice ↔ ∃ y ∈ L.lattice, x = a * y := by
  simp only [mem_lattice, smulPeriodPair_ω₁, smulPeriodPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by rw [← h]; ring⟩
  · rintro ⟨y, ⟨m, n, h⟩, rfl⟩
    exact ⟨m, n, by rw [← h]; ring⟩

private def smulLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smulPeriodPair a ha L).lattice where
  toFun l := ⟨a * l, (mem_smulPeriodPair_lattice ha L).mpr ⟨l, l.2, rfl⟩⟩
  invFun l := ⟨a⁻¹ * l, by
    obtain ⟨y, hy, hxy⟩ := (mem_smulPeriodPair_lattice ha L).mp l.2
    rw [hxy, inv_mul_cancel_left₀ ha]; exact hy⟩
  left_inv l := Subtype.ext (inv_mul_cancel_left₀ ha _)
  right_inv l := Subtype.ext (mul_inv_cancel_left₀ ha _)

@[scoped simp] private lemma smulLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (l :
    L.lattice) :
    ((smulLatticeEquiv a ha L) l : ℂ) = a * l := rfl

private theorem weierstrassP_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassP (smulPeriodPair a ha L) (a * z) = a⁻¹ ^ 2 * weierstrassP L z := by
  have key : ∀ u : ℂ, 1 / (a * u) ^ 2 = a⁻¹ ^ 2 * (1 / u ^ 2) := fun u => by
    simp [one_div, mul_pow, inv_pow, mul_comm]
  simp only [weierstrassP]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe]
  rw [show a * z - a * (l : ℂ) = a * (z - l) by ring, key, key, mul_sub]

end B1_homogeneity

section B2_lipschitz

private theorem summable_one_div_add_int_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w + n) ^ 2 := by
  simpa [one_div] using EisensteinSeries.linear_right_summable w 1 (k := 2) le_rfl

private theorem tsum_one_div_add_int_sq_neg (w : ℂ) :
    ∑' n : ℤ, 1 / (-w + n) ^ 2 = ∑' n : ℤ, 1 / (w + n) ^ 2 := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

private theorem tsum_one_div_sub_int_sq (w : ℂ) :
    ∑' n : ℤ, 1 / (w - n) ^ 2 = ∑' n : ℤ, 1 / (w + n) ^ 2 := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [sub_eq_add_neg]

private theorem lipschitz_two_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨w, hw⟩
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h]
  ring

private theorem lipschitz_two_of_im_neg {w : ℂ} (hw : w.im < 0) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m := by
  rw [← tsum_one_div_add_int_sq_neg, lipschitz_two_of_im_pos (w := -w) (by simpa using hw)]
  simp [mul_neg]

private theorem summable_nat_mul_cexp_pow {w : ℂ} (hw : 0 < w.im) :
    Summable fun m : ℕ ↦ (m : ℂ) * cexp (2 * π * I * w) ^ m := by
  simpa using summable_pow_mul_cexp 1 1 ⟨w, hw⟩

private theorem cexp_two_pi_I_mul_ne_one {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    cexp (2 * π * I * x) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have : x = n := by
    have := congrArg (· / (2 * π * I)) hn
    simpa [mul_div_assoc, div_self h2, mul_comm] using this
  exact hx ⟨n, this.symm⟩

private theorem lipschitz_two_closed_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  rw [lipschitz_two_of_im_pos hx, tsum_coe_mul_geometric_of_norm_lt_one]
  simpa using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩

private theorem lipschitz_two_closed_of_im_neg {x : ℂ} (hx : x.im < 0) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  have hr : ‖cexp (-(2 * π * I * x))‖ < 1 := by
    simpa [mul_neg] using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-x, by simpa using hx⟩
  have hq0 : cexp (2 * π * I * x) ≠ 0 := Complex.exp_ne_zero _
  have hq1 : 1 - cexp (2 * π * I * x) ≠ 0 := by
    intro h0
    have h1 : ‖cexp (2 * π * I * x)‖ = 1 := by rw [(sub_eq_zero.mp h0).symm, norm_one]
    rw [Complex.norm_exp] at h1
    have : (2 * π * I * x).re = -(2 * π * x.im) := by simp [mul_comm]
    rw [this, Real.exp_eq_one_iff] at h1
    nlinarith [Real.pi_pos]
  have hr1 : 1 - cexp (-(2 * π * I * x)) ≠ 0 := by
    rw [Complex.exp_neg]
    intro h0
    apply hq1
    have := sub_eq_zero.mp h0
    rw [eq_comm, inv_eq_one] at this
    simp [this]
  rw [lipschitz_two_of_im_neg hx, tsum_coe_mul_geometric_of_norm_lt_one hr]
  refine congrArg₂ (· * ·) rfl ?_
  rw [Complex.exp_neg] at hr1 ⊢
  rw [div_eq_div_iff (pow_ne_zero 2 hr1) (pow_ne_zero 2 hq1)]
  field_simp
  ring

open Metric Set Filter Topology in
private theorem lipschitz_two_closed {x : ℂ} (hx : x ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (x + n) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * x) / (1 - cexp (2 * π * I * x)) ^ 2) := by
  rcases lt_trichotomy x.im 0 with h | h | h
  · exact lipschitz_two_closed_of_im_neg h
  swap
  · exact lipschitz_two_closed_of_im_pos h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_compl_range_intCast x hx
  set U : Set ℂ := ball x (ε / 2) with hUdef
  have hUsub : U ⊆ Complex.integerComplement :=
    (ball_subset_ball (half_le_self hε.le)).trans hball
  have hsep : ∀ y ∈ U, ∀ n : ℤ, ε / 2 ≤ ‖y + n‖ := by
    intro y hy n
    by_contra! hlt
    have hmem : ((-n : ℤ) : ℂ) ∈ ball x ε := by
      rw [mem_ball, dist_comm, dist_eq_norm]
      calc ‖x - ((-n : ℤ) : ℂ)‖ = ‖(x - y) + (y + n)‖ := by push_cast; ring_nf
        _ ≤ ‖x - y‖ + ‖y + n‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := by
            gcongr
            rw [← dist_eq_norm, dist_comm]; exact hy
        _ = ε := by ring
    exact hball hmem ⟨-n, rfl⟩
  have hne : ∀ y ∈ U, ∀ n : ℤ, y + n ≠ 0 := fun y hy n h0 ↦ by
    have := hsep y hy n
    rw [h0, norm_zero] at this
    linarith
  have hnormU : ∀ y ∈ U, ‖y‖ ≤ ‖x‖ + ε / 2 := by
    intro y hy
    have : ‖y - x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hy
    calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ε / 2 := by linarith
  set R : ℝ := ‖x‖ + ε / 2 with hRdef
  set K : ℕ := ⌈2 * R⌉₊ with hKdef
  set u : ℤ → ℝ := fun n ↦
    (if n ∈ Finset.Icc (-(K : ℤ)) K then 4 / ε ^ 2 else 0) + 4 * (1 / (n : ℝ) ^ 2) with hudef
  have hu : Summable u := by
    refine Summable.add ?_ ((summable_one_div_int_pow.mpr one_lt_two).mul_left 4)
    exact summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) (by intro b hb; simp [hb])
  have hbound : ∀ (n : ℤ) (y : ℂ), y ∈ U → ‖1 / (y + n) ^ 2‖ ≤ u n := by
    intro n y hy
    have hpos : 0 < ‖y + n‖ := norm_pos_iff.mpr (hne y hy n)
    rw [norm_div, norm_one, norm_pow]
    by_cases hn : n ∈ Finset.Icc (-(K : ℤ)) K
    · simp only [hudef, hn, ite_true]
      have h1 : 1 / ‖y + ↑n‖ ^ 2 ≤ 4 / ε ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        nlinarith [hsep y hy n, norm_nonneg (y + n)]
      have h2 : (0 : ℝ) ≤ 4 * (1 / (n : ℝ) ^ 2) := by positivity
      linarith
    · simp only [hudef, hn, ite_false, zero_add]
      have hnK : (K : ℝ) < |(n : ℝ)| := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        rw [← Int.cast_abs]
        rcases hn with hn | hn
        · have : (K : ℤ) < |n| := by rw [abs_of_neg (by omega)]; omega
          exact_mod_cast this
        · have : (K : ℤ) < |n| := lt_of_lt_of_le hn (le_abs_self n)
          exact_mod_cast this
      have hR2 : 2 * R ≤ K := Nat.le_ceil _
      have hyR : ‖y‖ ≤ R := hnormU y hy
      have hlow : |(n : ℝ)| / 2 ≤ ‖y + n‖ := by
        have : |(n : ℝ)| ≤ ‖y + n‖ + ‖y‖ := by
          calc |(n : ℝ)| = ‖((n : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
            _ = ‖(y + n) - y‖ := by push_cast; ring_nf
            _ ≤ ‖y + n‖ + ‖y‖ := norm_sub_le _ _
        linarith
      have hnpos : 0 < |(n : ℝ)| := by linarith [Nat.cast_nonneg (α := ℝ) K]
      rw [show (4 : ℝ) * (1 / (n : ℝ) ^ 2) = 1 / (|(n : ℝ)| / 2) ^ 2 by
        rw [div_pow, sq_abs]; field_simp; ring]
      exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hF : DifferentiableOn ℂ (fun y : ℂ ↦ ∑' n : ℤ, 1 / (y + n) ^ 2) U := by
    refine differentiableOn_tsum_of_summable_norm hu (fun n ↦ ?_) isOpen_ball hbound
    exact DifferentiableOn.fun_div (by fun_prop) (by fun_prop) fun y hy ↦ pow_ne_zero _ (hne y hy n)
  have hG : DifferentiableOn ℂ
      (fun y : ℂ ↦ (2 * π * I) ^ 2 * (cexp (2 * π * I * y) / (1 - cexp (2 * π * I * y)) ^ 2))
      U := by
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_div ?_ ?_ ?_) _
    · exact (Complex.differentiable_exp.comp (differentiable_id.const_mul _)).differentiableOn
    · exact ((differentiable_const _).sub (Complex.differentiable_exp.comp
        (differentiable_id.const_mul _))).pow 2 |>.differentiableOn
    intro y hy
    exact pow_ne_zero _ (sub_ne_zero.mpr (cexp_two_pi_I_mul_ne_one (hUsub hy)).symm)
  set z₀ : ℂ := x + (ε / 4 : ℝ) * I with hz₀def
  have hz₀U : z₀ ∈ U := by
    rw [hUdef, mem_ball, dist_eq_norm, hz₀def, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hz₀im : 0 < z₀.im := by simp [hz₀def, h, hε]
  have hfg : (fun y : ℂ ↦ ∑' n : ℤ, 1 / (y + n) ^ 2) =ᶠ[𝓝 z₀]
      (fun y : ℂ ↦ (2 * π * I) ^ 2 * (cexp (2 * π * I * y) / (1 - cexp (2 * π * I * y)) ^ 2)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (by simpa using hz₀im)] with y hy
    exact lipschitz_two_closed_of_im_pos (by simpa using hy)
  exact (hF.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd isOpen_ball) (convex_ball x _).isPreconnected hz₀U hfg
    (mem_ball_self (half_pos hε))

private theorem summable_one_div_sub_int_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w - n) ^ 2 := by
  refine (Equiv.neg ℤ).summable_iff.mp ?_
  simpa [Function.comp_def, sub_eq_add_neg] using summable_one_div_add_int_sq w

private theorem tsum_int_one_div_sq : ∑' n : ℤ, 1 / ((n : ℂ)) ^ 2 = (π : ℂ) ^ 2 / 3 := by
  have h := two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) le_rfl even_two
  simp only [Nat.cast_ofNat, riemannZeta_two] at h
  simp only [one_div, ← h]
  ring

private theorem two_pi_I_sq : (2 * π * I : ℂ) ^ 2 = -(4 * π ^ 2) := by
  rw [mul_pow, I_sq]; ring

private theorem neg_pi_sq_div_three_div : -((π : ℂ) ^ 2 / 3) = (2 * π * I) ^ 2 * (1 / 12) := by
  rw [two_pi_I_sq]; ring

private theorem tsum_row_split (z l₀ : ℂ) :
    ∑' d : ℤ, (1 / (z - (l₀ + d)) ^ 2 - 1 / (l₀ + d) ^ 2) =
      ∑' d : ℤ, 1 / ((z - l₀) + d) ^ 2 - ∑' d : ℤ, 1 / (l₀ + d) ^ 2 := by
  rw [Summable.tsum_sub _ (summable_one_div_add_int_sq l₀), ← tsum_one_div_sub_int_sq (z - l₀)]
  · exact congrArg₂ _ (tsum_congr fun d ↦ by ring_nf) rfl
  · simpa [sub_sub] using summable_one_div_sub_int_sq (z - l₀)

private theorem tsum_row_zero (z : ℂ) :
    ∑' d : ℤ, (1 / (z - d) ^ 2 - 1 / ((d : ℂ)) ^ 2) =
      ∑' d : ℤ, 1 / (z + d) ^ 2 - (π : ℂ) ^ 2 / 3 := by
  rw [Summable.tsum_sub (summable_one_div_sub_int_sq z), tsum_one_div_sub_int_sq,
    tsum_int_one_div_sq]
  simpa [one_div] using EisensteinSeries.linear_right_summable (0 : ℂ) 1 (k := 2) le_rfl

private theorem lipschitz_two_of_im_neg' {w : ℂ} (hw : w.im < 0) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * (-w)) ^ m := by
  rw [lipschitz_two_of_im_neg hw]
  simp [mul_neg]

private theorem cexp_two_pi_I_mul_add (a b : ℂ) :
    cexp (2 * π * I * (a + b)) = cexp (2 * π * I * a) * cexp (2 * π * I * b) := by
  rw [mul_add, Complex.exp_add]

private theorem cexp_two_pi_I_mul_nat_mul (c : ℕ) (τ : ℂ) :
    cexp (2 * π * I * (c * τ)) = cexp (2 * π * I * τ) ^ c := by
  rw [← Complex.exp_nat_mul]
  ring_nf

private theorem cexp_two_pi_I_mul_neg (z : ℂ) :
    cexp (2 * π * I * (-z)) = (cexp (2 * π * I * z))⁻¹ := by
  rw [mul_neg, Complex.exp_neg]

private theorem lipschitz_row_pair {z τ : ℂ} (hτ : 0 < τ.im) (hz₁ : -τ.im < z.im) (hz₂ : z.im
    < τ.im)
    {c : ℕ} (hc : 0 < c) :
    ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) +
      ((∑' d : ℤ, 1 / ((z - (-(c : ℂ)) * τ) + d) ^ 2) - ∑' d : ℤ, 1 / ((-(c : ℂ)) * τ + d) ^ 2) =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) *
        (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
          cexp (2 * π * I * τ) ^ (c * m) := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcτ : τ.im ≤ c * τ.im := by nlinarith
  have hA : (z - c * τ).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero]
    linarith
  have hB : 0 < ((c : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    linarith
  have hC : 0 < (z - (-(c : ℂ)) * τ).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero, zero_mul, add_zero]
    linarith
  have hD : ((-(c : ℂ)) * τ).im < 0 := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero, zero_mul, add_zero]
    linarith
  have sA := summable_nat_mul_cexp_pow (w := -(z - c * τ)) (by simpa using hA)
  have sB := summable_nat_mul_cexp_pow hB
  have sC := summable_nat_mul_cexp_pow hC
  have sD := summable_nat_mul_cexp_pow (w := -((-(c : ℂ)) * τ)) (by simpa using hD)
  rw [lipschitz_two_of_im_neg' hA, lipschitz_two_of_im_pos hB, lipschitz_two_of_im_pos hC,
    lipschitz_two_of_im_neg' hD, ← mul_sub, ← mul_sub, ← mul_add, ← sA.tsum_sub sB,
    ← sC.tsum_sub sD, ← (sA.sub sB).tsum_add (sC.sub sD)]
  congr 1
  refine tsum_congr fun m ↦ ?_
  rw [show -(z - c * τ) = c * τ + -z by ring, show z - (-(c : ℂ)) * τ = c * τ + z by ring,
    show -((-(c : ℂ)) * τ) = c * τ by ring, cexp_two_pi_I_mul_add, cexp_two_pi_I_mul_add,
    cexp_two_pi_I_mul_neg, cexp_two_pi_I_mul_nat_mul]
  ring

private theorem lipschitz_row_zero {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (∑' d : ℤ, 1 / (z + d) ^ 2) - ∑' d : ℤ, 1 / ((d : ℂ)) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12) := by
  rw [lipschitz_two_closed hz, tsum_int_one_div_sq, sub_eq_add_neg, neg_pi_sq_div_three_div]
  ring

private theorem lipschitz_rows_qExpansion {z τ : ℂ} (hτ : 0 < τ.im) (hz₁ : -τ.im < z.im)
    (hz₂ : z.im < τ.im) (hz : z ∈ Complex.integerComplement)
    (hS : Summable fun c : ℤ ↦
      (∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) :
    ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
      (2 * π * I) ^ 2 *
        (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
              cexp (2 * π * I * τ) ^ ((c : ℕ) * m)) := by
  have h3 : Summable fun c : ℕ+ ↦
      (∑' d : ℤ, 1 / ((z - ((c : ℤ) : ℂ) * τ) + d) ^ 2) -
        ∑' d : ℤ, 1 / (((c : ℤ) : ℂ) * τ + d) ^ 2 :=
    hS.comp_injective fun a b h ↦ by exact_mod_cast h
  have h4 : Summable fun c : ℕ+ ↦
      (∑' d : ℤ, 1 / ((z - ((-(c : ℤ) : ℤ) : ℂ) * τ) + d) ^ 2) -
        ∑' d : ℤ, 1 / (((-(c : ℤ) : ℤ) : ℂ) * τ + d) ^ 2 :=
    hS.comp_injective (f := fun c ↦ _) fun a b h ↦ by simpa using h
  rw [tsum_int_eq_zero_add_tsum_pnat hS, add_assoc, ← h3.tsum_add h4]
  simp only [Int.cast_zero, zero_mul, sub_zero, zero_add]
  rw [lipschitz_row_zero hz, mul_add _ _ (∑' c : ℕ+, _), ← tsum_mul_left]
  congr 1
  refine tsum_congr fun c ↦ ?_
  have := lipschitz_row_pair hτ hz₁ hz₂ c.pos
  push_cast at this ⊢
  exact this

end B2_lipschitz

section B2_rearrange

open PeriodPair
open scoped UpperHalfPlane

private def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

@[scoped simp] private lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl
@[scoped simp] private lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

private abbrev wpSummand (L : PeriodPair) (z : ℂ) (p : ℤ × ℤ) : ℂ :=
  1 / (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) ^ 2 - 1 / (p.1 * L.ω₁ + p.2 * L.ω₂) ^ 2

private theorem hasSum_weierstrassP_prod (L : PeriodPair) (z : ℂ) :
    HasSum (wpSummand L z) (weierstrassP L z) := by
  have h := (L.latticeEquivProd.symm.toEquiv.hasSum_iff (f := fun l : L.lattice ↦
      1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)).mpr (L.hasSum_weierstrassP z)
  refine h.congr_fun fun p ↦ ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, wpSummand]
  have hcoe : ((L.latticeEquivProd.symm p : L.lattice) : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ :=
    L.latticeEquiv_symm_apply p
  rw [hcoe]

private theorem summable_weierstrassP_prod (L : PeriodPair) (z : ℂ) :
    Summable (wpSummand L z) :=
  (hasSum_weierstrassP_prod L z).summable

private theorem weierstrassP_eq_tsum_tsum (L : PeriodPair) (z : ℂ) :
    weierstrassP L z =
      ∑' c : ℤ, ∑' d : ℤ,
        (1 / (z - (c * L.ω₁ + d * L.ω₂)) ^ 2 - 1 / (c * L.ω₁ + d * L.ω₂) ^ 2) := by
  rw [← (hasSum_weierstrassP_prod L z).tsum_eq]
  exact (summable_weierstrassP_prod L z).tsum_prod

private theorem summable_weierstrassP_row (L : PeriodPair) (z : ℂ) :
    Summable fun c : ℤ ↦
      ∑' d : ℤ, (1 / (z - (c * L.ω₁ + d * L.ω₂)) ^ 2 - 1 / (c * L.ω₁ + d * L.ω₂) ^ 2) :=
  (summable_weierstrassP_prod L z).prod

private theorem wpRow_periodPairOfTau_split (τ : ℍ) (z : ℂ) (c : ℤ) :
    ∑' d : ℤ, wpSummand (periodPairOfTau τ) z (c, d) =
      (∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) + d) ^ 2) - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2 := by
  have hA : Summable fun d : ℤ ↦ (1 : ℂ) / ((z - c * (τ : ℂ)) - d) ^ 2 := by
    have := summable_one_div_add_int_sq (z - c * (τ : ℂ))
    refine ((Equiv.neg ℤ).summable_iff.mpr this).congr fun d ↦ ?_
    simp [sub_eq_add_neg]
  have hB : Summable fun d : ℤ ↦ (1 : ℂ) / (c * (τ : ℂ) + d) ^ 2 :=
    summable_one_div_add_int_sq (c * (τ : ℂ))
  have step : (∑' d : ℤ, wpSummand (periodPairOfTau τ) z (c, d)) =
      (∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) - d) ^ 2) - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2 := by
    rw [← hA.tsum_sub hB]
    refine tsum_congr fun d ↦ ?_
    simp only [wpSummand, periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]
    ring
  rw [step, tsum_one_div_sub_int_sq]

private theorem weierstrassP_periodPairOfTau_eq_row_sum (τ : ℍ) (z : ℂ) :
    weierstrassP (periodPairOfTau τ) z =
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) + d) ^ 2)
                  - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2) := by
  rw [weierstrassP_eq_tsum_tsum]
  exact tsum_congr fun c ↦ by
    simpa [wpSummand, periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]
      using wpRow_periodPairOfTau_split τ z c

end B2_rearrange

section B2_assembly

open scoped UpperHalfPlane in
private theorem weierstrassP_periodPairOfTau_qExpansion (τ : ℍ) {z : ℂ}
    (hz₁ : -τ.im < z.im) (hz₂ : z.im < τ.im) (hz : z ∈ Complex.integerComplement) :
    PeriodPair.weierstrassP (periodPairOfTau τ) z =
      (2 * π * I) ^ 2 *
        (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
              cexp (2 * π * I * (τ : ℂ)) ^ ((c : ℕ) * m)) := by
  rw [weierstrassP_periodPairOfTau_eq_row_sum]
  refine lipschitz_rows_qExpansion τ.im_pos hz₁ hz₂ hz ?_
  exact (summable_weierstrassP_row (periodPairOfTau τ) z).congr
    fun c ↦ wpRow_periodPairOfTau_split τ z c

end B2_assembly

section B2_torsion

private def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

private def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

private lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _
private lemma qN_ne_zero (N : ℕ) (τ : ℂ) : qN N τ ≠ 0 := Complex.exp_ne_zero _

private lemma qN_pow_self {N : ℕ} (hN : N ≠ 0) (τ : ℂ) : qN N τ ^ N = cexp (2 * π * I * τ) := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [qN, ← Complex.exp_nat_mul]
  congr 1
  field_simp

private lemma cexp_two_pi_I_mul_torsionPt {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (τ : ℂ) :
    cexp (2 * π * I * ((a₁ * τ + a₂) / N)) = zetaN N ^ a₂ * qN N τ ^ a₁ := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [zetaN, qN, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

private lemma norm_qN (N : ℕ) (τ : ℂ) : ‖qN N τ‖ = Real.exp (-(2 * π * τ.im / N)) := by
  rw [qN, Complex.norm_exp]
  congr 1
  rw [show 2 * (π : ℂ) * I * τ / N = (2 * π * I * τ) / (N : ℕ) from rfl, Complex.div_natCast_re]
  simp [mul_comm]
  ring

private lemma torsion_term_aux (ζ q : ℂ) (hq : q ≠ 0) (a₁ a₂ k m : ℕ) :
    ((ζ ^ a₂ * q ^ a₁) ^ m + (ζ ^ a₂ * q ^ a₁)⁻¹ ^ m - 2) * q ^ ((a₁ + k) * m) =
      ζ ^ (a₂ * m) * q ^ ((a₁ + k + a₁) * m) + ζ⁻¹ ^ (a₂ * m) * q ^ (k * m) -
        2 * q ^ ((a₁ + k) * m) := by
  have h2 : (ζ ^ a₂ * q ^ a₁)⁻¹ ^ m * q ^ ((a₁ + k) * m) = ζ⁻¹ ^ (a₂ * m) * q ^ (k * m) := by
    rw [mul_inv, mul_pow, ← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, add_mul, pow_add,
      mul_assoc]
    congr 1
    rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  linear_combination h2

open scoped UpperHalfPlane in
private lemma torsionPt_hyps (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    -τ.im < (((a₁ : ℂ) * τ + a₂) / N).im ∧ (((a₁ : ℂ) * τ + a₂) / N).im < τ.im ∧
      ((a₁ : ℂ) * τ + a₂) / N ∈ Complex.integerComplement := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) ha₁
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ : 0 < τ.im := τ.im_pos
  have him : (((a₁ : ℂ) * τ + a₂) / N).im = a₁ * τ.im / N := by
    rw [Complex.div_natCast_im]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [him]
    have : (0 : ℝ) ≤ a₁ * τ.im / N := by positivity
    linarith
  · rw [him, div_lt_iff₀ hNr]
    have : (a₁ : ℝ) < N := by exact_mod_cast ha₁
    nlinarith
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have him' := congrArg Complex.im hn
    rw [him] at him'
    simp only [Complex.intCast_im] at him'
    have ha₁0 : a₁ = 0 := by
      rcases mul_eq_zero.mp ((div_eq_zero_iff.mp him'.symm).resolve_right hNr.ne') with h | h
      · exact_mod_cast h
      · exact absurd h hτ.ne'
    have ha₂0 : a₂ ≠ 0 := h0.resolve_left (not_not.mpr ha₁0)
    subst ha₁0
    rw [Complex.div_natCast_re] at hre
    simp only [Complex.intCast_re, Nat.cast_zero, zero_mul, zero_add, Complex.natCast_re] at hre
    rw [eq_div_iff hNr.ne'] at hre
    have h1 : (0 : ℝ) < n := by
      have : (0 : ℝ) < a₂ := by exact_mod_cast Nat.pos_of_ne_zero ha₂0
      nlinarith
    have h2 : (n : ℝ) < 1 := by
      have : (a₂ : ℝ) < N := by exact_mod_cast ha₂
      nlinarith
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega

open scoped UpperHalfPlane in
private theorem weierstrassP_torsionPt_qExpansion (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂
    < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N) =
      (2 * π * I) ^ 2 *
        (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (zetaN N ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N + a₁) * m) +
              (zetaN N)⁻¹ ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N - a₁) * m) -
                2 * qN N τ ^ ((c : ℕ) * N * m))) := by
  have hN : N ≠ 0 := by omega
  obtain ⟨hz₁, hz₂, hz⟩ := torsionPt_hyps τ ha₁ ha₂ h0
  rw [weierstrassP_periodPairOfTau_qExpansion τ hz₁ hz₂ hz, cexp_two_pi_I_mul_torsionPt hN,
    ← qN_pow_self hN]
  congr 2
  refine tsum_congr fun c ↦ tsum_congr fun m ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (c : ℕ) * N = a₁ + k :=
    ⟨(c : ℕ) * N - a₁,
        (Nat.add_sub_cancel' (le_trans ha₁.le (Nat.le_mul_of_pos_left N c.pos))).symm⟩
  rw [← pow_mul (qN N τ) N, show N * ((c : ℕ) * m) = ((c : ℕ) * N) * m by ring, hk,
    Nat.add_sub_cancel_left, mul_assoc, torsion_term_aux _ _ (qN_ne_zero N τ)]

end B2_torsion

section B3_holo

open scoped UpperHalfPlane Manifold

private lemma norm_zetaN (N : ℕ) : ‖zetaN N‖ = 1 := by
  rw [zetaN, Complex.norm_exp, show 2 * (π : ℂ) * I / N = (2 * π * I) / (N : ℕ) from rfl,
    Complex.div_natCast_re]
  simp

private lemma norm_qN_le_one (N : ℕ) {τ : ℂ} (hτ : 0 ≤ τ.im) : ‖qN N τ‖ ≤ 1 := by
  rw [norm_qN, Real.exp_le_one_iff, neg_nonpos]
  positivity

private lemma norm_qN_lt_one {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) : ‖qN N τ‖ < 1 := by
  rw [norm_qN, Real.exp_lt_one_iff, neg_lt_zero]
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

private lemma norm_qN_le_of_le_im (N : ℕ) {B : ℝ} {τ : ℂ} (hτ : B ≤ τ.im) :
    ‖qN N τ‖ ≤ Real.exp (-(2 * π * B / N)) := by
  rw [norm_qN, Real.exp_le_exp, neg_le_neg_iff]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have : (0 : ℝ) < N := by exact_mod_cast hN
    gcongr

private def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

private lemma norm_wpTail_le {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) (p : ℕ+ × ℕ+) {τ : ℂ} (hτ : 0
    ≤ τ.im) :
    ‖wpTail N a₁ a₂ p τ‖ ≤ 4 * ((p.2 : ℕ) * ‖qN N τ‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  obtain ⟨c, m⟩ := p
  have hq1 := norm_qN_le_one N hτ
  have hcN : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
    have h1 : (c : ℕ) * (a₁ + 1) ≤ (c : ℕ) * N := Nat.mul_le_mul_left _ ha₁
    have h2 : a₁ ≤ (c : ℕ) * a₁ := Nat.le_mul_of_pos_left _ c.pos
    rw [mul_add, mul_one] at h1
    omega
  have e1 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N + a₁) * (m : ℕ) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have e2 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N - a₁) * (m : ℕ) := Nat.mul_le_mul_right _ hcN
  have e3 : (c : ℕ) * (m : ℕ) ≤ (c : ℕ) * N * (m : ℕ) := Nat.mul_le_mul_right _ (by nlinarith)
  have b1 : ‖qN N τ‖ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e1
  have b2 : ‖qN N τ‖ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e2
  have b3 : ‖qN N τ‖ ^ ((c : ℕ) * N * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e3
  have hz : ‖zetaN N‖ = 1 := norm_zetaN N
  set ρ : ℝ := ‖qN N τ‖ with hρ
  set A : ℂ := zetaN N ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) with hAdef
  set B : ℂ := (zetaN N)⁻¹ ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) with hBdef
  set C : ℂ := qN N τ ^ ((c : ℕ) * N * (m : ℕ)) with hCdef
  have hA : ‖A‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hAdef, norm_mul, norm_pow, hz, one_pow, one_mul, norm_pow]; exact b1
  have hB : ‖B‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hBdef, norm_mul, norm_pow, norm_inv, hz, inv_one, one_pow, one_mul, norm_pow]; exact b2
  have hC : ‖(2 : ℂ) * C‖ ≤ 2 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [norm_mul, Complex.norm_ofNat, hCdef, norm_pow]; linarith
  have hst : ‖A + B - 2 * C‖ ≤ 4 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    linarith [norm_sub_le (A + B) (2 * C), norm_add_le A B]
  change ‖((m : ℕ) : ℂ) * (A + B - 2 * C)‖ ≤ 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ)))
  rw [norm_mul, Complex.norm_natCast]
  calc ((m : ℕ) : ℝ) * ‖A + B - 2 * C‖ ≤ (m : ℕ) * (4 * ρ ^ ((c : ℕ) * (m : ℕ))) := by gcongr
    _ = 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ))) := by ring

private lemma summable_wpTail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ 4 * ((p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have h := summable_prod_mul_pow 1 (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  refine (h.mul_left 4).congr fun p ↦ ?_
  simp

private lemma summable_wpTail {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun p ↦ wpTail N a₁ a₂ p τ :=
  Summable.of_norm_bounded
    (summable_wpTail_majorant (norm_nonneg _) (norm_qN_lt_one (by omega) hτ))
    fun p ↦ norm_wpTail_le ha₁ a₂ p hτ.le

private theorem weierstrassP_torsionPt_eq_tsum_prod (τ : ℍ) {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂
    < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N) =
      (2 * π * I) ^ 2 *
        (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
          ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) := by
  have hS := summable_wpTail ha₁ a₂ (τ := (τ : ℂ)) τ.im_pos
  rw [weierstrassP_torsionPt_qExpansion τ ha₁ ha₂ h0, hS.tsum_prod]
  congr 2
  refine tsum_congr fun c ↦ ?_
  set F : ℕ → ℂ := fun m ↦ (m : ℂ) *
    (zetaN N ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N + a₁) * m) +
      (zetaN N)⁻¹ ^ (a₂ * m) * qN N τ ^ (((c : ℕ) * N - a₁) * m) -
        2 * qN N τ ^ ((c : ℕ) * N * m)) with hF
  have hs : Summable F := summable_pnat_iff_summable_nat.mp (hS.prod_factor c)
  change ∑' m : ℕ, F m = ∑' m : ℕ+, F m
  rw [← tsum_zero_pnat_eq_tsum_nat hs]
  simp [hF]

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

private lemma wpTorsion_eq_wpTorsionSeries {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    wpTorsion N a₁ a₂ τ = wpTorsionSeries N a₁ a₂ τ :=
  weierstrassP_torsionPt_eq_tsum_prod τ ha₁ ha₂ h0

private lemma one_sub_zetaN_pow_mul_qN_pow_ne_zero {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) {τ : ℂ} (hτ : 0 < τ.im) :
    1 - zetaN N ^ a₂ * qN N τ ^ a₁ ≠ 0 := by
  obtain ⟨-, -, hz⟩ := torsionPt_hyps ⟨τ, hτ⟩ ha₁ ha₂ h0
  rw [← cexp_two_pi_I_mul_torsionPt (by omega), sub_ne_zero]
  exact (cexp_two_pi_I_mul_ne_one hz).symm

private lemma differentiable_qN (N : ℕ) : Differentiable ℂ (qN N) := by
  unfold qN; fun_prop

private lemma differentiable_wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) :
    Differentiable ℂ (wpTail N a₁ a₂ p) := by
  unfold wpTail
  have := differentiable_qN N
  fun_prop

open Complex in
private theorem differentiableOn_wpTorsionSeries {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    DifferentiableOn ℂ (wpTorsionSeries N a₁ a₂) {τ : ℂ | 0 < τ.im} := by
  intro τ₀ hτ₀
  set B : ℝ := τ₀.im / 2 with hB
  have hB0 : 0 < B := by simp only [Set.mem_ofPred_eq] at hτ₀; positivity
  set U : Set ℂ := {τ : ℂ | B < τ.im} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hτ₀U : τ₀ ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, hB]; simp only [Set.mem_ofPred_eq] at hτ₀; linarith
  have hUsub : U ⊆ {τ : ℂ | 0 < τ.im} := fun τ hτ ↦ lt_trans hB0 hτ
  set ρ : ℝ := Real.exp (-(2 * π * B / N)) with hρ
  have hN : 0 < N := by omega
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff, neg_lt_zero]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have htail : DifferentiableOn ℂ (fun τ ↦ ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) U := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_wpTail_majorant (Real.exp_pos _).le hρ1)
      (fun p ↦ (differentiable_wpTail N a₁ a₂ p).differentiableOn) hUopen ?_
    intro p τ hτ
    refine (norm_wpTail_le ha₁ a₂ p (lt_trans hB0 hτ).le).trans ?_
    gcongr
    exact norm_qN_le_of_le_im N (le_of_lt hτ)
  have hhead : DifferentiableOn ℂ
      (fun τ ↦ zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2) U := by
    have := differentiable_qN N
    refine DifferentiableOn.fun_div (by fun_prop) (by fun_prop) fun τ hτ ↦ pow_ne_zero _ ?_
    exact one_sub_zetaN_pow_mul_qN_pow_ne_zero ha₁ ha₂ h0 (hUsub hτ)
  have hall : DifferentiableOn ℂ (wpTorsionSeries N a₁ a₂) U := by
    unfold wpTorsionSeries
    exact DifferentiableOn.fun_mul (differentiableOn_const _)
      ((hhead.fun_add (differentiableOn_const _)).fun_add htail)
  exact ((hall τ₀ hτ₀U).differentiableAt (hUopen.mem_nhds hτ₀U)).differentiableWithinAt

private theorem mdifferentiable_wpTorsion {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpTorsion N a₁ a₂) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_wpTorsionSeries ha₁ ha₂ h0).congr fun τ hτ ↦ ?_
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hτ]
  exact wpTorsion_eq_wpTorsionSeries ha₁ ha₂ h0 ⟨τ, hτ⟩

end B3_holo

section R1Bridge

open scoped UpperHalfPlane Manifold

private lemma PeriodPair.ext_omega {L L' : PeriodPair} (h1 : L.ω₁ = L'.ω₁) (h2 : L.ω₂ = L'.ω₂) :
    L = L' := by
  cases L; cases L'; simp_all

end R1Bridge

end Aux
open scoped FrickeFunctions.WeierstrassPQExpansion.Aux

end
open scoped FrickeFunctions.WeierstrassPQExpansion.Aux

open Complex Real in
open scoped UpperHalfPlane Manifold in
open Aux in
/-- Lipschitz summation and q-expansions of the Weierstrass function: for `0 < im w`, `∑ₙ (w + n)⁻²
= (2πi)² ∑ₘ m qᵐ` with `q = exp (2πi w)`; the companion formula for `im w < 0`; the q-expansion
of the regularized lattice sum in the strip `-im τ < im z < im τ`; for a family of lattices `ℤτ
+ ℤ`, the q-expansion of `℘` at the torsion point `(a₁ τ + a₂) / N` and its holomorphy in `τ`;
and the homogeneity `℘_{cL} (c z) = c⁻² ℘_L z`. -/
public theorem _root_.ModularForm.weierstrassP_qExpansion_package :
    (∀ w : ℂ, 0 < w.im →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m) ∧
    (∀ w : ℂ, w.im < 0 →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m) ∧
    (∀ z τ : ℂ, -τ.im < z.im → z.im < τ.im → z ∈ Complex.integerComplement →
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
        (2 * π * I) ^ 2 *
          (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
            ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
              (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
                cexp (2 * π * I * τ) ^ ((c : ℕ) * m))) ∧
    (∀ L : ℍ → PeriodPair, (∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
      ∀ N a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (∀ τ : ℍ, PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N) =
          (2 * π * I) ^ 2 *
            (cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁ /
                (1 - cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁) ^ 2 +
              1 / 12 +
              ∑' p : ℕ+ × ℕ+, ((p.2 : ℕ) : ℂ) *
                (cexp (2 * π * I / N) ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
                  (cexp (2 * π * I / N))⁻¹ ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
                  2 * cexp (2 * π * I * (τ : ℂ) / N) ^ ((p.1 : ℕ) * N * (p.2 : ℕ))))) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
          (fun τ : ℍ => PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N))) ∧
    (∀ L L' : PeriodPair, ∀ c : ℂ, L'.ω₁ = c * L.ω₁ → L'.ω₂ = c * L.ω₂ →
      ∀ z : ℂ, PeriodPair.weierstrassP L' (c * z) =
        c⁻¹ ^ 2 * PeriodPair.weierstrassP L z) := by
  refine ⟨fun w hw => lipschitz_two_of_im_pos hw, fun w hw => lipschitz_two_of_im_neg hw,
    fun z τ hz₁ hz₂ hz => ?_, ?_, ?_⟩
  · have hτpos : 0 < τ.im := by linarith
    have hS : Summable fun c : ℤ ↦
        (∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2 :=
      (summable_weierstrassP_row (periodPairOfTau ⟨τ, hτpos⟩) z).congr
        fun c ↦ wpRow_periodPairOfTau_split ⟨τ, hτpos⟩ z c
    exact lipschitz_rows_qExpansion hτpos hz₁ hz₂ hz hS
  · intro L hL N a₁ a₂ ha₁ ha₂ h0
    have hLeq : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
      PeriodPair.ext_omega (hL τ).1 (hL τ).2
    constructor
    · intro τ
      rw [hLeq τ]
      simpa only [zetaN, qN, wpTail] using weierstrassP_torsionPt_eq_tsum_prod τ ha₁ ha₂ h0
    · have hfun : (fun τ : ℍ => PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N)) =
          wpTorsion N a₁ a₂ := funext fun τ => by rw [wpTorsion, hLeq τ]
      rw [hfun]
      exact mdifferentiable_wpTorsion ha₁ ha₂ h0
  · intro L L' c hω₁ hω₂ z
    have hc : c ≠ 0 := by
      rintro rfl
      have h0 : L'.ω₁ = 0 := by rw [hω₁, zero_mul]
      have h1 := L'.indep.ne_zero 0
      simp only [Matrix.cons_val_zero] at h1
      exact h1 h0
    have hL' : L' = smulPeriodPair c hc L := by
      refine PeriodPair.ext_omega ?_ ?_ <;> simp [smulPeriodPair, hω₁, hω₂]
    rw [hL']
    exact weierstrassP_smulPeriodPair c hc L z

end WeierstrassPQExpansion

end FrickeFunctions
