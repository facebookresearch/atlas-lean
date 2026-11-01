/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Growth bounds and a zero-free region for the Riemann zeta function

For `T ≥ e²` let `σ₀ = 1 - 1 / log T` and let `R_T` be the closed rectangle
`[σ₀, 2] × [-T, T]`. We prove the classical estimates for `ζ` near the line `re s = 1`
that drive the elementary proofs of the prime number theorem with error term
`O(x exp(-c (log x)^{1/10}))`.

## Main statements

* `riemannZeta_eq_sum_add_integral_sawtooth`: the Euler–Maclaurin expansion
  `ζ(s) = ∑_{m < n} m^{-s} + n^{-s}/2 + n^{1-s}/(s-1) - s ∫_n^∞ (x - ⌊x⌋ - 1/2) x^{-s-1} dx`
  for `re s > 0`, `s ≠ 1`.
* `norm_mul_integral_sawtooth_le`: the remainder is at most `‖s‖ / (2 σ n^σ)`.
* `exists_pos_norm_riemannZeta_sub_one_div_le_mul_log`: `ζ(s) - 1/(s-1) = O(log T)` on `R_T`.
* `exists_pos_norm_riemannZeta_le_mul_log_of_mem_frontier`: `ζ(s) = O(log T)` on `∂R_T`.
* `exists_pos_norm_riemannZeta_le_mul_abs_im_rpow_half`: the convexity bound
  `ζ(s) = O(|t|^{1/2})` for `re s ≥ 1/2`.
* `exists_pos_norm_deriv_riemannZeta_add_one_div_sq_le_mul_log_sq`:
  `ζ'(s) + 1/(s-1)² = O(log² T)` on `R_T`, and
  `exists_pos_norm_deriv_riemannZeta_le_mul_log_sq_of_mem_frontier`: `ζ'(s) = O(log² T)` on
  `∂R_T`.
* `one_le_norm_riemannZeta_pow_three_mul`: the `3-4-1` inequality.
* `exists_pos_div_log_pow_seven_lt_norm_riemannZeta`: the zero-free region
  `|ζ(σ + it)| > c₂ / log⁷ T` for `1 ≤ |t| ≤ T` and `1 - c₁ / log⁹ T ≤ σ ≤ 2`.
* `exists_riemannZeta₁_ne_zero_and_norm_logDeriv_le`: `riemannZeta₁` has no zeros in a box
  `[1 - δ, 2] × [-1, 1]`, where its logarithmic derivative is bounded.
-/

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Topology

/-! ### The sawtooth function -/

/-- The sawtooth function `x - ⌊x⌋ - 1 / 2` is bounded by `1 / 2`. -/
theorem abs_sub_floor_sub_half_le (x : ℝ) : |x - (⌊x⌋ : ℝ) - 1 / 2| ≤ 1 / 2 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  rw [abs_le]; constructor <;> linarith

/-- The sawtooth integrand `(x - ⌊x⌋ - 1 / 2) / x ^ (z + 1)` is at most `x ^ (-(re z + 1)) / 2`
in norm. -/
theorem norm_sawtooth_div_cpow_le (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1)‖ ≤ 1 / 2 * x ^ (-(z.re + 1)) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re,
    Real.rpow_neg hx.le, ← div_eq_mul_inv]
  gcongr
  exact abs_sub_floor_sub_half_le x

/-- The sawtooth integrand `(x - ⌊x⌋ - 1 / 2) / x ^ (z + 1)` is integrable on `(a, ∞)` for
`a > 0` and `re z > 0`. -/
theorem integrableOn_Ioi_sawtooth_div_cpow {z : ℂ} (hz : 0 < z.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1))
      (Set.Ioi a) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1))
      (volume.restrict (Set.Ioi a)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hb : IntegrableOn (fun x : ℝ => 1 / 2 * x ^ (-(z.re + 1))) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul _
  refine Integrable.mono' hb hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_sawtooth_div_cpow_le z (by simp only [Set.mem_Ioi] at hx; linarith)



/-! ### The rectangle `[1 - 1 / log T, 2] × [-T, T]` -/

/-- A point of the frontier of `[a, b] × [-T, T]` lies in the rectangle but not in its
interior. -/
private theorem mem_and_not_mem_of_mem_frontier {a b T : ℝ} {s : ℂ}
    (hs : s ∈ frontier (Icc a b ×ℂ Icc (-T) T)) :
    (a ≤ s.re ∧ s.re ≤ b ∧ |s.im| ≤ T) ∧ ¬(a < s.re ∧ s.re < b ∧ |s.im| < T) := by
  have hmem := (isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hs
  simp only [mem_reProdIm, mem_Icc] at hmem
  refine ⟨⟨hmem.1.1, hmem.1.2, abs_le.mpr hmem.2⟩, fun h => hs.2 ?_⟩
  rw [interior_reProdIm, interior_Icc, interior_Icc, mem_reProdIm]
  exact ⟨⟨h.1, h.2.1⟩, abs_lt.mp h.2.2⟩

/-- **The pole term on the boundary of the rectangle.** For `T ≥ e²` and `s` on the frontier
of `[1 - 1 / log T, 2] × [-T, T]`, `‖1 / (s - 1)‖ ≤ log T`. -/
theorem norm_one_div_sub_one_le_log_of_mem_frontier {T : ℝ} (hT : Real.exp 2 ≤ T) {s : ℂ}
    (hs : s ∈ frontier (Icc (1 - 1 / Real.log T) 2 ×ℂ Icc (-T) T)) :
    ‖1 / (s - 1)‖ ≤ Real.log T := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 2) hT
  have hL2 : (2 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by
    have h : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    linarith
  -- `s` lies in the rectangle, on one of its sides
  obtain ⟨⟨hA1, hA2, hA3⟩, hbox⟩ := mem_and_not_mem_of_mem_frontier hs
  -- ## `1 / log T ≤ ‖s - 1‖` on every side
  have hre : |s.re - 1| ≤ ‖s - 1‖ := by
    simpa [Complex.sub_re, Complex.one_re] using Complex.abs_re_le_norm (s - 1)
  have him : |s.im| ≤ ‖s - 1‖ := by
    simpa [Complex.sub_im, Complex.one_im] using Complex.abs_im_le_norm (s - 1)
  have hinv1 : 1 / Real.log T ≤ 1 := by
    rw [div_le_one hL0]; linarith
  have hkey : 1 / Real.log T ≤ ‖s - 1‖ := by
    rcases lt_or_eq_of_le hA1 with h1 | h1
    · rcases lt_or_eq_of_le hA2 with h2 | h2
      · -- interior of the two vertical sides: `s` must be on a horizontal side, `|t| = T`
        have h3 : T ≤ |s.im| := by
          by_contra hlt
          exact hbox ⟨h1, h2, not_le.mp hlt⟩
        calc 1 / Real.log T ≤ 1 := hinv1
          _ ≤ T := hT1
          _ ≤ |s.im| := h3
          _ ≤ ‖s - 1‖ := him
      · -- the right side `σ = 2`, where `|s - 1| ≥ 1`
        have habs : |s.re - 1| = 1 := by
          rw [h2]; norm_num
        rw [habs] at hre
        linarith
    · -- the left side `σ = 1 - 1 / log T`, where `|s - 1| ≥ 1 / log T`
      have hrw : (1 - 1 / Real.log T) - 1 = -(1 / Real.log T) := by ring
      have habs : |s.re - 1| = 1 / Real.log T := by
        rw [← h1, hrw, abs_neg, abs_of_nonneg (by positivity)]
      rw [habs] at hre
      exact hre
  -- ## Conclude
  have hpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by positivity) hkey
  have hmul : 1 ≤ Real.log T * ‖s - 1‖ := by
    have h := mul_le_mul_of_nonneg_left hkey hL0.le
    rwa [mul_one_div, div_self hL0.ne'] at h
  rw [norm_div, norm_one]
  rw [div_le_iff₀ hpos]
  exact hmul

/-! ### The Euler–Maclaurin expansion of `ζ` -/

/-- **The sawtooth tail integral.** For `σ = re s > 0` and every integer `n ≥ 1`,

`‖s * ∫_n^∞ (x - [x] - 1 / 2) / x ^ (s + 1) dx‖ ≤ ‖s‖ / (2 * σ * n ^ σ)`,

where `[x]` is the greatest integer `≤ x`. -/
theorem norm_mul_integral_sawtooth_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖s * ∫ x in Set.Ioi (n : ℝ),
        ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤
      ‖s‖ / (2 * s.re * (n : ℝ) ^ s.re) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
  -- ## Integrability of the tail against the majorant `x ^ (-(σ + 1))`
  have hb : IntegrableOn (fun x : ℝ => 1 / 2 * x ^ (-(s.re + 1))) (Set.Ioi (n : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hn0).const_mul _
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioi (n : ℝ))),
      ‖((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖
        ≤ 1 / 2 * x ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_sawtooth_div_cpow_le s (by simp only [Set.mem_Ioi] at hx; linarith)
  have hInt := integrableOn_Ioi_sawtooth_div_cpow hs hn0
  -- ## The majorant integrates to `1 / (2 σ n ^ σ)`
  have hval : ∫ x in Set.Ioi (n : ℝ), 1 / 2 * x ^ (-(s.re + 1))
      = 1 / (2 * s.re * (n : ℝ) ^ s.re) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hn0,
      show -(s.re + 1) + 1 = -s.re by ring, Real.rpow_neg hn0.le]
    field_simp
  -- ## Bound the tail integral
  have hle : ‖∫ x in Set.Ioi (n : ℝ),
      ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖
        ≤ 1 / (2 * s.re * (n : ℝ) ^ s.re) := by
    rw [← hval]
    exact (norm_integral_le_integral_norm _).trans (integral_mono_ae hInt.norm hb hae)
  -- ## Conclude
  rw [norm_mul]
  have hfin := mul_le_mul_of_nonneg_left hle (norm_nonneg s)
  rwa [mul_one_div] at hfin

/-- **The Euler–Maclaurin expansion of `ζ`.** For `re s > 0`,
`s ≠ 1` and every integer `n ≥ 1`,

`ζ (s) = ∑_{m = 1}^{n - 1} m ^ (-s) + n ^ (-s) / 2 + n ^ (1 - s) / (s - 1)`
`          - s * ∫_n^∞ (x - [x] - 1 / 2) / x ^ (s + 1) dx`,

where `[x]` is the greatest integer `≤ x`. -/
theorem riemannZeta_eq_sum_add_integral_sawtooth
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    riemannZeta s =
      (∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-s))
        + (n : ℂ) ^ (-s) / 2
        + (n : ℂ) ^ (1 - s) / (s - 1)
        - s * ∫ x in Set.Ioi (n : ℝ),
            ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) := by
  open MeasureTheory intervalIntegral Topology in
  -- Name the sawtooth integrand, as a function of the parameter.
  obtain ⟨saw, hsaw⟩ : ∃ saw : ℂ → ℝ → ℂ, ∀ (z : ℂ) (x : ℝ),
      saw z x = ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1) := ⟨_, fun _ _ => rfl⟩
  have hsawf : ∀ z : ℂ, saw z
      = fun x : ℝ => ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1) :=
    fun z => funext (hsaw z)
  simp only [← hsaw]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  -- ## Basic bounds and integrability
  have hnorm : ∀ (z : ℂ) (x : ℝ), 0 < x → ‖saw z x‖ ≤ 1 / 2 * x ^ (-(z.re + 1)) :=
    fun z x hx => by rw [hsaw]; exact norm_sawtooth_div_cpow_le z hx
  have hIntC : ∀ z : ℂ, 0 < z.re → IntegrableOn (saw z) (Set.Ioi (n : ℝ)) := fun z hz => by
    rw [hsawf z]; exact integrableOn_Ioi_sawtooth_div_cpow hz (by linarith)
  have hII : ∀ z : ℂ, 0 < z.re → ∀ a b : ℝ, (n : ℝ) ≤ a → a ≤ b →
      IntervalIntegrable (saw z) volume a b := by
    intro z hz a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact (hIntC z hz).mono_set (fun x hx => by
      simp only [Set.mem_Ioc] at hx; simp only [Set.mem_Ioi]; linarith [hx.1])
  -- ## The unit-interval evaluation
  have hunit : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → ∀ k : ℕ, 1 ≤ k →
      (∫ x in (k : ℝ)..((k : ℝ) + 1), saw z x)
        = (((k : ℂ) + 1) ^ (1 - z) - (k : ℂ) ^ (1 - z)) / (1 - z)
          - ((k : ℂ) + 1 / 2) * ((((k : ℂ) + 1) ^ (-z) - (k : ℂ) ^ (-z)) / (-z)) := by
    intro z hz hz1 k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hnot : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k : ℝ) + 1) := by
      rw [Set.uIcc_of_le hle]
      simp only [Set.mem_Icc, not_and, not_le]
      intro h; linarith
    have hr1 : (-z) ≠ -1 := by simpa using hz1
    have hr2 : (-z - 1) ≠ -1 := fun h => hz (by linear_combination -h)
    have hcongr : (∫ x in (k : ℝ)..((k : ℝ) + 1), saw z x)
        = ∫ x in (k : ℝ)..((k : ℝ) + 1),
            ((x : ℂ) ^ (-z) - ((k : ℂ) + 1 / 2) * (x : ℂ) ^ (-z - 1)) := by
      refine integral_congr_Ioo_of_le hle ?_
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hxpos : (0 : ℝ) < x := by linarith
      have hfl : ⌊x⌋ = (k : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      have hxne : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
      have hzne : ((x : ℝ) : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hxne)
      have e1 : ((x : ℝ) : ℂ) ^ (z + 1) = (x : ℂ) ^ z * (x : ℂ) := by
        rw [Complex.cpow_add _ _ hxne, Complex.cpow_one]
      have e2 : ((x : ℝ) : ℂ) ^ (-z) = ((x : ℂ) ^ z)⁻¹ := Complex.cpow_neg _ _
      have e3 : ((x : ℝ) : ℂ) ^ (-z - 1) = ((x : ℂ) ^ z * (x : ℂ))⁻¹ := by
        rw [show (-z - 1) = -(z + 1) by ring, Complex.cpow_neg, e1]
      simp only [hsaw, hfl]
      push_cast
      rw [e1, e2, e3]
      field_simp
      ring
    rw [hcongr, integral_sub (intervalIntegrable_cpow (Or.inr hnot))
      ((intervalIntegrable_cpow (Or.inr hnot)).const_mul _),
      intervalIntegral.integral_const_mul, integral_cpow (Or.inr ⟨hr1, hnot⟩),
      integral_cpow (Or.inr ⟨hr2, hnot⟩),
      show (-z + 1) = 1 - z by ring, show (-z - 1 + 1) = -z by ring]
    push_cast
    ring
  -- ## The finite Euler-Maclaurin identity, by induction on the upper endpoint
  have key : ∀ z : ℂ, 0 < z.re → z ≠ 1 → ∀ N : ℕ, n ≤ N →
      ∑ k ∈ Finset.Icc n N, (k : ℂ) ^ (-z)
        = ((n : ℂ) ^ (-z) + (N : ℂ) ^ (-z)) / 2
          + ((N : ℂ) ^ (1 - z) - (n : ℂ) ^ (1 - z)) / (1 - z)
          - z * ∫ x in (n : ℝ)..(N : ℝ), saw z x := by
    intro z hz hz1
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    have hu : (1 : ℂ) - z ≠ 0 := fun h => hz1 (by linear_combination -h)
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
        have hN1 : 1 ≤ N := le_trans hn hN
        have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
        have hNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have hsplit : (∫ x in (n : ℝ)..((N : ℝ) + 1), saw z x)
            = (∫ x in (n : ℝ)..(N : ℝ), saw z x) + ∫ x in (N : ℝ)..((N : ℝ) + 1), saw z x :=
          (integral_add_adjacent_intervals (hII z hz _ _ le_rfl hNR)
            (hII z hz _ _ hNR (by linarith))).symm
        have hA : ((N : ℂ) + 1) ^ (1 - z) = ((N : ℂ) + 1) * ((N : ℂ) + 1) ^ (-z) := by
          have h0 : (N : ℂ) + 1 ≠ 0 := by
            have hr : ((N : ℝ) + 1 : ℝ) ≠ 0 := by positivity
            exact_mod_cast fun h => hr (by exact_mod_cast h)
          rw [show (1 : ℂ) - z = 1 + -z by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
        have hB : (N : ℂ) ^ (1 - z) = (N : ℂ) * (N : ℂ) ^ (-z) := by
          rw [show (1 : ℂ) - z = 1 + -z by ring, Complex.cpow_add _ _ hNne, Complex.cpow_one]
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        rw [hsplit, hunit z hz0 hz1 N hN1, hA, hB]
        field_simp
        ring
  -- ## The identity in the half-plane of absolute convergence
  have hgt : ∀ z : ℂ, 1 < z.re →
      riemannZeta z = (∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z)) + (n : ℂ) ^ (-z) / 2
        + (n : ℂ) ^ (1 - z) / (z - 1) - z * ∫ x in Set.Ioi (n : ℝ), saw z x := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    have hu : (1 : ℂ) - z ≠ 0 := fun h => hz1 (by linear_combination -h)
    have hu' : z - (1 : ℂ) ≠ 0 := fun h => hz1 (by linear_combination h)
    have hc : ∀ m : ℕ, 1 / (m : ℂ) ^ z = (m : ℂ) ^ (-z) := by
      intro m; rw [Complex.cpow_neg, div_eq_mul_inv, one_mul]
    have hsum : HasSum (fun m : ℕ => 1 / (m : ℂ) ^ z) (riemannZeta z) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hz]
      exact (Complex.summable_one_div_nat_cpow.mpr hz).hasSum
    have hlim1 : Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), 1 / (m : ℂ) ^ z)
        Filter.atTop (nhds (riemannZeta z)) :=
      (hsum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
    have h0 : ∑ m ∈ Finset.Ico 0 n, (m : ℂ) ^ (-z) = ∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z) := by
      rw [show Finset.Ico 0 n = insert 0 (Finset.Ico 1 n) by ext a; simp; omega,
        Finset.sum_insert (by simp)]
      simp [Complex.zero_cpow (neg_ne_zero.mpr hz0)]
    have hpart : ∀ N : ℕ, n ≤ N → ∑ m ∈ Finset.range (N + 1), 1 / (m : ℂ) ^ z
        = (∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z)) + ∑ k ∈ Finset.Icc n N, (k : ℂ) ^ (-z) := by
      intro N hN
      have hIcc : Finset.Ico n (N + 1) = Finset.Icc n N := by ext a; simp
      simp only [hc]
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun m : ℕ => (m : ℂ) ^ (-z))
        (Nat.zero_le n) (by omega), hIcc, h0]
    have hrpow : ∀ c : ℝ, 0 < c → Filter.Tendsto (fun N : ℕ => ((N : ℝ)) ^ (-c))
        Filter.atTop (nhds 0) :=
      fun c hc => (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
    have hnormcast : ∀ (w : ℂ) (N : ℕ), 1 ≤ N → ‖((N : ℕ) : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
      intro w N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    have tA : Filter.Tendsto (fun N : ℕ => (N : ℂ) ^ (-z)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (hrpow z.re (by linarith))
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [hnormcast (-z) N hN, Complex.neg_re]
    have tB : Filter.Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - z)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (hrpow (z.re - 1) (by linarith))
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [hnormcast (1 - z) N hN, Complex.sub_re, Complex.one_re,
        show (1 : ℝ) - z.re = -(z.re - 1) by ring]
    have tC : Filter.Tendsto (fun N : ℕ => ∫ x in (n : ℝ)..(N : ℝ), saw z x) Filter.atTop
        (nhds (∫ x in Set.Ioi (n : ℝ), saw z x)) :=
      intervalIntegral_tendsto_integral_Ioi _ (hIntC z (by linarith))
        tendsto_natCast_atTop_atTop
    have hlim2 : Filter.Tendsto (fun N : ℕ => (∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z))
        + (((n : ℂ) ^ (-z) + (N : ℂ) ^ (-z)) / 2
          + ((N : ℂ) ^ (1 - z) - (n : ℂ) ^ (1 - z)) / (1 - z)
          - z * ∫ x in (n : ℝ)..(N : ℝ), saw z x)) Filter.atTop
        (nhds ((∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z))
          + (((n : ℂ) ^ (-z) + 0) / 2 + (0 - (n : ℂ) ^ (1 - z)) / (1 - z)
            - z * ∫ x in Set.Ioi (n : ℝ), saw z x))) :=
      tendsto_const_nhds.add
        ((((tendsto_const_nhds.add tA).div_const 2).add
          ((tB.sub tendsto_const_nhds).div_const (1 - z))).sub (tC.const_mul z))
    have hev : (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), 1 / (m : ℂ) ^ z)
        =ᶠ[Filter.atTop] (fun N : ℕ => (∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-z))
          + (((n : ℂ) ^ (-z) + (N : ℂ) ^ (-z)) / 2
            + ((N : ℂ) ^ (1 - z) - (n : ℂ) ^ (1 - z)) / (1 - z)
            - z * ∫ x in (n : ℝ)..(N : ℝ), saw z x)) := by
      filter_upwards [Filter.eventually_ge_atTop n] with N hN
      rw [hpart N hN, key z (by linarith) hz1 N hN]
    have hfin := tendsto_nhds_unique (hlim1.congr' hev) hlim2
    rw [hfin]
    field_simp
    ring
  -- ## Differentiability of the tail integral on the half-plane `0 < re z`
  have hre_le : ∀ z w : ℂ, |z.re - w.re| ≤ dist z w := by
    intro z w
    rw [Complex.dist_eq]
    simpa using Complex.abs_re_le_norm (z - w)
  have hcore : ∀ y : ℝ, 0 < y → ∀ c w : ℂ,
      HasDerivAt (fun z : ℂ => c / (y : ℂ) ^ (z + 1))
        (-((Real.log y : ℂ) * (c / (y : ℂ) ^ (w + 1)))) w := by
    intro y hy c w
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hg : HasDerivAt (fun z : ℂ => -(z + 1)) (-1) w :=
      ((hasDerivAt_id w).add_const (1 : ℂ)).neg
    have h1 : HasDerivAt (fun z : ℂ => ((y : ℝ) : ℂ) ^ (-(z + 1)))
        (((y : ℝ) : ℂ) ^ (-(w + 1)) * Complex.log ((y : ℝ) : ℂ) * (-1)) w :=
      hg.const_cpow (Or.inl hy0)
    have h2 : HasDerivAt (fun z : ℂ => c * ((y : ℝ) : ℂ) ^ (-(z + 1)))
        (c * (((y : ℝ) : ℂ) ^ (-(w + 1)) * Complex.log ((y : ℝ) : ℂ) * (-1))) w :=
      h1.const_mul c
    have hfun : (fun z : ℂ => c * ((y : ℝ) : ℂ) ^ (-(z + 1)))
        = fun z : ℂ => c / ((y : ℝ) : ℂ) ^ (z + 1) := by
      funext z
      rw [Complex.cpow_neg, div_eq_mul_inv]
    rw [hfun] at h2
    convert h2 using 1
    rw [Complex.cpow_neg, ← Complex.ofReal_log hy.le, div_eq_mul_inv]
    ring
  have hderiv : ∀ w : ℂ, 0 < w.re →
      HasDerivAt (fun z : ℂ => ∫ x in Set.Ioi (n : ℝ), saw z x)
        (∫ x in Set.Ioi (n : ℝ), -((Real.log x : ℂ) * saw w x)) w := by
    intro w hw
    obtain ⟨σ₂, h2a, h2b⟩ := exists_between hw
    have hεpos : 0 < w.re - σ₂ := by linarith
    have hballre : ∀ z ∈ Metric.ball w (w.re - σ₂), σ₂ < z.re := by
      intro z hz
      rw [Metric.mem_ball] at hz
      have h := abs_lt.mp (lt_of_le_of_lt (hre_le z w) hz)
      linarith [h.1]
    have hbint : IntegrableOn (fun x : ℝ => 1 / σ₂ * x ^ (-(σ₂ / 2) - 1)) (Set.Ioi (n : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)).const_mul _
    have hbound : ∀ x : ℝ, (n : ℝ) < x → ∀ z : ℂ, σ₂ < z.re →
        ‖-((Real.log x : ℂ) * saw z x)‖ ≤ 1 / σ₂ * x ^ (-(σ₂ / 2) - 1) := by
      intro x hx z hz
      have hx1 : (1 : ℝ) ≤ x := by linarith
      have hxpos : (0 : ℝ) < x := by linarith
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
      have h1 : ‖-((Real.log x : ℂ) * saw z x)‖ ≤ Real.log x * (1 / 2 * x ^ (-(σ₂ + 1))) := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
        refine mul_le_mul_of_nonneg_left ?_ hlog
        refine le_trans (hnorm z x hxpos) ?_
        have hmono : x ^ (-(z.re + 1)) ≤ x ^ (-(σ₂ + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        linarith
      refine le_trans h1 ?_
      have h2 : Real.log x ≤ x ^ (σ₂ / 2) / (σ₂ / 2) :=
        Real.log_le_rpow_div hxpos.le (by linarith)
      have h4 : x ^ (σ₂ / 2) * x ^ (-(σ₂ + 1)) = x ^ (-(σ₂ / 2) - 1) := by
        rw [← Real.rpow_add hxpos]; ring_nf
      calc Real.log x * (1 / 2 * x ^ (-(σ₂ + 1)))
          ≤ (x ^ (σ₂ / 2) / (σ₂ / 2)) * (1 / 2 * x ^ (-(σ₂ + 1))) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 1 / σ₂ * (x ^ (σ₂ / 2) * x ^ (-(σ₂ + 1))) := by field_simp
        _ = 1 / σ₂ * x ^ (-(σ₂ / 2) - 1) := by rw [h4]
    have hmeas1 : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => -((Real.log x : ℂ) * saw z x))
        (volume.restrict (Set.Ioi (n : ℝ))) := by
      intro z
      simp only [hsaw]
      apply Measurable.aestronglyMeasurable
      fun_prop
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (n : ℝ)))
      (F := fun (z : ℂ) (x : ℝ) => saw z x)
      (F' := fun (z : ℂ) (x : ℝ) => -((Real.log x : ℂ) * saw z x))
      (x₀ := w) (bound := fun x : ℝ => 1 / σ₂ * x ^ (-(σ₂ / 2) - 1))
      (Metric.ball_mem_nhds w hεpos) ?_ (hIntC w hw) (hmeas1 w) ?_ hbint ?_
    · exact hmain.2
    · filter_upwards [Metric.ball_mem_nhds w hεpos] with z hz
      exact (hIntC z (lt_trans h2a (hballre z hz))).1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
      exact hbound x hx z (hballre z hz)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
      simp only [hsaw]
      exact hcore x (by simp only [Set.mem_Ioi] at hx; linarith) _ z
  -- ## Analytic continuation
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ {z : ℂ | 0 < z.re} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  obtain ⟨E, hE⟩ : ∃ E : ℂ → ℂ, ∀ w : ℂ, E w = riemannZeta₁ w
      - (w - 1) * ((∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-w)) + (n : ℂ) ^ (-w) / 2)
      - (n : ℂ) ^ (1 - w) + (w - 1) * w * ∫ x in Set.Ioi (n : ℝ), saw w x :=
    ⟨_, fun _ => rfl⟩
  have hEdiff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ E w := by
    intro w hw
    have hcp : ∀ (a : ℂ), a ≠ 0 → ∀ g : ℂ → ℂ, DifferentiableAt ℂ g w →
        DifferentiableAt ℂ (fun v : ℂ => a ^ g v) w := fun a ha g hg => hg.const_cpow (Or.inl ha)
    have h1 : DifferentiableAt ℂ riemannZeta₁ w := differentiable_riemannZeta₁ w
    have h2 : DifferentiableAt ℂ
        (fun v : ℂ => ∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-v)) w := by
      refine DifferentiableAt.fun_sum fun m hm => ?_
      have hm0 : (m : ℂ) ≠ 0 := by
        simp only [Finset.mem_Ico] at hm
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      exact hcp _ hm0 _ (differentiableAt_id.neg)
    have h3 : DifferentiableAt ℂ (fun v : ℂ => (n : ℂ) ^ (-v)) w :=
      hcp _ hnC _ (differentiableAt_id.neg)
    have h4 : DifferentiableAt ℂ (fun v : ℂ => (n : ℂ) ^ (1 - v)) w :=
      hcp _ hnC _ ((differentiableAt_const 1).sub differentiableAt_id)
    have h5 : DifferentiableAt ℂ (fun v : ℂ => ∫ x in Set.Ioi (n : ℝ), saw v x) w :=
      (hderiv w hw).differentiableAt
    have hall : DifferentiableAt ℂ (fun w : ℂ => riemannZeta₁ w
        - (w - 1) * ((∑ m ∈ Finset.Ico 1 n, (m : ℂ) ^ (-w)) + (n : ℂ) ^ (-w) / 2)
        - (n : ℂ) ^ (1 - w) + (w - 1) * w * ∫ x in Set.Ioi (n : ℝ), saw w x) w :=
      ((h1.sub (((differentiableAt_id.sub (differentiableAt_const 1))).mul
        (h2.add (h3.div_const 2)))).sub h4).add
        (((differentiableAt_id.sub (differentiableAt_const 1)).mul differentiableAt_id).mul h5)
    exact hall.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun v => hE v))
  have hEan : AnalyticOnNhd ℂ E {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hEdiff w hw).differentiableWithinAt) hUopen
  have hEzero : ∀ w : ℂ, 1 < w.re → E w = (0 : ℂ → ℂ) w := by
    intro w hw
    change E w = 0
    have hw1 : w ≠ 1 := by intro h; rw [h] at hw; simp at hw
    have hu' : w - (1 : ℂ) ≠ 0 := fun h => hw1 (by linear_combination h)
    have hz1 : riemannZeta₁ w = (w - 1) * riemannZeta w := by
      rw [riemannZeta_eq_inv_sub_mul hw1]
      field_simp
    rw [hE, hz1, hgt w hw]
    field_simp
    ring
  have hEqOn : Set.EqOn E 0 {z : ℂ | 0 < z.re} :=
    hEan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hUconv.isPreconnected (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re})
      (Filter.eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < (2 : ℂ).re)) hEzero)
  have hEs : E s = 0 := hEqOn hs
  rw [hE] at hEs
  have hu' : s - (1 : ℂ) ≠ 0 := fun h => hs1 (by linear_combination h)
  have hz1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    field_simp
  rw [hz1] at hEs
  field_simp at hEs ⊢
  linear_combination hEs

/-! ### Growth of `ζ` and `ζ'` near the line `re s = 1` -/

/-- **`ζ (s) - 1 / (s - 1) = O (log T)` on `[1 - 1 / log T, 2] × [-T, T]`.** There is an
absolute constant `C > 0` such that for every `T ≥ e²` and every `s` with
`1 - 1 / log T ≤ re s ≤ 2` and `|im s| ≤ T`,

`‖ζ (s) - 1 / (s - 1)‖ ≤ C * Real.log T`. -/
theorem exists_pos_norm_riemannZeta_sub_one_div_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 2 ≤ T → ∀ s : ℂ,
      1 - 1 / Real.log T ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      ‖riemannZeta s - 1 / (s - 1)‖ ≤ C * Real.log T := by
  open MeasureTheory intervalIntegral in
  -- ## A harmonic-sum bound
  have hharm : ∀ N : ℕ, 1 ≤ N → ∑ m ∈ Finset.Ico 1 (N + 1), (1 / (m : ℝ)) ≤ 1 + Real.log N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        have hstep : 1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
          have h := Real.log_le_sub_one_of_pos
            (show (0:ℝ) < (N : ℝ) / ((N : ℝ) + 1) by positivity)
          rw [Real.log_div (by positivity) (by positivity)] at h
          have he : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by
            field_simp
            ring
          rw [he] at h
          linarith
        rw [Finset.sum_Ico_succ_top (by omega)]
        push_cast
        linarith
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  refine ⟨100 + ‖riemannZeta 1‖, by positivity, ?_⟩
  intro T hT s hσ1 hσ2 hst
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hT7 : (7 : ℝ) ≤ T := le_trans he2 hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  -- ## The single point `s = 1` is absorbed into the constant
  by_cases hs1 : s = 1
  · subst hs1
    have h := mul_le_mul_of_nonneg_left hL2
      (show (0:ℝ) ≤ 100 + ‖riemannZeta 1‖ by positivity)
    simp only [sub_self, div_zero, sub_zero]
    nlinarith [norm_nonneg (riemannZeta 1)]
  have hinvL : 1 / Real.log T ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hσhalf : (1:ℝ)/2 ≤ s.re := by linarith
  have hσpos : 0 < s.re := by linarith
  -- ## The cut-off `n = ⌊T⌋₊`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊T⌋₊ := ⟨_, rfl⟩
  have hn7 : 7 ≤ n := by
    rw [hn]; exact Nat.le_floor (by push_cast; linarith)
  have hn1 : 1 ≤ n := by omega
  have hnT : (n:ℝ) ≤ T := by rw [hn]; exact Nat.floor_le hT0.le
  have hnT' : T - 1 < (n:ℝ) := by
    rw [hn]; have := Nat.lt_floor_add_one T; linarith
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0R : (0:ℝ) < (n:ℝ) := by linarith
  -- ## The pointwise bound `x ^ (-σ) ≤ e / x` for `1 ≤ x ≤ T`
  have hpt : ∀ x : ℝ, 1 ≤ x → x ≤ T → x ^ (-s.re) ≤ Real.exp 1 * x⁻¹ := by
    intro x hx1 hxT
    have hx0 : (0:ℝ) < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogxT : Real.log x ≤ Real.log T := Real.log_le_log hx0 hxT
    have h1 : x ^ (1 - s.re) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hx0]
      refine Real.exp_le_exp.mpr ?_
      rcases le_or_gt (1 - s.re) 0 with h | h
      · nlinarith
      · have h2 : 1 - s.re ≤ 1 / Real.log T := by linarith
        have h3 : Real.log x * (1 - s.re) ≤ Real.log T * (1 / Real.log T) := by
          nlinarith
        rw [mul_one_div, div_self hL0.ne'] at h3
        exact h3
    have h3 : x ^ (-s.re) = x ^ (1 - s.re) * x⁻¹ := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]
      ring_nf
    rw [h3]
    have hxi : (0:ℝ) < x⁻¹ := by positivity
    nlinarith
  -- ## Norms of complex powers
  have hnormcast : ∀ (m : ℕ), 1 ≤ m → ‖(m : ℂ) ^ (-s)‖ = (m : ℝ) ^ (-s.re) := by
    intro m hm
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hmpos, Complex.neg_re]
  -- ## Bound on the finite sum
  have hsumharm : ∑ m ∈ Finset.Ico 1 n, (1 / (m:ℝ)) ≤ 1 + Real.log T := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N + 1 := ⟨n - 1, by omega⟩
    have hNpos : (0:ℝ) < (N:ℝ) := by
      have : 6 ≤ N := by omega
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    have hNT : (N:ℝ) ≤ T := by
      have : (N:ℝ) + 1 = (n:ℝ) := by rw [hN]; push_cast; ring
      linarith
    have h1 := hharm N (by omega)
    rw [hN]
    exact h1.trans (by linarith [Real.log_le_log hNpos hNT])
  have hA : ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖ ≤ Real.exp 1 * (1 + Real.log T) := by
    calc ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖
        ≤ ∑ m ∈ Finset.Ico 1 n, ‖(m:ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ico 1 n, Real.exp 1 * (1 / (m:ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          simp only [Finset.mem_Ico] at hm
          have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
          have hmT : (m:ℝ) ≤ T := by
            have : (m:ℝ) < (n:ℝ) := by exact_mod_cast hm.2
            linarith
          rw [hnormcast m hm.1, one_div]
          exact hpt m hm1 hmT
      _ = Real.exp 1 * ∑ m ∈ Finset.Ico 1 n, (1 / (m:ℝ)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp 1 * (1 + Real.log T) := by
          exact mul_le_mul_of_nonneg_left hsumharm hexp0.le
  -- ## Bound on the half-term
  have hB : ‖(n:ℂ) ^ (-s) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, hnormcast n hn1]
    have h1 : (n:ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  -- ## The pole term, via the integral representation
  have hnot0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) (n:ℝ) := fun h => by
    rw [Set.uIcc_of_le hn1R] at h; linarith [h.1]
  have hsne : (-s) ≠ -1 := fun h => hs1 (by linear_combination -h)
  have hint1 : IntervalIntegrable (fun x : ℝ => ‖(x:ℂ) ^ (-s)‖) volume 1 (n:ℝ) :=
    (intervalIntegrable_cpow (Or.inr hnot0)).norm
  have hint2 : IntervalIntegrable (fun x : ℝ => Real.exp 1 * x⁻¹) volume 1 (n:ℝ) :=
    (continuousOn_const.mul ((continuousOn_id (α := ℝ)).inv₀ fun x hx =>
      (ne_of_mem_of_not_mem hx hnot0 : x ≠ 0))).intervalIntegrable
  have hcpow : ∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-s)
      = ((n:ℂ) ^ (1 - s) - 1) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨hsne, hnot0⟩), show -s + 1 = 1 - s by ring]
    norm_num
  have hDeq : ((n:ℂ) ^ (1 - s) - 1) / (s - 1)
      = -(∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-s)) := by
    rw [hcpow, show s - 1 = -(1 - s) by ring, div_neg]
  have hD : ‖((n:ℂ) ^ (1 - s) - 1) / (s - 1)‖ ≤ Real.exp 1 * Real.log T := by
    rw [hDeq, norm_neg]
    calc ‖∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-s)‖
        ≤ ∫ x : ℝ in (1:ℝ)..(n:ℝ), ‖(x:ℂ) ^ (-s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hn1R
      _ ≤ ∫ x : ℝ in (1:ℝ)..(n:ℝ), Real.exp 1 * x⁻¹ := by
          refine intervalIntegral.integral_mono_on hn1R hint1 hint2 ?_
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          have hx0 : (0:ℝ) < x := by linarith
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
          exact hpt x hx1 (by linarith)
      _ = Real.exp 1 * Real.log ((n:ℝ) / 1) := by
          rw [intervalIntegral.integral_const_mul, integral_inv hnot0]
      _ ≤ Real.exp 1 * Real.log T := by
          rw [div_one]
          exact mul_le_mul_of_nonneg_left (Real.log_le_log hn0R hnT) hexp0.le
  -- ## The sawtooth tail
  have hnpow : T / 6 ≤ (n:ℝ) ^ s.re := by
    have h1 : (n:ℝ) ^ (1 - 1 / Real.log T) ≤ (n:ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hn1R hσ1
    have h2 : (n:ℝ) ^ (1 - 1 / Real.log T) = (n:ℝ) / (n:ℝ) ^ (1 / Real.log T) := by
      rw [Real.rpow_sub hn0R, Real.rpow_one]
    have h3 : (n:ℝ) ^ (1 / Real.log T) ≤ Real.exp 1 := by
      calc (n:ℝ) ^ (1 / Real.log T) ≤ T ^ (1 / Real.log T) :=
            Real.rpow_le_rpow hn0R.le hnT (by positivity)
        _ = Real.exp 1 := by
            rw [Real.rpow_def_of_pos hT0, mul_one_div, div_self hL0.ne']
    have hpos : (0:ℝ) < (n:ℝ) ^ (1 / Real.log T) := Real.rpow_pos_of_pos hn0R _
    have h4 : T / 6 ≤ (n:ℝ) / (n:ℝ) ^ (1 / Real.log T) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]
      nlinarith
    linarith [h2 ▸ h1]
  have hE : ‖s * ∫ x in Set.Ioi (n:ℝ),
      ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤ 10 := by
    refine (norm_mul_integral_sawtooth_le hσpos hn1).trans ?_
    have hden : (0:ℝ) < 2 * s.re * (n:ℝ) ^ s.re := by
      have : (0:ℝ) < (n:ℝ) ^ s.re := Real.rpow_pos_of_pos hn0R _
      positivity
    rw [div_le_iff₀ hden]
    have hnorms : ‖s‖ ≤ 2 + T := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      have : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, hσ2⟩
      linarith
    nlinarith
  -- ## Put the pieces together
  have hEM := riemannZeta_eq_sum_add_integral_sawtooth
    hσpos hs1 hn1
  have hdecomp : riemannZeta s - 1 / (s - 1)
      = (∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)) + (n:ℂ) ^ (-s) / 2
        + ((n:ℂ) ^ (1 - s) - 1) / (s - 1)
        - s * ∫ x in Set.Ioi (n:ℝ),
            ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1) := by
    rw [hEM, sub_div]
    ring
  have htri : ‖riemannZeta s - 1 / (s - 1)‖
      ≤ ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖ + ‖(n:ℂ) ^ (-s) / 2‖
        + ‖((n:ℂ) ^ (1 - s) - 1) / (s - 1)‖
        + ‖s * ∫ x in Set.Ioi (n:ℝ),
            ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ := by
    rw [hdecomp]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ le_rfl
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (norm_add_le _ _) le_rfl
  have hfin : Real.exp 1 * Real.log T ≤ 2.7182818286 * Real.log T :=
    mul_le_mul_of_nonneg_right hexp.le hL0.le
  have hCl : 100 * Real.log T ≤ (100 + ‖riemannZeta 1‖) * Real.log T :=
    mul_le_mul_of_nonneg_right (by linarith [norm_nonneg (riemannZeta 1)]) hL0.le
  linarith

/-- **`ζ (s) = O (log T)` on the boundary of `[1 - 1 / log T, 2] × [-T, T]`.** There is an
absolute constant `C > 0` such that for every `T ≥ e²` and every `s` on the frontier of the
rectangle `[1 - 1 / log T, 2] × [-T, T]`,

`‖ζ (s)‖ ≤ C * Real.log T`. -/
theorem exists_pos_norm_riemannZeta_le_mul_log_of_mem_frontier :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 2 ≤ T →
      ∀ s ∈ frontier (Icc (1 - 1 / Real.log T) 2 ×ℂ Icc (-T) T),
      ‖riemannZeta s‖ ≤ C * Real.log T := by
  -- The boundary sits inside the rectangle, where the bound for `ζ (s) - 1 / (s - 1)` applies
  obtain ⟨C, hC0, hC⟩ := exists_pos_norm_riemannZeta_sub_one_div_le_mul_log
  refine ⟨C + 1, by linarith, ?_⟩
  intro T hT s hs
  obtain ⟨⟨hs1, hs2, hs3⟩, -⟩ := mem_and_not_mem_of_mem_frontier hs
  -- `ζ (s) = (ζ (s) - 1 / (s - 1)) + 1 / (s - 1)`, and both pieces are `O (log T)`
  have h1 := hC T hT s hs1 hs2 hs3
  have h2 := norm_one_div_sub_one_le_log_of_mem_frontier hT hs
  have h3 : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := by
    simpa using norm_add_le (riemannZeta s - 1 / (s - 1)) (1 / (s - 1))
  have h4 : (C + 1) * Real.log T = C * Real.log T + Real.log T := by ring
  linarith

/-- **The convexity bound `ζ (s) = O (|t| ^ (1 / 2))`.** There are absolute constants `C > 0`
and `T₀ > 0` such that for every `s` with `re s ≥ 1 / 2` and `|im s| ≥ T₀`,

`‖ζ (s)‖ ≤ C * |Complex.im s| ^ (1 / 2 : ℝ)`. -/
theorem exists_pos_norm_riemannZeta_le_mul_abs_im_rpow_half :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → T₀ ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (1 / 2 : ℝ) := by
  -- ## `∑_{1 ≤ m ≤ N} m ^ (-1/2) ≤ 2 √N`, by induction on `N`
  have hsqrtsum : ∀ N : ℕ, ∑ m ∈ Finset.Ico 1 (N + 1), (m : ℝ) ^ (-(1/2) : ℝ)
      ≤ 2 * Real.sqrt (N : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have ha : (0:ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        have hb : (0:ℝ) < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have ha2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
        have hb2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
        have hterm : ((N : ℝ) + 1) ^ (-(1/2) : ℝ) = (Real.sqrt ((N : ℝ) + 1))⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
        have hstep : (Real.sqrt ((N : ℝ) + 1))⁻¹
            ≤ 2 * Real.sqrt ((N : ℝ) + 1) - 2 * Real.sqrt (N : ℝ) := by
          rw [inv_eq_one_div, div_le_iff₀ hb]
          nlinarith [sq_nonneg (Real.sqrt ((N:ℝ) + 1) - Real.sqrt (N:ℝ))]
        have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [Finset.sum_Ico_succ_top (by omega), hcast, hterm]
        linarith
  refine ⟨6, 4, by norm_num, by norm_num, ?_⟩
  intro s hσ ht
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = |s.im| := ⟨_, rfl⟩
  rw [← hTdef] at ht ⊢
  have hT4 : (4:ℝ) ≤ T := ht
  have hT0 : (0:ℝ) < T := by linarith
  have hσpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hTdef
    simp at hTdef
    linarith
  -- ## The cut-off `n = ⌊T⌋₊`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊T⌋₊ := ⟨_, rfl⟩
  have hn4 : 4 ≤ n := by rw [hn]; exact Nat.le_floor (by push_cast; linarith)
  have hn1 : 1 ≤ n := by omega
  have hnT : (n:ℝ) ≤ T := by rw [hn]; exact Nat.floor_le hT0.le
  have hnT' : T - 1 < (n:ℝ) := by
    rw [hn]; have := Nat.lt_floor_add_one T; linarith
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0R : (0:ℝ) < (n:ℝ) := by linarith
  have hsT : (2:ℝ) ≤ Real.sqrt T := by
    nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T]
  have hnormcast : ∀ (m : ℕ), 1 ≤ m → ∀ w : ℂ, ‖(m : ℂ) ^ w‖ = (m : ℝ) ^ w.re := by
    intro m hm w
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
  -- ## The finite sum, bounded by `2 √T` since `σ ≥ 1 / 2`
  have hA : ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖ ≤ 2 * Real.sqrt T := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N + 1 := ⟨n - 1, by omega⟩
    have hNT : (N:ℝ) ≤ T := by
      have hcast : (N:ℝ) + 1 = (n:ℝ) := by rw [hN]; push_cast; ring
      linarith
    calc ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖
        ≤ ∑ m ∈ Finset.Ico 1 n, ‖(m:ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ico 1 n, (m:ℝ) ^ (-(1/2) : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          simp only [Finset.mem_Ico] at hm
          have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
          rw [hnormcast m hm.1, Complex.neg_re]
          exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      _ ≤ 2 * Real.sqrt (N:ℝ) := by rw [hN]; exact hsqrtsum N
      _ ≤ 2 * Real.sqrt T := by
          have h := Real.sqrt_le_sqrt hNT
          linarith
  -- ## The half-term
  have hB : ‖(n:ℂ) ^ (-s) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, hnormcast n hn1, Complex.neg_re]
    have h1 : (n:ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
    have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2]; linarith
  -- ## The pole term: `n ^ (1 - σ) ≤ √T` against `‖s - 1‖ ≥ T`
  have him : T ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
    rw [hTdef]; exact h
  have hC : ‖(n:ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    have hnum : ‖(n:ℂ) ^ (1 - s)‖ ≤ Real.sqrt T := by
      rw [hnormcast n hn1, Complex.sub_re, Complex.one_re]
      calc (n:ℝ) ^ (1 - s.re) ≤ (n:ℝ) ^ ((1:ℝ)/2) :=
            Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
        _ = Real.sqrt (n:ℝ) := (Real.sqrt_eq_rpow _).symm
        _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hnT
    have hpos : (0:ℝ) < ‖s - 1‖ := lt_of_lt_of_le hT0 him
    rw [norm_div, div_le_one hpos]
    have hsq : Real.sqrt T ≤ T := by
      nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T]
    linarith
  -- ## The sawtooth tail: `‖s‖ / (2 σ n ^ σ) ≤ 1 / 2 + 2 √T`
  have hD : ‖s * ∫ x in Set.Ioi (n:ℝ),
      ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ ≤ 1 / 2 + 2 * Real.sqrt T := by
    refine (norm_mul_integral_sawtooth_le hσpos hn1).trans ?_
    have hnpow : Real.sqrt (n:ℝ) ≤ (n:ℝ) ^ s.re := by
      calc Real.sqrt (n:ℝ) = (n:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
        _ ≤ (n:ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
    have hsqn : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0R
    have hpowpos : (0:ℝ) < (n:ℝ) ^ s.re := lt_of_lt_of_le hsqn hnpow
    have hn1pow : (1:ℝ) ≤ (n:ℝ) ^ s.re := by
      have h := Real.rpow_le_rpow_of_exponent_le hn1R hσpos.le
      rwa [Real.rpow_zero] at h
    have hnorms : ‖s‖ ≤ s.re + T := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hTdef, abs_of_pos hσpos]
    have h2uv : Real.sqrt T ≤ 2 * Real.sqrt (n:ℝ) := by
      have h1 : Real.sqrt T ≤ Real.sqrt (4 * (n:ℝ)) := Real.sqrt_le_sqrt (by linarith)
      rwa [show (4:ℝ) * (n:ℝ) = 2 ^ 2 * (n:ℝ) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)] at h1
    have hTle : T ≤ 2 * Real.sqrt T * Real.sqrt (n:ℝ) := by
      nlinarith [Real.sq_sqrt hT0.le, Real.sqrt_nonneg T]
    have hden : (0:ℝ) < 2 * s.re * (n:ℝ) ^ s.re := by positivity
    rw [div_le_iff₀ hden]
    have e1 : s.re ≤ s.re * (n:ℝ) ^ s.re := le_mul_of_one_le_right hσpos.le hn1pow
    have e2 : Real.sqrt T * Real.sqrt (n:ℝ) ≤ 2 * (Real.sqrt T * (s.re * (n:ℝ) ^ s.re)) := by
      have haux : (0:ℝ) ≤ (s.re - 1/2) * (n:ℝ) ^ s.re :=
        mul_nonneg (by linarith) hpowpos.le
      have h1 : Real.sqrt (n:ℝ) ≤ 2 * (s.re * (n:ℝ) ^ s.re) := by linarith
      linarith [mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg T)]
    linarith
  -- ## Put the pieces together
  have hEM := riemannZeta_eq_sum_add_integral_sawtooth
    hσpos hs1 hn1
  have htri : ‖riemannZeta s‖
      ≤ ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-s)‖ + ‖(n:ℂ) ^ (-s) / 2‖
        + ‖(n:ℂ) ^ (1 - s) / (s - 1)‖
        + ‖s * ∫ x in Set.Ioi (n:ℝ),
            ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)‖ := by
    rw [hEM]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ?_ le_rfl
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (norm_add_le _ _) le_rfl
  have hgoal : (6:ℝ) * T ^ (1/2 : ℝ) = 6 * Real.sqrt T := by rw [Real.sqrt_eq_rpow]
  rw [hgoal]
  linarith

/-- **`ζ' (s) + 1 / (s - 1) ^ 2 = O (log ^ 2 T)` on `[1 - 1 / log T, 2] × [-T, T]`.** There
is an absolute constant `C > 0` such that for every `T ≥ e²` and every `s` with
`1 - 1 / log T ≤ re s ≤ 2` and `|im s| ≤ T`,

`‖ζ' (s) + 1 / (s - 1) ^ 2‖ ≤ C * Real.log T ^ 2`. -/
theorem exists_pos_norm_deriv_riemannZeta_add_one_div_sq_le_mul_log_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 2 ≤ T → ∀ s : ℂ,
      1 - 1 / Real.log T ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      ‖deriv riemannZeta s + 1 / (s - 1) ^ 2‖ ≤ C * Real.log T ^ 2 := by
  open MeasureTheory intervalIntegral in
  -- ## A harmonic-sum bound
  have hharm : ∀ N : ℕ, 1 ≤ N → ∑ m ∈ Finset.Ico 1 (N + 1), (1 / (m : ℝ)) ≤ 1 + Real.log N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        have hstep : 1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
          have h := Real.log_le_sub_one_of_pos
            (show (0:ℝ) < (N : ℝ) / ((N : ℝ) + 1) by positivity)
          rw [Real.log_div (by positivity) (by positivity)] at h
          have he : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by
            field_simp
            ring
          rw [he] at h
          linarith
        rw [Finset.sum_Ico_succ_top (by omega)]
        push_cast
        linarith
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE2 : Real.exp 2 ≤ 8 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  refine ⟨100 + ‖deriv riemannZeta 1‖ + ‖riemannZeta₀ 1‖, by positivity, ?_⟩
  intro T hT s hσ1 hσ2 hst
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hT7 : (7 : ℝ) ≤ T := le_trans he2 hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hLne : Real.log T ≠ 0 := ne_of_gt hL0
  -- ## The single point `s = 1` is absorbed into the constant
  by_cases hs1 : s = 1
  · subst hs1
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      add_zero]
    nlinarith [norm_nonneg (deriv riemannZeta 1), norm_nonneg (riemannZeta₀ 1),
      mul_nonneg (norm_nonneg (deriv riemannZeta 1))
        (show (0:ℝ) ≤ Real.log T ^ 2 - 4 by nlinarith),
      mul_nonneg (norm_nonneg (riemannZeta₀ 1))
        (show (0:ℝ) ≤ Real.log T ^ 2 by positivity)]
  -- ## The cut-off `n = ⌊T⌋₊`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊T⌋₊ := ⟨_, rfl⟩
  have hn7 : 7 ≤ n := by
    rw [hn]; exact Nat.le_floor (by push_cast; linarith)
  have hn1 : 1 ≤ n := by omega
  have hnT : (n:ℝ) ≤ T := by rw [hn]; exact Nat.floor_le hT0.le
  have hnT' : T - 1 < (n:ℝ) := by
    rw [hn]; have := Nat.lt_floor_add_one T; linarith
  have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hn0R : (0:ℝ) < (n:ℝ) := by linarith
  have hsumharm : ∑ m ∈ Finset.Ico 1 n, (1 / (m:ℝ)) ≤ 1 + Real.log T := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N + 1 := ⟨n - 1, by omega⟩
    have hNpos : (0:ℝ) < (N:ℝ) := by
      have : 6 ≤ N := by omega
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    have hNT : (N:ℝ) ≤ T := by
      have : (N:ℝ) + 1 = (n:ℝ) := by rw [hN]; push_cast; ring
      linarith
    have h1 := hharm N (by omega)
    rw [hN]
    exact h1.trans (by linarith [Real.log_le_log hNpos hNT])
  -- ## The growth bound on a rectangle slightly larger than `R_T`
  have hgrowth : ∀ z : ℂ, z ≠ 1 → 1 - 3 / (2 * Real.log T) ≤ z.re → z.re ≤ 3 →
      |z.im| ≤ T + 1 → ‖riemannZeta z - 1 / (z - 1)‖ ≤ 40 * Real.log T := by
    intro z hz1 hzl hzr hzi
    have h34 : 3 / (2 * Real.log T) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hσ14 : (1:ℝ)/4 ≤ z.re := by linarith
    have hσpos : 0 < z.re := by linarith
    -- ### The pointwise bound `x ^ (-σ) ≤ 8 / x` for `1 ≤ x ≤ T`
    have hpt : ∀ x : ℝ, 1 ≤ x → x ≤ T → x ^ (-z.re) ≤ 8 * x⁻¹ := by
      intro x hx1 hxT
      have hx0 : (0:ℝ) < x := by linarith
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
      have hlogxT : Real.log x ≤ Real.log T := Real.log_le_log hx0 hxT
      have h1 : x ^ (1 - z.re) ≤ 8 := by
        rw [Real.rpow_def_of_pos hx0]
        refine le_trans (Real.exp_le_exp.mpr ?_) hE2
        rcases le_or_gt (1 - z.re) 0 with h | h
        · nlinarith
        · have h2 : 1 - z.re ≤ 3 / (2 * Real.log T) := by linarith
          have h3 : Real.log x * (1 - z.re) ≤ Real.log T * (3 / (2 * Real.log T)) := by
            nlinarith
          have h4 : Real.log T * (3 / (2 * Real.log T)) = 3 / 2 := by
            field_simp
          linarith
      have h3 : x ^ (-z.re) = x ^ (1 - z.re) * x⁻¹ := by
        rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]
        ring_nf
      rw [h3]
      have hxi : (0:ℝ) < x⁻¹ := by positivity
      nlinarith
    have hnormcast : ∀ (m : ℕ), 1 ≤ m → ‖(m : ℂ) ^ (-z)‖ = (m : ℝ) ^ (-z.re) := by
      intro m hm
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      rw [show ((m : ℕ) : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hmpos, Complex.neg_re]
    -- ### The finite sum
    have hA : ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-z)‖ ≤ 8 * (1 + Real.log T) := by
      calc ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-z)‖
          ≤ ∑ m ∈ Finset.Ico 1 n, ‖(m:ℂ) ^ (-z)‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Finset.Ico 1 n, 8 * (1 / (m:ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            simp only [Finset.mem_Ico] at hm
            have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
            have hmT : (m:ℝ) ≤ T := by
              have : (m:ℝ) < (n:ℝ) := by exact_mod_cast hm.2
              linarith
            rw [hnormcast m hm.1, one_div]
            exact hpt m hm1 hmT
        _ = 8 * ∑ m ∈ Finset.Ico 1 n, (1 / (m:ℝ)) := by rw [Finset.mul_sum]
        _ ≤ 8 * (1 + Real.log T) := by linarith
    -- ### The half-term
    have hB : ‖(n:ℂ) ^ (-z) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, hnormcast n hn1]
      have h1 : (n:ℝ) ^ (-z.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith
    -- ### The pole term, via the integral representation
    have hnot0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) (n:ℝ) := fun h => by
      rw [Set.uIcc_of_le hn1R] at h; linarith [h.1]
    have hsne : (-z) ≠ -1 := fun h => hz1 (by linear_combination -h)
    have hint1 : IntervalIntegrable (fun x : ℝ => ‖(x:ℂ) ^ (-z)‖) volume 1 (n:ℝ) :=
      (intervalIntegrable_cpow (Or.inr hnot0)).norm
    have hint2 : IntervalIntegrable (fun x : ℝ => 8 * x⁻¹) volume 1 (n:ℝ) :=
      (continuousOn_const.mul ((continuousOn_id (α := ℝ)).inv₀ fun x hx =>
        (ne_of_mem_of_not_mem hx hnot0 : x ≠ 0))).intervalIntegrable
    have hcpow : ∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-z)
        = ((n:ℂ) ^ (1 - z) - 1) / (1 - z) := by
      rw [integral_cpow (Or.inr ⟨hsne, hnot0⟩), show -z + 1 = 1 - z by ring]
      norm_num
    have hDeq : ((n:ℂ) ^ (1 - z) - 1) / (z - 1)
        = -(∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-z)) := by
      rw [hcpow, show z - 1 = -(1 - z) by ring, div_neg]
    have hD : ‖((n:ℂ) ^ (1 - z) - 1) / (z - 1)‖ ≤ 8 * Real.log T := by
      rw [hDeq, norm_neg]
      calc ‖∫ x : ℝ in (1:ℝ)..(n:ℝ), (x:ℂ) ^ (-z)‖
          ≤ ∫ x : ℝ in (1:ℝ)..(n:ℝ), ‖(x:ℂ) ^ (-z)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hn1R
        _ ≤ ∫ x : ℝ in (1:ℝ)..(n:ℝ), 8 * x⁻¹ := by
            refine intervalIntegral.integral_mono_on hn1R hint1 hint2 ?_
            intro x hx
            obtain ⟨hx1, hx2⟩ := hx
            have hx0 : (0:ℝ) < x := by linarith
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.neg_re]
            exact hpt x hx1 (by linarith)
        _ = 8 * Real.log ((n:ℝ) / 1) := by
            rw [intervalIntegral.integral_const_mul, integral_inv hnot0]
        _ ≤ 8 * Real.log T := by
            rw [div_one]
            exact mul_le_mul_of_nonneg_left (Real.log_le_log hn0R hnT) (by norm_num)
    -- ### The sawtooth tail
    have hnpow : (T - 1) / 8 ≤ (n:ℝ) ^ z.re := by
      have h1 : (n:ℝ) ^ (1 - 3 / (2 * Real.log T)) ≤ (n:ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hn1R hzl
      have h2 : (n:ℝ) ^ (1 - 3 / (2 * Real.log T))
          = (n:ℝ) / (n:ℝ) ^ (3 / (2 * Real.log T)) := by
        rw [Real.rpow_sub hn0R, Real.rpow_one]
      have h3 : (n:ℝ) ^ (3 / (2 * Real.log T)) ≤ 8 := by
        calc (n:ℝ) ^ (3 / (2 * Real.log T)) ≤ T ^ (3 / (2 * Real.log T)) :=
              Real.rpow_le_rpow hn0R.le hnT (by positivity)
          _ = Real.exp (3 / 2) := by
              rw [Real.rpow_def_of_pos hT0]
              congr 1
              field_simp
          _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 8 := hE2
      have hpos : (0:ℝ) < (n:ℝ) ^ (3 / (2 * Real.log T)) := Real.rpow_pos_of_pos hn0R _
      have h4 : (T - 1) / 8 ≤ (n:ℝ) / (n:ℝ) ^ (3 / (2 * Real.log T)) := by
        rw [div_le_div_iff₀ (by norm_num) hpos]
        nlinarith
      linarith [h2 ▸ h1]
    have hE : ‖z * ∫ x in Set.Ioi (n:ℝ),
        ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1)‖ ≤ 30 := by
      refine (norm_mul_integral_sawtooth_le hσpos hn1).trans ?_
      have hnp0 : (0:ℝ) < (n:ℝ) ^ z.re := Real.rpow_pos_of_pos hn0R _
      have hden : (0:ℝ) < 2 * z.re * (n:ℝ) ^ z.re := by positivity
      rw [div_le_iff₀ hden]
      have hnorms : ‖z‖ ≤ T + 4 := by
        refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
        have h5 : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith, hzr⟩
        linarith
      have hprod : (1/4) * ((T - 1)/8) ≤ z.re * (n:ℝ) ^ z.re :=
        mul_le_mul hσ14 hnpow (by linarith) (by linarith)
      nlinarith
    -- ### Put the pieces together
    have hEM := riemannZeta_eq_sum_add_integral_sawtooth
      hσpos hz1 hn1
    have hdecomp : riemannZeta z - 1 / (z - 1)
        = (∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-z)) + (n:ℂ) ^ (-z) / 2
          + ((n:ℂ) ^ (1 - z) - 1) / (z - 1)
          - z * ∫ x in Set.Ioi (n:ℝ),
              ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1) := by
      rw [hEM, sub_div]
      ring
    have htri : ‖riemannZeta z - 1 / (z - 1)‖
        ≤ ‖∑ m ∈ Finset.Ico 1 n, (m:ℂ) ^ (-z)‖ + ‖(n:ℂ) ^ (-z) / 2‖
          + ‖((n:ℂ) ^ (1 - z) - 1) / (z - 1)‖
          + ‖z * ∫ x in Set.Ioi (n:ℝ),
              ((x - (⌊x⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (x : ℂ) ^ (z + 1)‖ := by
      rw [hdecomp]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      refine (norm_add_le _ _).trans ?_
      exact add_le_add (norm_add_le _ _) le_rfl
    linarith
  -- ## Cauchy's estimate on the disc of radius `1 / (2 log T)` about `s`
  have hquarter : 1 / (2 * Real.log T) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hr : (0:ℝ) < 1 / (2 * Real.log T) := by positivity
  have hsph : ∀ w ∈ Metric.sphere s (1 / (2 * Real.log T)),
      ‖riemannZeta₀ w‖ ≤ 40 * Real.log T + ‖riemannZeta₀ 1‖ := by
    intro w hw
    have hdw : ‖w - s‖ = 1 / (2 * Real.log T) := by
      rw [← Complex.dist_eq]; exact Metric.mem_sphere.mp hw
    have hre : |w.re - s.re| ≤ 1 / (2 * Real.log T) := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [Complex.sub_re, hdw] at h
      exact h
    have him : |w.im - s.im| ≤ 1 / (2 * Real.log T) := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [Complex.sub_im, hdw] at h
      exact h
    by_cases hw1 : w = 1
    · subst hw1
      nlinarith [norm_nonneg (riemannZeta₀ 1)]
    · have hrw : riemannZeta₀ w = riemannZeta w - 1 / (w - 1) := by
        rw [riemannZeta_eq_inv_sub_add hw1, one_div]
        ring
      rw [hrw]
      refine le_trans (hgrowth w hw1 ?_ ?_ ?_)
        (by linarith [norm_nonneg (riemannZeta₀ 1)])
      · have h1 : 1 / Real.log T + 1 / (2 * Real.log T) = 3 / (2 * Real.log T) := by
          field_simp
          ring
        have h2 := (abs_le.mp hre).1
        linarith
      · have h2 := (abs_le.mp hre).2
        linarith
      · have h2 := abs_sub_abs_le_abs_sub w.im s.im
        linarith [(abs_le.mp him).2, abs_nonneg (w.im - s.im)]
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (differentiable_riemannZeta₀.diffContOnCl
      (s := Metric.ball s (1 / (2 * Real.log T)))) hsph
  have hdiv : (40 * Real.log T + ‖riemannZeta₀ 1‖) / (1 / (2 * Real.log T))
      = (40 * Real.log T + ‖riemannZeta₀ 1‖) * (2 * Real.log T) := by
    field_simp
  rw [hdiv] at hcauchy
  have hkey : deriv riemannZeta s + 1 / (s - 1) ^ 2 = deriv riemannZeta₀ s := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_add hs1, inv_pow, one_div]
    ring
  rw [hkey]
  have hprod1 : (0:ℝ) ≤ ‖riemannZeta₀ 1‖ * Real.log T * (Real.log T - 2) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hL0.le) (by linarith)
  have hprod2 : (0:ℝ) ≤ ‖deriv riemannZeta 1‖ * Real.log T ^ 2 :=
    mul_nonneg (norm_nonneg _) (sq_nonneg _)
  nlinarith [hcauchy, sq_nonneg (Real.log T)]

/-- **`ζ' (s) = O (log ^ 2 T)` on the boundary of `[1 - 1 / log T, 2] × [-T, T]`.** There is
an absolute constant `C > 0` such that for every `T ≥ e²` and every `s` on the frontier of
the rectangle `[1 - 1 / log T, 2] × [-T, T]`,

`‖ζ' (s)‖ ≤ C * Real.log T ^ 2`.

`riemannZeta` is differentiable on `ℂ \ {1}` and `s = 1` is interior to the rectangle,
so `deriv riemannZeta s` is the honest derivative at every `s` quantified over here. -/
theorem exists_pos_norm_deriv_riemannZeta_le_mul_log_sq_of_mem_frontier :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, Real.exp 2 ≤ T →
      ∀ s ∈ frontier (Icc (1 - 1 / Real.log T) 2 ×ℂ Icc (-T) T),
      ‖deriv riemannZeta s‖ ≤ C * Real.log T ^ 2 := by
  -- The bound for `ζ' (s) + 1 / (s - 1) ^ 2`, plus the squared pole bound on the boundary
  obtain ⟨C, hC0, hC⟩ := exists_pos_norm_deriv_riemannZeta_add_one_div_sq_le_mul_log_sq
  refine ⟨C + 1, by linarith, ?_⟩
  intro T hT s hs
  obtain ⟨⟨hs1, hs2, hs3⟩, -⟩ := mem_and_not_mem_of_mem_frontier hs
  have h1 := hC T hT s hs1 hs2 hs3
  have h2 := norm_one_div_sub_one_le_log_of_mem_frontier hT hs
  have h2' : ‖1 / (s - 1) ^ 2‖ ≤ Real.log T ^ 2 := by
    have he : ‖1 / (s - 1) ^ 2‖ = ‖1 / (s - 1)‖ ^ 2 := by
      rw [one_div, one_div, norm_inv, norm_inv, norm_pow, inv_pow]
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3 : ‖deriv riemannZeta s‖ ≤
      ‖deriv riemannZeta s + 1 / (s - 1) ^ 2‖ + ‖1 / (s - 1) ^ 2‖ := by
    have h := norm_sub_le (deriv riemannZeta s + 1 / (s - 1) ^ 2) (1 / (s - 1) ^ 2)
    rwa [add_sub_cancel_right] at h
  have h4 : (C + 1) * Real.log T ^ 2 = C * Real.log T ^ 2 + Real.log T ^ 2 := by ring
  linarith

/-! ### A zero-free region -/

/-- **The `3-4-1` inequality for `ζ`.** For `σ > 1` and real `t`,
`‖ζ (σ) ^ 3 * ζ (σ + i t) ^ 4 * ζ (σ + 2 i t)‖ ≥ 1`. -/
theorem one_le_norm_riemannZeta_pow_three_mul {σ t : ℝ} (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta (σ : ℂ) ^ 3 * riemannZeta ((σ : ℂ) + t * I) ^ 4 *
        riemannZeta ((σ : ℂ) + 2 * t * I)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) 1
    (x := σ - 1) (by linarith) t
  simp only [DirichletCharacter.LFunctionTrivChar, one_pow,
    DirichletCharacter.LFunction_modOne_eq] at h
  convert h using 5 <;> push_cast <;> ring_nf

/-- **A zero-free region for `ζ`.** There are absolute constants `c₁ > 0` and
`c₂ > 0` such that for every `T ≥ Real.exp 2` and every `s = σ + i t` with `1 ≤ |t| ≤ T` and
`1 - c₁ / log ^ 9 T ≤ σ ≤ 2`,

`‖ζ (s)‖ > c₂ / log T ^ 7`. -/
theorem exists_pos_div_log_pow_seven_lt_norm_riemannZeta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ T : ℝ, Real.exp 2 ≤ T → ∀ s : ℂ, 1 ≤ |s.im| → |s.im| ≤ T →
      1 - c₁ / Real.log T ^ 9 ≤ s.re → s.re ≤ 2 →
        c₂ / Real.log T ^ 7 < ‖riemannZeta s‖ := by
  -- ## The three constants the argument needs
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_pos_norm_riemannZeta_sub_one_div_le_mul_log
  obtain ⟨C₅, hC₅0, hC₅⟩ :=
    exists_pos_norm_deriv_riemannZeta_add_one_div_sq_le_mul_log_sq
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, 1 ≤ B ∧ B = 2 * C₀ + 1 := ⟨_, by linarith, rfl⟩
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ M = C₅ + 1 := ⟨_, by linarith, rfl⟩
  obtain ⟨c₁, hc₁0, hc₁⟩ : ∃ c : ℝ, 0 < c ∧ 2048 * B * M ^ 4 * c = 1 := by
    have hpos : (0:ℝ) < 2048 * B * M ^ 4 := by positivity
    exact ⟨1 / (2048 * B * M ^ 4), by positivity, by field_simp⟩
  have hM4 : (1:ℝ) ≤ M ^ 4 := one_le_pow₀ hM1
  have hc₁1 : c₁ ≤ 1 / 2048 := by
    have hBM : (1:ℝ) ≤ B * M ^ 4 := by nlinarith
    linarith [mul_le_mul_of_nonneg_right hBM hc₁0.le]
  refine ⟨c₁, c₁ * M, hc₁0, by positivity, ?_⟩
  intro T hT s him1 himT hσl hσu
  -- ## Basic facts about `T` and `log T`
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hT7 : (7 : ℝ) ≤ T := le_trans he2 hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hL2 : (2 : ℝ) ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hT
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  have hL8 : (256 : ℝ) ≤ Real.log T ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hL2 8
    norm_num at h
    linarith
  have hL9pos : (0:ℝ) < Real.log T ^ 9 := by positivity
  have hL9id : Real.log T ^ 9 = Real.log T * Real.log T ^ 8 := by ring
  have hδ0 : 0 < c₁ / Real.log T ^ 9 := by positivity
  have hδ1 : c₁ / Real.log T ^ 9 ≤ 1 / Real.log T := by
    rw [div_le_div_iff₀ hL9pos hL0]
    nlinarith [mul_le_mul_of_nonneg_right hc₁1 hL0.le,
      mul_le_mul_of_nonneg_left hL8 hL0.le]
  have hδhalf : c₁ / Real.log T ^ 9 ≤ 1 / 2 := by
    have : 1 / Real.log T ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    linarith
  have hδcancel : c₁ / Real.log T ^ 9 * Real.log T ^ 9 = c₁ :=
    div_mul_cancel₀ _ (ne_of_gt hL9pos)
  -- ## `log (2 T)` is comparable to `log T`
  have hlog2T0 : (0:ℝ) < Real.log (2 * T) := by
    have : Real.log T ≤ Real.log (2 * T) :=
      Real.log_le_log hT0 (by linarith)
    linarith
  have hlog2T : Real.log (2 * T) ≤ 3 / 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hT0)]
    have h := Real.log_two_lt_d9
    linarith
  have hδ2 : c₁ / Real.log T ^ 9 ≤ 1 / Real.log (2 * T) := by
    rw [div_le_div_iff₀ hL9pos hlog2T0]
    nlinarith [mul_le_mul_of_nonneg_right hc₁1 hlog2T0.le,
      mul_le_mul_of_nonneg_left hL8 hL0.le]
  -- ## Neither `s` nor any point of the horizontal segment through `s` is the pole
  have hne : ∀ y : ℝ, ((y:ℂ) + (s.im:ℂ) * Complex.I) ≠ 1 := by
    intro y h
    have h2 : ((y:ℂ) + (s.im:ℂ) * Complex.I).im = (1:ℂ).im := by rw [h]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.one_im] at h2
    rw [h2] at him1
    simp only [abs_zero] at him1
    linarith
  -- ## Step 1: `‖ζ (x)‖ (x - 1) ≤ 2` for real `1 < x ≤ 2`, from Euler-Maclaurin at `n = 1`
  have hzreal : ∀ x : ℝ, 1 < x → x ≤ 2 → ‖riemannZeta (x:ℂ)‖ * (x - 1) ≤ 2 := by
    intro x hx1 hx2
    have hx0 : (0:ℝ) < x := by linarith
    have hre : (0:ℝ) < ((x:ℂ)).re := by simpa using hx0
    have hxne : (x:ℂ) ≠ 1 := by
      intro h
      have : x = 1 := by exact_mod_cast h
      linarith
    have hEM := riemannZeta_eq_sum_add_integral_sawtooth
      hre hxne (n := 1) le_rfl
    have htail := norm_mul_integral_sawtooth_le (s := (x:ℂ)) hre (n := 1) le_rfl
    obtain ⟨J, hJ⟩ : ∃ J : ℂ, J = (x:ℂ) * ∫ y in Set.Ioi (((1:ℕ)):ℝ),
        ((y - (⌊y⌋ : ℝ) - 1 / 2 : ℝ) : ℂ) / (y : ℂ) ^ ((x:ℂ) + 1) := ⟨_, rfl⟩
    rw [← hJ] at hEM htail
    have hnormx : ‖(x:ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hone : (((1:ℕ)):ℝ) ^ ((x:ℂ)).re = 1 := by
      simp
    rw [hone, hnormx, Complex.ofReal_re] at htail
    have htail2 : ‖J‖ ≤ 1 / 2 := by
      have hxx : x / (2 * x * 1) = 1 / 2 := by
        field_simp
      rwa [hxx] at htail
    simp only [Finset.Ico_self, Finset.sum_empty, Nat.cast_one, Complex.one_cpow,
      zero_add] at hEM
    have hpole : ‖1 / ((x:ℂ) - 1)‖ = 1 / (x - 1) := by
      rw [show (x:ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_div, norm_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < x - 1)]
    have h1 : ‖riemannZeta (x:ℂ)‖ ≤ ‖(1:ℂ) / 2 + 1 / ((x:ℂ) - 1)‖ + ‖J‖ := by
      rw [hEM]; exact norm_sub_le _ _
    have h2 : ‖(1:ℂ) / 2 + 1 / ((x:ℂ) - 1)‖ ≤ 1 / 2 + 1 / (x - 1) := by
      refine (norm_add_le _ _).trans ?_
      rw [hpole]
      norm_num
    have h3 : ‖riemannZeta (x:ℂ)‖ ≤ 1 + 1 / (x - 1) := by linarith
    have hinv : 1 / (x - 1) * (x - 1) = 1 :=
      div_mul_cancel₀ 1 (by linarith : x - 1 ≠ 0)
    nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : (0:ℝ) ≤ x - 1)]
  -- ## Step 2: `‖ζ (x + 2 i t)‖ ≤ B log T`, from the bound on the rectangle at height `2 T`
  have hz2t : ∀ x : ℝ, 1 - c₁ / Real.log T ^ 9 ≤ x → x ≤ 2 →
      ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖ ≤ B * Real.log T := by
    intro x hxl hxu
    have hwre : ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I).re = x := by simp
    have hwim : ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I).im = 2 * s.im := by simp
    have h2T : Real.exp 2 ≤ 2 * T := by linarith
    have h1 := hC₀ (2 * T) h2T _ (by rw [hwre]; linarith) (by rw [hwre]; exact hxu)
      (by rw [hwim, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith)
    have h2 : (2:ℝ) ≤ ‖((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1‖ := by
      have h := Complex.abs_im_le_norm (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1)
      rw [Complex.sub_im, hwim, Complex.one_im, sub_zero, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
      linarith
    have h3 : ‖1 / (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1)‖ ≤ 1 / 2 := by
      rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h4 : ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖ ≤
        ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) -
          1 / (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1)‖ +
        ‖1 / (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1)‖ := by
      simpa using norm_add_le
        (riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) -
          1 / (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1))
        (1 / (((x:ℂ) + 2 * (s.im:ℂ) * Complex.I) - 1))
    have h5 : C₀ * Real.log (2 * T) ≤ C₀ * (3 / 2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlog2T hC₀0.le
    have hCL : (0:ℝ) ≤ C₀ * Real.log T := by positivity
    rw [hB]
    linarith
  -- ## Step 3: the 3-4-1 lower bound at any `x` with `1 + c₁ / log ^ 9 T ≤ x ≤ 2`
  have hstep : ∀ x : ℝ, 1 + c₁ / Real.log T ^ 9 ≤ x → x ≤ 2 →
      4 * (c₁ * M) ≤ ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ * Real.log T ^ 7 := by
    intro x hxl hxu
    have hx1 : 1 < x := by linarith
    have hd0 : (0:ℝ) < x - 1 := by linarith
    have hdc : c₁ / Real.log T ^ 9 ≤ x - 1 := by linarith
    have h341 := one_le_norm_riemannZeta_pow_three_mul (σ := x) (t := s.im) hx1
    rw [norm_mul, norm_mul, norm_pow, norm_pow] at h341
    have hp := hzreal x hx1 hxu
    have hq := hz2t x (by linarith) hxu
    have hpn : (0:ℝ) ≤ ‖riemannZeta (x:ℂ)‖ := norm_nonneg _
    have hqn : (0:ℝ) ≤ ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖ := norm_nonneg _
    have hZn : (0:ℝ) ≤ ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ := norm_nonneg _
    -- ### `(x - 1) ^ 3 ≤ 8 * (‖ζ (x + i t)‖ ^ 4 * (B log T))`
    have key : (x - 1) ^ 3 ≤ 8 * (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
        (B * Real.log T)) := by
      have e1 : (x - 1) ^ 3 * 1 ≤ (x - 1) ^ 3 *
          (‖riemannZeta (x:ℂ)‖ ^ 3 * ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
            ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖) :=
        mul_le_mul_of_nonneg_left h341 (by positivity)
      have e2 : (x - 1) ^ 3 *
          (‖riemannZeta (x:ℂ)‖ ^ 3 * ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
            ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖)
          = (‖riemannZeta (x:ℂ)‖ * (x - 1)) ^ 3 *
            (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
              ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖) := by ring
      have e3 : (‖riemannZeta (x:ℂ)‖ * (x - 1)) ^ 3 ≤ 2 ^ 3 :=
        pow_le_pow_left₀ (by positivity) hp 3
      have e4 : (‖riemannZeta (x:ℂ)‖ * (x - 1)) ^ 3 *
          (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
            ‖riemannZeta ((x:ℂ) + 2 * (s.im:ℂ) * Complex.I)‖)
          ≤ 8 * (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 * (B * Real.log T)) := by
        refine mul_le_mul (by linarith) ?_ (by positivity) (by norm_num)
        gcongr
      linarith [e1, e2 ▸ e1]
    -- ### Compare with the claimed bound, by comparing fourth powers
    by_contra hcon
    rw [not_le] at hcon
    have hZL0 : (0:ℝ) ≤ ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ * Real.log T ^ 7 := by
      positivity
    have h4 : (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ * Real.log T ^ 7) ^ 4 <
        (4 * (c₁ * M)) ^ 4 := pow_lt_pow_left₀ hcon hZL0 (by norm_num)
    have h6 : (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ * Real.log T ^ 7) ^ 4 =
        ‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 * Real.log T ^ 28 := by ring
    have h7 : (4 * (c₁ * M)) ^ 4 = 256 * (c₁ ^ 4 * M ^ 4) := by ring
    rw [h6, h7] at h4
    have h5 : c₁ ^ 3 ≤ (x - 1) ^ 3 * Real.log T ^ 27 := by
      have h := pow_le_pow_left₀ hδ0.le hdc 3
      rw [div_pow, div_le_iff₀ (by positivity)] at h
      calc c₁ ^ 3 ≤ (x - 1) ^ 3 * (Real.log T ^ 9) ^ 3 := h
        _ = (x - 1) ^ 3 * Real.log T ^ 27 := by ring
    have h8 : c₁ ^ 3 ≤ 8 * B * (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 *
        Real.log T ^ 28) := by
      calc c₁ ^ 3 ≤ (x - 1) ^ 3 * Real.log T ^ 27 := h5
        _ ≤ (8 * (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 * (B * Real.log T))) *
              Real.log T ^ 27 := by gcongr
        _ = 8 * B * (‖riemannZeta ((x:ℂ) + (s.im:ℂ) * Complex.I)‖ ^ 4 * Real.log T ^ 28) := by
              ring
    have hBpos : (0:ℝ) < 8 * B := by linarith
    have h9 := mul_lt_mul_of_pos_left h4 hBpos
    have h10 : 8 * B * (256 * (c₁ ^ 4 * M ^ 4)) = (2048 * B * M ^ 4 * c₁) * c₁ ^ 3 := by ring
    rw [h10, hc₁, one_mul] at h9
    linarith
  -- ## Step 4: the derivative bound on the horizontal segment through `s`
  have hderivbd : ∀ y : ℝ, 1 - c₁ / Real.log T ^ 9 ≤ y → y ≤ 1 + c₁ / Real.log T ^ 9 →
      ‖deriv riemannZeta ((y:ℂ) + (s.im:ℂ) * Complex.I)‖ ≤ M * Real.log T ^ 2 := by
    intro y hyl hyu
    have hwre : ((y:ℂ) + (s.im:ℂ) * Complex.I).re = y := by simp
    have hwim : ((y:ℂ) + (s.im:ℂ) * Complex.I).im = s.im := by simp
    have h1 := hC₅ T hT _ (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact himT)
    have h2 : (1:ℝ) ≤ ‖((y:ℂ) + (s.im:ℂ) * Complex.I) - 1‖ := by
      have h := Complex.abs_im_le_norm (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1)
      rw [Complex.sub_im, hwim, Complex.one_im, sub_zero] at h
      linarith
    have h3 : ‖1 / (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1) ^ 2‖ ≤ 1 := by
      rw [norm_div, norm_one, norm_pow, div_le_one (by positivity)]
      nlinarith
    have h4 : ‖deriv riemannZeta ((y:ℂ) + (s.im:ℂ) * Complex.I)‖ ≤
        ‖deriv riemannZeta ((y:ℂ) + (s.im:ℂ) * Complex.I) +
          1 / (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1) ^ 2‖ +
        ‖1 / (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1) ^ 2‖ := by
      have h := norm_sub_le
        (deriv riemannZeta ((y:ℂ) + (s.im:ℂ) * Complex.I) +
          1 / (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1) ^ 2)
        (1 / (((y:ℂ) + (s.im:ℂ) * Complex.I) - 1) ^ 2)
      rwa [add_sub_cancel_right] at h
    have h5 : (1:ℝ) ≤ Real.log T ^ 2 := one_le_pow₀ (by linarith)
    rw [hM]
    linarith
  -- ## Step 5: the mean value inequality along that segment
  have hmvt : ∀ y z : ℝ, y ∈ Set.Icc (1 - c₁ / Real.log T ^ 9) (1 + c₁ / Real.log T ^ 9) →
      z ∈ Set.Icc (1 - c₁ / Real.log T ^ 9) (1 + c₁ / Real.log T ^ 9) →
      ‖riemannZeta ((z:ℂ) + (s.im:ℂ) * Complex.I) -
        riemannZeta ((y:ℂ) + (s.im:ℂ) * Complex.I)‖ ≤ M * Real.log T ^ 2 * ‖z - y‖ := by
    intro y z hy hz
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u : ℝ => riemannZeta ((u:ℂ) + (s.im:ℂ) * Complex.I))
      (f' := fun u : ℝ => deriv riemannZeta ((u:ℂ) + (s.im:ℂ) * Complex.I))
      (s := Set.Icc (1 - c₁ / Real.log T ^ 9) (1 + c₁ / Real.log T ^ 9)) ?_ ?_
      (convex_Icc _ _) hy hz
    · intro u _
      refine HasDerivAt.hasDerivWithinAt ?_
      have hg : HasDerivAt (fun w : ℂ => riemannZeta (w + (s.im:ℂ) * Complex.I))
          (deriv riemannZeta ((u:ℂ) + (s.im:ℂ) * Complex.I)) (u:ℂ) :=
        ((differentiableAt_riemannZeta (hne u)).hasDerivAt).comp_add_const _ _
      exact hg.comp_ofReal
    · intro u hu
      exact hderivbd u hu.1 hu.2
  -- ## Step 6: assemble, splitting on which side of `1 + c₁ / log ^ 9 T` the point `s` lies
  rw [div_lt_iff₀ (by positivity)]
  rcases le_total (1 + c₁ / Real.log T ^ 9) s.re with hcase | hcase
  · have h := hstep s.re hcase hσu
    rw [Complex.re_add_im] at h
    linarith [mul_pos hc₁0 (show (0:ℝ) < M by linarith)]
  · have hle2 : 1 + c₁ / Real.log T ^ 9 ≤ 2 := by linarith
    have h := hstep (1 + c₁ / Real.log T ^ 9) le_rfl hle2
    have hy : s.re ∈ Set.Icc (1 - c₁ / Real.log T ^ 9) (1 + c₁ / Real.log T ^ 9) :=
      ⟨hσl, hcase⟩
    have hz : (1 + c₁ / Real.log T ^ 9) ∈
        Set.Icc (1 - c₁ / Real.log T ^ 9) (1 + c₁ / Real.log T ^ 9) :=
      ⟨by linarith, le_rfl⟩
    have hmv := hmvt s.re (1 + c₁ / Real.log T ^ 9) hy hz
    rw [Complex.re_add_im] at hmv
    have hdist : ‖(1 + c₁ / Real.log T ^ 9) - s.re‖ ≤ 2 * (c₁ / Real.log T ^ 9) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hstep2 : M * Real.log T ^ 2 * ‖(1 + c₁ / Real.log T ^ 9) - s.re‖ ≤
        M * Real.log T ^ 2 * (2 * (c₁ / Real.log T ^ 9)) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    have herr : M * Real.log T ^ 2 * (2 * (c₁ / Real.log T ^ 9)) * Real.log T ^ 7
        = 2 * (M * c₁) := by
      field_simp
    have htri : ‖riemannZeta (((1 + c₁ / Real.log T ^ 9 : ℝ) : ℂ) + (s.im:ℂ) * Complex.I)‖
        ≤ ‖riemannZeta s‖ +
          ‖riemannZeta (((1 + c₁ / Real.log T ^ 9 : ℝ) : ℂ) + (s.im:ℂ) * Complex.I) -
            riemannZeta s‖ := by
      have := norm_add_le (riemannZeta s)
        (riemannZeta (((1 + c₁ / Real.log T ^ 9 : ℝ) : ℂ) + (s.im:ℂ) * Complex.I) -
          riemannZeta s)
      simpa using this
    have hmul : (‖riemannZeta (((1 + c₁ / Real.log T ^ 9 : ℝ) : ℂ) + (s.im:ℂ) * Complex.I) -
        riemannZeta s‖) * Real.log T ^ 7 ≤
        M * Real.log T ^ 2 * (2 * (c₁ / Real.log T ^ 9)) * Real.log T ^ 7 :=
      mul_le_mul_of_nonneg_right (le_trans hmv hstep2) (by positivity)
    rw [herr] at hmul
    linarith [mul_le_mul_of_nonneg_right htri (by positivity : (0:ℝ) ≤ Real.log T ^ 7),
      mul_pos hc₁0 (show (0:ℝ) < M by linarith)]

/-- **The zero-free box for `ζ₁` at small ordinate.** There are `δ > 0` and `M > 0` such that
for every `s` with `1 - δ ≤ s.re ≤ 2` and `|s.im| ≤ 1`, the entire function `ζ₁` does not
vanish at `s` and `‖ζ₁' s / ζ₁ s‖ ≤ M`.

Both conclusions are asserted of the *same* `δ` and `M`: with the non-vanishing clause dropped
the bound would hold vacuously at a zero of `ζ₁`, since Lean's division by zero is zero. -/
theorem exists_riemannZeta₁_ne_zero_and_norm_logDeriv_le :
    ∃ δ > 0, ∃ M > 0, ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 →
      riemannZeta₁ s ≠ 0 ∧ ‖deriv riemannZeta₁ s / riemannZeta₁ s‖ ≤ M := by
  -- On `Re s ≥ 1` the zeros of `ζ₁` are exactly those of `ζ`, and there are none.
  have hne_one : ∀ s : ℂ, 1 ≤ s.re → riemannZeta₁ s ≠ 0 := by
    intro s hs
    rcases eq_or_ne s 1 with rfl | hs1
    · simp
    · have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
      rw [riemannZeta_eq_inv_sub_mul hs1] at hz
      exact fun h => hz (by rw [h, mul_zero])
  -- The zero set of `ζ₁` inside the wide box is compact.
  set K₀ : Set ℂ := (Set.Icc (0 : ℝ) 2) ×ℂ (Set.Icc (-1 : ℝ) 1) with hK₀def
  have hK₀ : IsCompact K₀ := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  set Z : Set ℂ := K₀ ∩ (riemannZeta₁ ⁻¹' {0}) with hZdef
  have hZc : IsCompact Z :=
    hK₀.inter_right (isClosed_singleton.preimage differentiable_riemannZeta₁.continuous)
  -- Take `δ` from the largest real part attained by a zero.
  obtain ⟨δ, hδ0, hδhalf, hδ⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ s ∈ Z, s.re < 1 - δ := by
    rcases Set.eq_empty_or_nonempty Z with he | hne
    · exact ⟨1 / 2, by norm_num, le_rfl, fun s hs => absurd hs (by rw [he]; exact fun h => h)⟩
    · obtain ⟨s₀, hs₀Z, hs₀max⟩ := hZc.exists_isMaxOn hne Complex.continuous_re.continuousOn
      have hs₀0 : 0 ≤ s₀.re := (Complex.mem_reProdIm.mp hs₀Z.1).1.1
      have h1 : s₀.re < 1 := by
        by_contra h
        exact (hne_one s₀ (not_lt.mp h)) hs₀Z.2
      refine ⟨(1 - s₀.re) / 2, by linarith, by linarith, fun s hs => ?_⟩
      have hle : s.re ≤ s₀.re := hs₀max hs
      linarith
  have hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → riemannZeta₁ s ≠ 0 := by
    intro s h1 h2 h3 hz
    obtain ⟨him1, him2⟩ := abs_le.mp h3
    have hsZ : s ∈ Z :=
      ⟨Complex.mem_reProdIm.mpr ⟨⟨by linarith, h2⟩, him1, him2⟩, hz⟩
    exact absurd (hδ s hsZ) (by linarith)
  -- `ζ₁' / ζ₁` is continuous on the (compact) narrow box, hence bounded there.
  set K : Set ℂ := (Set.Icc (1 - δ) 2) ×ℂ (Set.Icc (-1 : ℝ) 1) with hKdef
  have hK : IsCompact K := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hKne : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs
    obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := Complex.mem_reProdIm.mp hs
    exact hbox s hr1 hr2 (abs_le.mpr ⟨hi1, hi2⟩)
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) K := by
    intro s hs
    exact ((differentiable_riemannZeta₁.deriv.continuous.continuousAt).div
      (differentiable_riemannZeta₁.continuous.continuousAt) (hKne s hs)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨δ, hδ0, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun s h1 h2 h3 => ?_⟩
  obtain ⟨him1, him2⟩ := abs_le.mp h3
  exact ⟨hbox s h1 h2 h3,
    le_trans (hC s (Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, him1, him2⟩)) (le_max_left _ _)⟩
