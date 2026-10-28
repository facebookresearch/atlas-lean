/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXiZeros
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import MathlibExt.NumberTheory.LSeries.ZeroFreeRegion
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Counting the zeros of `ζ` and of Dirichlet `L`-functions near a height

We bound the number of nontrivial zeros `ρ = β + iγ` of `ζ` near a height `T`: the weighted
count `∑_ρ 1 / (1 + (T - γ)²)` is `O(log T)`, so a window of bounded width around `T` contains
`O(log T)` zeros, and consequently `∑_{|γ| < R} 1 / |ρ| = O(log² R)`. All sums run over a family
listing the zeros of `ξ` with multiplicity.

## Main definitions

* `DirichletCharacter.zeroCount χ T`: the number `N(T, χ)` of zeros of `L(s, χ)` with
  `0 < Re s < 1` and `|Im s| < T`, counted with multiplicity.

## Main statements

* `norm_logDeriv_riemannZeta_le_tsum`: `‖ζ'/ζ(s)‖ ≤ ∑ Λ(n) / n^σ` for `Re s ≥ σ > 1`.
* `one_div_one_add_sq_sub_im_le_re`: `1 / (1 + (T - γ)²) ≤ 4 Re (1 / (2 + iT - ρ) + 1 / ρ)`.
* `exists_tsum_one_div_one_add_sq_sub_im_le_log`: `∑_ρ 1 / (1 + (T - γ)²) = O(log T)`.
* `exists_card_le_log_of_abs_abs_im_sub_le`: at most `(1 + D²) C log T` zeros satisfy
  `||γ| - T| ≤ D`.
* `exists_tsum_one_div_norm_le_log_sq`: `∑_{|γ| < R} 1 / |ρ| = O(log² R)`.
-/

@[expose] public section

universe u

open ArithmeticFunction LSeries RiemannXi

namespace DirichletCharacter

/-- **`N(T, χ)`**: the number of zeros of `L(s, χ)` in the open rectangle `0 < Re s < 1`,
`|Im s| < T`, counted with multiplicity (`analyticOrderNatAt`). The strip is open, so the
trivial zero at `s = 0` of an even character is not counted. If there were infinitely many such
zeros, the `finsum` would take the junk value `0`. -/
noncomputable def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T},
    analyticOrderNatAt (LFunction χ) ρ

end DirichletCharacter

/-- For `Re s ≥ σ > 1`, `‖ζ'(s)/ζ(s)‖ ≤ ∑ Λ(n) / n^σ`. -/
theorem norm_logDeriv_riemannZeta_le_tsum {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n, ‖term (fun n => (Λ n : ℂ)) σ n‖ := by
  have hsum : Summable fun n => ‖term (fun n => (Λ n : ℂ)) σ n‖ :=
    (LSeriesSummable_vonMangoldt (by simpa using hσ)).norm
  have hle : ∀ n, ‖term (fun n => (Λ n : ℂ)) s n‖ ≤ ‖term (fun n => (Λ n : ℂ)) σ n‖ :=
    fun n => norm_term_le_of_re_le_re _ (by simpa using hs) n
  have hsw : Summable fun n => ‖term (fun n => (Λ n : ℂ)) s n‖ :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  rw [← neg_neg (deriv riemannZeta s / riemannZeta s), ← neg_div,
    ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by linarith), norm_neg]
  exact (norm_tsum_le_tsum_norm hsw).trans (hsw.tsum_le_tsum hle hsum)

/-- `ζ'/ζ` is bounded on every half-plane `Re s ≥ 1 + δ`, `δ > 0`. -/
theorem exists_norm_logDeriv_riemannZeta_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 + δ ≤ s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ K :=
  ⟨_, tsum_nonneg fun _ => norm_nonneg _,
    fun _ hs => norm_logDeriv_riemannZeta_le_tsum (by linarith) hs⟩

/-- For `0 ≤ β ≤ 1`, `1 / (1 + (T - γ)²) ≤ 4 Re (1 / (2 + iT - ρ) + 1 / ρ)` where `ρ = β + iγ`. -/
theorem one_div_one_add_sq_sub_im_le_re {ρ : ℂ} (hb0 : 0 ≤ ρ.re) (hb1 : ρ.re ≤ 1) (T : ℝ) :
    1 / (1 + (T - ρ.im) ^ 2) ≤
      4 * (1 / ((2 : ℂ) + T * Complex.I - ρ) + 1 / ρ).re := by
  rw [Complex.add_re, one_div ((2 : ℂ) + T * Complex.I - ρ), one_div ρ, Complex.inv_re,
    Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  have hρ : 0 ≤ ρ.re / Complex.normSq ρ := div_nonneg hb0 (Complex.normSq_nonneg _)
  set a := 2 + (T * 0 - 0 * 1) - ρ.re with ha
  set d := 0 + (T * 1 + 0 * 0) - ρ.im with hd'
  have ha' : a = 2 - ρ.re := by rw [ha]; ring
  have hd'' : d = T - ρ.im := by rw [hd']; ring
  rw [← hd'']
  have ha1 : 1 ≤ a := by linarith
  have ha2 : a ≤ 2 := by linarith
  have hpos : 0 < a * a + d * d := by nlinarith
  have : 1 / (1 + d ^ 2) ≤ 4 * (a / (a * a + d * d)) := by
    rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [sq_nonneg d]
  nlinarith

/-- **The zeros near height `T`.** There is a constant `C` such that for `T ≥ 2`, the sum
`∑_ρ 1 / (1 + (T - γ)²)` over the nontrivial zeros `ρ = β + iγ` of `ζ`, counted with
multiplicity (any family `z` listing the zeros of `ξ` with multiplicity), converges and is at
most `C log T`. -/
theorem exists_tsum_one_div_one_add_sq_sub_im_le_log :
    ∃ C : ℝ, ∀ {ι : Type u} (z : ι → ℂ),
      (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
      ∀ T : ℝ, 2 ≤ T → Summable (fun n => 1 / (1 + (T - (z n).im) ^ 2)) ∧
        ∑' n, 1 / (1 + (T - (z n).im) ^ 2) ≤ C * Real.log T := by
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum.{u}
  set K : ℝ := ∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * |A| + 4 * K / Real.log 2, fun {ι} z hz T hT => ?_⟩
  set s : ℂ := (2 : ℂ) + T * Complex.I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hTabs : |T| = T := abs_of_pos (by linarith)
  have key := hA z hz s (by rw [hsre]; norm_num) (by rw [hsre]) (by rw [hsim, hTabs]; exact hT)
  rw [hsim, hTabs] at key
  -- lower bound for `-Re ζ'/ζ(s)`
  have hre_ge : -K ≤ -(deriv riemannZeta s / riemannZeta s).re := by
    have hb := norm_logDeriv_riemannZeta_le_tsum (σ := 2) one_lt_two hsre.ge
    push_cast at hb
    have := Complex.abs_re_le_norm (deriv riemannZeta s / riemannZeta s)
    have := le_abs_self (deriv riemannZeta s / riemannZeta s).re
    linarith
  have hzmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz
  have hm := Complex.summable_one_div_sub_add_one_div (ne_zero_of_card_eq_analyticOrderAt hz)
    (summable_norm_rpow_neg_two hz) s
  have hmre : Summable fun n => (1 / (s - z n) + 1 / z n).re := Complex.reCLM.summable hm
  have hterm : ∀ n, 1 / (1 + (T - (z n).im) ^ 2) ≤ 4 * (1 / (s - z n) + 1 / z n).re :=
    fun n => one_div_one_add_sq_sub_im_le_re (hzmem n).2.1 (hzmem n).2.2 T
  have hsum : Summable fun n => 1 / (1 + (T - (z n).im) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm (hmre.mul_left 4)
  refine ⟨hsum, ?_⟩
  have hsumF : ∑' n, 1 / (1 + (T - (z n).im) ^ 2) ≤ 4 * ∑' n, (1 / (s - z n) + 1 / z n).re := by
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm (hmre.mul_left 4)
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hAl : A * Real.log T ≤ |A| * Real.log T :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  have hKl : K ≤ K / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith
  have hexp : (4 * |A| + 4 * K / Real.log 2) * Real.log T
      = 4 * (|A| * Real.log T) + 4 * (K / Real.log 2 * Real.log T) := by ring
  rw [hexp]
  linarith

/-- **Zeros in a window.** There is a constant `C ≥ 0` such that for `T ≥ 2` and `D ≥ 0`, any
finite set of indices `n` of a family listing the zeros of `ξ` with multiplicity, all with
`||Im z n| - T| ≤ D`, has at most `(1 + D²) C log T` elements. -/
theorem exists_card_le_log_of_abs_abs_im_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (z : ι → ℂ),
      (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
      ∀ T D : ℝ, 2 ≤ T → 0 ≤ D → ∀ F : Finset ι, (∀ n ∈ F, |(|(z n).im| - T)| ≤ D) →
        (F.card : ℝ) ≤ (1 + D ^ 2) * C * Real.log T := by
  obtain ⟨C, hC⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{u}
  refine ⟨2 * |C|, by positivity, fun {ι} z hz T D hT hD F hF => ?_⟩
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hCa : C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hl
  have hsumF : ∀ y : ι → ℂ, (∀ w, ENat.card {n // y n = w} = analyticOrderAt riemannXi w) →
      ∑ n ∈ F, 1 / (1 + (T - (y n).im) ^ 2) ≤ |C| * Real.log T := by
    intro y hy
    obtain ⟨hs, ht⟩ := hC y hy T hT
    exact ((hs.sum_le_tsum F fun n _ => by positivity).trans ht).trans hCa
  have ha := hsumF z hz
  have hb := hsumF (fun n => 1 - z n) (card_one_sub_eq_analyticOrderAt hz)
  have him : ∀ n, (1 - z n).im = -(z n).im := fun n => by simp
  simp only [him] at hb
  have hone : ∀ n ∈ F, (1 : ℝ) ≤ (1 + D ^ 2) * (1 / (1 + (T - (z n).im) ^ 2) +
      1 / (1 + (T - -(z n).im) ^ 2)) := by
    intro n hn
    have h := hF n hn
    have pa : 0 ≤ 1 / (1 + (T - (z n).im) ^ 2) := by positivity
    have pb : 0 ≤ 1 / (1 + (T - -(z n).im) ^ 2) := by positivity
    have hD2 : 0 ≤ 1 + D ^ 2 := by positivity
    rcases le_or_gt 0 (z n).im with h0 | h0
    · rw [abs_of_nonneg h0] at h
      have hsq : (T - (z n).im) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : 1 ≤ (1 + D ^ 2) * (1 / (1 + (T - (z n).im) ^ 2)) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · rw [abs_of_neg h0] at h
      have hsq : (T - -(z n).im) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs, show T - -(z n).im = -(-(z n).im - T) by ring, abs_neg]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : 1 ≤ (1 + D ^ 2) * (1 / (1 + (T - -(z n).im) ^ 2)) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      nlinarith
  calc (F.card : ℝ) = ∑ n ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ F, (1 + D ^ 2) * (1 / (1 + (T - (z n).im) ^ 2) +
          1 / (1 + (T - -(z n).im) ^ 2)) := Finset.sum_le_sum hone
    _ = (1 + D ^ 2) * (∑ n ∈ F, 1 / (1 + (T - (z n).im) ^ 2) +
          ∑ n ∈ F, 1 / (1 + (T - -(z n).im) ^ 2)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + D ^ 2) * (|C| * Real.log T + |C| * Real.log T) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- **The inverse zero sum.** There is a constant `C` such that for `R ≥ 2`, the sum of `1 / |ρ|`
over the nontrivial zeros `ρ = β + iγ` of `ζ` with `|γ| < R`, counted with multiplicity (any
family `z` listing the zeros of `ξ` with multiplicity), is at most `C log² R`. The sum has finite
support. -/
theorem exists_tsum_one_div_norm_le_log_sq :
    ∃ C : ℝ, ∀ {ι : Type u} (z : ι → ℂ),
      (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
      ∀ R : ℝ, 2 ≤ R →
        ∑' n, (if |(z n).im| < R then 1 / ‖z n‖ else 0) ≤ C * Real.log R ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_card_le_log_of_abs_abs_im_sub_le.{u}
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ > 0, ∀ s : ℂ, riemannXi s = 0 → δ ≤ ‖s‖ := by
    have h := (differentiable_riemannXi.continuous.continuousAt (x := (0 : ℂ))).eventually_ne
      riemannXi_zero_ne_zero
    obtain ⟨δ, hδ, h'⟩ := Metric.eventually_nhds_iff.mp h
    refine ⟨δ, hδ, fun s hs => ?_⟩
    by_contra hlt
    push Not at hlt
    exact h' (by simpa using hlt) hs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 1 / δ + 1 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨10 * C * K * (1 / Real.log 2 + 2), fun {ι} z hz R hR => ?_⟩
  have hlR : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hzero : ∀ n, riemannXi (z n) = 0 := Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz
  -- pointwise bound
  have hpt : ∀ n, 1 / ‖z n‖ ≤ K / (1 + (⌊|(z n).im|⌋₊ : ℝ)) := by
    intro n
    have hn := hδ' _ (hzero n)
    have hpos : 0 < ‖z n‖ := lt_of_lt_of_le hδ hn
    have h1 : |(z n).im| ≤ ‖z n‖ := Complex.abs_im_le_norm (z n)
    have h2 : (⌊|(z n).im|⌋₊ : ℝ) ≤ |(z n).im| := Nat.floor_le (abs_nonneg _)
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h3 : 1 ≤ ‖z n‖ / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : K * ‖z n‖ = ‖z n‖ / δ + ‖z n‖ := by rw [hK]; field_simp
    rw [e]; linarith
  -- count bound
  have hcount : ∀ k : ℕ, (k : ℝ) ≤ R → ∀ F : Finset ι,
      ((F.filter (fun n => ⌊|(z n).im|⌋₊ = k)).card : ℝ) ≤ 10 * C * Real.log R := by
    intro k hk F
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := hC z hz ((k : ℝ) + 2) 2 (by linarith) (by norm_num)
      (F.filter (fun n => ⌊|(z n).im|⌋₊ = k)) (by
        intro n hn
        have hk' := (Finset.mem_filter.mp hn).2
        have hlo : (k : ℝ) ≤ |(z n).im| := hk' ▸ Nat.floor_le (abs_nonneg _)
        have hhi : |(z n).im| < k + 1 := hk' ▸ Nat.lt_floor_add_one _
        rw [abs_le]; constructor <;> linarith)
    have hlog : Real.log ((k : ℝ) + 2) ≤ 2 * Real.log R := by
      have : (k : ℝ) + 2 ≤ R * R := by nlinarith
      calc Real.log ((k : ℝ) + 2) ≤ Real.log (R * R) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log R := by
          rw [Real.log_mul (by positivity) (by positivity)]; ring
    have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (1 + 2 ^ 2) * C by positivity)
    linarith
  have hharm : ∑ k ∈ Finset.range (⌊R⌋₊ + 1), K / (1 + (k : ℝ)) ≤
      K * ((1 / Real.log 2 + 2) * Real.log R) := by
    have h1 : ∑ k ∈ Finset.range (⌊R⌋₊ + 1), K / (1 + (k : ℝ)) =
        K * ((harmonic (⌊R⌋₊ + 1) : ℚ) : ℝ) := by
      rw [harmonic, Rat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      rw [div_eq_mul_inv, add_comm]
    have h2 := harmonic_le_one_add_log (⌊R⌋₊ + 1)
    have hfl : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le (by linarith)
    have h3 : Real.log (((⌊R⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log R := by
      push_cast
      have : (⌊R⌋₊ : ℝ) + 1 ≤ R * R := by nlinarith
      calc Real.log ((⌊R⌋₊ : ℝ) + 1) ≤ Real.log (R * R) :=
            Real.log_le_log (by positivity) this
        _ = 2 * Real.log R := by
          rw [Real.log_mul (by positivity) (by positivity)]; ring
    have h4 : 1 ≤ Real.log R / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have h5 : 1 / Real.log 2 * Real.log R = Real.log R / Real.log 2 := by ring
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hK0
    nlinarith
  apply tsum_le_of_sum_le' (by positivity)
  intro F
  set F' := F.filter (fun n => |(z n).im| < R) with hF'
  have hmaps : ∀ n ∈ F', ⌊|(z n).im|⌋₊ ∈ Finset.range (⌊R⌋₊ + 1) := by
    intro n hn
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (Finset.mem_filter.mp hn).2.le
  calc ∑ n ∈ F, (if |(z n).im| < R then 1 / ‖z n‖ else 0)
      = ∑ n ∈ F', 1 / ‖z n‖ := by rw [hF', Finset.sum_filter]
    _ ≤ ∑ n ∈ F', K / (1 + (⌊|(z n).im|⌋₊ : ℝ)) := Finset.sum_le_sum fun n _ => hpt n
    _ = ∑ k ∈ Finset.range (⌊R⌋₊ + 1), ∑ n ∈ F'.filter (fun n => ⌊|(z n).im|⌋₊ = k),
          K / (1 + (⌊|(z n).im|⌋₊ : ℝ)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ Finset.range (⌊R⌋₊ + 1),
          ((F'.filter (fun n => ⌊|(z n).im|⌋₊ = k)).card : ℝ) * (K / (1 + (k : ℝ))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2])]
        simp
    _ ≤ ∑ k ∈ Finset.range (⌊R⌋₊ + 1), (10 * C * Real.log R) * (K / (1 + (k : ℝ))) := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine hcount k ?_ F'
        have hk' : k ≤ ⌊R⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact (Nat.cast_le.mpr hk').trans (Nat.floor_le (by linarith))
    _ = (10 * C * Real.log R) * ∑ k ∈ Finset.range (⌊R⌋₊ + 1), K / (1 + (k : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (10 * C * Real.log R) * (K * ((1 / Real.log 2 + 2) * Real.log R)) :=
        mul_le_mul_of_nonneg_left hharm (mul_nonneg (by positivity) (by linarith))
    _ = _ := by ring
