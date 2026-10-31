/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
import MathlibExt.Analysis.Complex.VerticalIntegral.CauchyKernel
import MathlibExt.Analysis.Complex.VerticalIntegral.Integrable
import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel
import MathlibExt.NumberTheory.LSeries.VerticalLine

/-!
# Perron-type formulas with integrable kernels

Let `f(s) = ∑ aₙ n^{-s}` converge absolutely on `re s = c`. If a kernel `K` is integrable on the
line and `(1 / 2πi) ∫_(c) y ^ s K(s) ds = φ(y)` with `φ(y) = 0` for `0 < y < 1`, then
integrating term by term gives
`(1 / 2πi) ∫_(c) f(s) x ^ s K(s) ds = ∑_{n ≤ x} aₙ φ(x / n)`.

With the kernels of `MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel` this gives the
smoothed Perron formulas with logarithmic weights and the Riesz means.

## Main statements

* `LSeriesSummable.hasVerticalIntegral_LSeries_mul_cpow_mul`: the general formula.
* `LSeriesSummable.hasVerticalIntegral_LSeries_mul_cpow_div_pow_succ`: for `k ≥ 1`,
  `(1 / 2πi) ∫_(c) f(s) x ^ s / s ^ (k + 1) ds = (1 / k!) ∑_{n ≤ x} aₙ (log (x / n)) ^ k`.
* `LSeriesSummable.hasVerticalIntegral_LSeries_mul_cpow_div_prod`: the Riesz mean, for `k ≥ 1`,
  `(1 / 2πi) ∫_(c) f(s) x ^ s / (s (s + 1) ⋯ (s + k)) ds =
  (1 / (k! x ^ k)) ∑_{n ≤ x} aₙ (x - n) ^ k`.
-/

@[expose] public section

open MeasureTheory Complex
open scoped Real

namespace LSeriesSummable

variable {a : ℕ → ℂ} {c : ℝ}

/-- **Perron's formula for an integrable kernel.** Let `∑ aₙ n^{-s}` converge absolutely at
`c`, let `K` be integrable on the line `re s = c`, and suppose that for every `y > 0` the
principal value `(1 / 2πi) ∫_(c) y ^ s K(s) ds` is `φ y`, with `φ y = 0` for `0 < y < 1`. Then
for `x > 0`, `(1 / 2πi) ∫_(c) LSeries a s * x ^ s * K s ds = ∑_{1 ≤ n ≤ x} aₙ φ (x / n)`. -/
theorem hasVerticalIntegral_LSeries_mul_cpow_mul (hsum : LSeriesSummable a c) {x : ℝ}
    (hx : 0 < x) {K : ℂ → ℂ} {φ : ℝ → ℂ} (hK : VerticalIntegrable K c)
    (hφ : ∀ y : ℝ, 0 < y → HasVerticalIntegral c (fun s => (y : ℂ) ^ s * K s) (φ y))
    (hφ0 : ∀ y : ℝ, 0 < y → y < 1 → φ y = 0) :
    HasVerticalIntegral c (fun s => LSeries a s * ((x : ℂ) ^ s * K s))
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * φ (x / n)) := by
  -- the kernel `t ↦ y ^ (c + it) K (c + it)` is integrable, and its integral is `φ y`
  set G : ℝ → ℝ → ℂ := fun y t => (y : ℂ) ^ ((c : ℂ) + t * I) * K (c + t * I) with hGdef
  have hGint : ∀ y : ℝ, 0 < y → Integrable (G y) := by
    intro y hy
    refine Integrable.bdd_mul (c := y ^ c) hK ?_ (ae_of_all _ fun t => ?_)
    · exact (Continuous.const_cpow (by fun_prop)
        (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
    · rw [norm_cpow_eq_rpow_re_of_pos hy]
      simp
  have hGφ : ∀ y : ℝ, 0 < y → (1 / (2 * π)) • ∫ t, G y t = φ y := fun y hy =>
    (hasVerticalIntegral_of_integrable (hGint y hy) fun _ => rfl).unique (hφ y hy)
  -- the whole integrand
  have hvert : HasVerticalIntegral c (fun s => LSeries a s * ((x : ℂ) ^ s * K s))
      ((1 / (2 * π)) • ∫ t : ℝ, LSeries a (c + t * I) * G x t) :=
    hasVerticalIntegral_of_integrable (hsum.integrable_vertical_mul (hGint x hx)) fun _ => rfl
  -- term-by-term evaluation
  have hHS := (hsum.hasSum_integral_term_vertical_mul (hGint x hx)).const_smul (1 / (2 * π))
  have hterm : ∀ n : ℕ, (1 / (2 * π)) • ∫ t : ℝ, LSeries.term a (c + t * I) n * G x t =
      if n ∈ Finset.Icc 1 ⌊x⌋₊ then a n * φ (x / n) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hxn : 0 < x / n := div_pos hx hn0
    have e : ∀ t : ℝ, LSeries.term a (c + t * I) n * G x t = a n * G (x / n) t := by
      intro t
      have hcpow : ((n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]
        exact fun h => hn0.ne' (by exact_mod_cast h.1)
      simp only [hGdef, LSeries.term_of_ne_zero hn, ofReal_div,
        div_cpow_ofReal_nonneg hx.le hn0.le]
      push_cast at hcpow ⊢
      field_simp
    simp_rw [e]
    rw [integral_const_mul, ← mul_smul_comm, hGφ _ hxn]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_Icc, not_and_or] at hmem
      have hlt : x / n < 1 := by
        rcases hmem with h | h
        · omega
        · rw [div_lt_one hn0]
          exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast not_le.mp h)
      rw [hφ0 _ hxn hlt, mul_zero]
  simp only [hterm] at hHS
  rw [← (hasSum_sum_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊)
    (fun n hn => by simp only [hn, ↓reduceIte])).unique hHS] at hvert
  rwa [Finset.sum_congr rfl fun n (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) =>
    (by simp only [hn, ↓reduceIte] : (if n ∈ Finset.Icc 1 ⌊x⌋₊ then a n * φ (x / n) else 0) =
      a n * φ (x / n))] at hvert

/-- **Perron's formula with logarithmic weights.** Let `∑ aₙ n^{-s}` converge absolutely at
`c > 0`, and let `k ≥ 1` and `x > 0`. Then
`(1 / 2πi) ∫_(c) LSeries a s * x ^ s / s ^ (k + 1) ds = (∑_{n ≤ x} aₙ (log (x / n)) ^ k) / k!`.
-/
theorem hasVerticalIntegral_LSeries_mul_cpow_div_pow_succ (hsum : LSeriesSummable a c)
    {k : ℕ} (hk : 1 ≤ k) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    HasVerticalIntegral c (fun s => LSeries a s * (x : ℂ) ^ s / s ^ (k + 1))
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (Real.log (x / n) : ℂ) ^ k) / (k.factorial : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have hK : VerticalIntegrable (fun s : ℂ => 1 / s ^ (m + 1 + 1)) c := by
    refine verticalIntegrable_of_norm_le_div_pow (n := m) hc zero_le_one ?_ fun t => ?_
    · exact continuous_const.div (by fun_prop)
        fun t => pow_ne_zero _ (ofReal_add_mul_I_ne_zero (Or.inl hc.ne'))
    · simp [norm_pow]
  have h := hsum.hasVerticalIntegral_LSeries_mul_cpow_mul hx hK
    (φ := fun y => if 1 ≤ y then (Real.log y : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ) else 0)
    (fun y hy => by
      split_ifs with h1
      · exact (hasVerticalIntegral_cpow_div_pow_succ_of_one_le hk hc h1).congr_line
          fun t => by ring
      · exact (hasVerticalIntegral_cpow_div_pow_succ_of_le_one hk hc hy
          (not_le.mp h1).le).congr_line fun t => by ring)
    (fun y _ hy => by simp only [not_le.mpr hy, ↓reduceIte])
  have h' := h.congr_line (g := fun s => LSeries a s * (x : ℂ) ^ s / s ^ (m + 1 + 1))
    fun t => by ring
  convert h' using 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : 1 ≤ x / n :=
    (one_le_div hn0).mpr ((Nat.cast_le.mpr hnx).trans (Nat.floor_le hx.le))
  simp only [h1, ↓reduceIte, mul_div_assoc]

/-- **Perron's formula for Riesz means.** Let `∑ aₙ n^{-s}` converge absolutely at `c > 0`, and
let `k ≥ 1` and `x > 0`. Then
`(1 / 2πi) ∫_(c) LSeries a s * x ^ s / (s (s + 1) ⋯ (s + k)) ds =
(∑_{n ≤ x} aₙ (x - n) ^ k) / (k! x ^ k)`. -/
theorem hasVerticalIntegral_LSeries_mul_cpow_div_prod (hsum : LSeriesSummable a c) {k : ℕ}
    (hk : 1 ≤ k) (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    HasVerticalIntegral c
      (fun s => LSeries a s * (x : ℂ) ^ s / ∏ j ∈ Finset.range (k + 1), (s + j))
      ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) ^ k) /
        ((k.factorial : ℂ) * (x : ℂ) ^ k)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  -- the lower bound `‖s‖ ^ (k + 1) ≤ ‖s (s + 1) ⋯ (s + k)‖` on the line
  have hfac : ∀ (t : ℝ) (j : ℕ), ‖(c : ℂ) + t * I‖ ≤ ‖(c : ℂ) + t * I + j‖ := by
    intro t j
    have e2 : (c : ℂ) + t * I + j = ((c + j : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [e2, norm_add_mul_I, norm_add_mul_I]
    apply Real.sqrt_le_sqrt
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hPge : ∀ t : ℝ, ‖(c : ℂ) + t * I‖ ^ (m + 2) ≤
      ‖∏ j ∈ Finset.range (m + 1 + 1), ((c : ℂ) + t * I + j)‖ := by
    intro t
    rw [norm_prod]
    calc ‖(c : ℂ) + t * I‖ ^ (m + 2) = ∏ j ∈ Finset.range (m + 1 + 1), ‖(c : ℂ) + t * I‖ := by
          simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => hfac t j
  have hwpos : ∀ t : ℝ, 0 < ‖(c : ℂ) + t * I‖ := fun t =>
    norm_pos_iff.mpr (ofReal_add_mul_I_ne_zero (Or.inl hc.ne'))
  have hPne : ∀ t : ℝ, ∏ j ∈ Finset.range (m + 1 + 1), ((c : ℂ) + t * I + j) ≠ 0 := by
    intro t h
    have h1 := hPge t
    rw [h, norm_zero] at h1
    exact absurd h1 (not_le.mpr (pow_pos (hwpos t) _))
  have hK : VerticalIntegrable (fun s : ℂ => 1 / ∏ j ∈ Finset.range (m + 1 + 1), (s + j)) c := by
    refine verticalIntegrable_of_norm_le_div_pow (n := m) hc zero_le_one ?_ fun t => ?_
    · exact continuous_const.div (continuous_finsetProd _ fun j _ => by fun_prop) hPne
    · rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le (pow_pos (hwpos t) _) (hPge t)
  have h := hsum.hasVerticalIntegral_LSeries_mul_cpow_mul hx hK
    (φ := fun y => if 1 ≤ y then (1 - 1 / (y : ℂ)) ^ (m + 1) / ((m + 1).factorial : ℂ) else 0)
    (fun y hy => by
      split_ifs with h1
      · exact (hasVerticalIntegral_cpow_div_prod_of_one_le hk hc h1).congr_line
          fun t => by ring
      · exact (hasVerticalIntegral_cpow_div_prod_of_le_one hk hc hy.le
          (not_le.mp h1).le).congr_line fun t => by ring)
    (fun y _ hy => by simp only [not_le.mpr hy, ↓reduceIte])
  have h' := h.congr_line (g := fun s => LSeries a s * (x : ℂ) ^ s /
    ∏ j ∈ Finset.range (m + 1 + 1), (s + j)) fun t => by ring
  convert h' using 1
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : 1 ≤ x / n :=
    (one_le_div hn0).mpr ((Nat.cast_le.mpr hnx).trans (Nat.floor_le hx.le))
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp only [h1, ↓reduceIte]
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end LSeriesSummable
