/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Defs

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Monochromatic pairs with square sum (Erdős Problem 439)

We approximate the measure on the values of `W * n^2 + n` by spreading each atom uniformly over
its following gap. Taking `W` to be a sufficiently large factorial makes the error small at
all additive frequencies. Shift averaging handles the oscillating quadratic phases, and a
complete character sum handles frequencies within bounded scaled distance of a rational.
Fourier inversion then gives a same-colour pair, with enough mass to exclude the diagonal.

The square-sum theorem is due to Khalfalah and Szemerédi, as cited below. The proof here treats
only squares; in particular, it does not use the more general polynomial theorem.
-/

namespace MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted


open Finset Filter Topology
open scoped BigOperators ComplexConjugate

noncomputable section

private def phase (t : ℝ) : ℂ := Complex.exp (Complex.I * (↑(2 * Real.pi * t) : ℂ))

private lemma phase_zero : phase 0 = 1 := by simp [phase]

private lemma phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  simp only [phase, mul_add, Complex.ofReal_add, Complex.exp_add]

private lemma phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  rw [phase, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg, mul_neg, neg_mul]

private lemma phase_sub (a b : ℝ) : phase (a - b) = phase a * conj (phase b) := by
  rw [sub_eq_add_neg, phase_add, phase_conj]

private lemma phase_nat_mul (t : ℝ) (j : ℕ) : phase (t * j) = phase t ^ j := by
  induction j with
  | zero => simp [phase_zero]
  | succ j ih => rw [Nat.cast_succ, mul_add, mul_one, phase_add, ih, pow_succ]

private lemma phase_eq_one {t : ℝ} : phase t = 1 ↔ ∃ m : ℤ, t = m := by
  have hπ := Real.pi_pos
  rw [phase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h : 2 * Real.pi * t = (m : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_im, Complex.mul_re] using congrArg Complex.im hm
    exact mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) (by linear_combination h)
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

private lemma phase_int (m : ℤ) : phase (m : ℝ) = 1 := phase_eq_one.2 ⟨m, rfl⟩

private lemma phase_continuous : Continuous phase := by
  unfold phase
  fun_prop

private lemma phase_dist (a b : ℝ) : ‖phase a - phase b‖ = ‖phase (a - b) - 1‖ := by
  have h : (phase (a - b) - 1) * phase b = phase a - phase b := by
    rw [sub_mul, one_mul, ← phase_add, sub_add_cancel]
  rw [← h, norm_mul, phase_norm, mul_one]

private lemma phase_dist_le (a b : ℝ) : ‖phase a - phase b‖ ≤ 2 * Real.pi * |a - b| := by
  rw [phase_dist, phase, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h : |Real.sin (Real.pi * (a - b))| ≤ |Real.pi * (a - b)| := Real.abs_sin_le_abs
  have h' : 2 * Real.pi * (a - b) / 2 = Real.pi * (a - b) := by ring
  rw [h', Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  linarith

private lemma phase_small (t : ℝ) (ht : |t| ≤ 1 / 2) : 4 * |t| ≤ ‖phase t - 1‖ := by
  rw [phase, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), show 2 * Real.pi * t / 2 = Real.pi * t by ring]
  have hπ := Real.pi_pos
  have hs := Real.mul_le_sin (show 0 ≤ Real.pi * |t| by positivity)
    (show Real.pi * |t| ≤ Real.pi / 2 by nlinarith)
  have habs : Real.sin (Real.pi * |t|) = |Real.sin (Real.pi * t)| := by
    have lepi : Real.pi * |t| ≤ Real.pi := by nlinarith
    have hn := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ Real.pi * |t| by positivity) lepi
    by_cases ht' : 0 ≤ t
    · rw [abs_of_nonneg ht'] at hn ⊢
      exact (abs_of_nonneg hn).symm
    · rw [abs_of_neg (lt_of_not_ge ht'), mul_neg, Real.sin_neg] at hn ⊢
      exact (abs_of_nonpos (by linarith)).symm
  have heq : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  linarith [hs, habs]

private def mean (L : ℕ) (f : ℕ → ℂ) : ℂ := (L : ℂ)⁻¹ * ∑ j ∈ range L, f j

private lemma mean_congr {L : ℕ} {f g : ℕ → ℂ} (h : ∀ j < L, f j = g j) :
    mean L f = mean L g := by
  unfold mean
  rw [Finset.sum_congr rfl (fun j hj ↦ h j (mem_range.1 hj))]

private lemma mean_sub (L : ℕ) (f g : ℕ → ℂ) :
    mean L (fun j ↦ f j - g j) = mean L f - mean L g := by
  simp only [mean, sum_sub_distrib, mul_sub]

private lemma mean_mul (L : ℕ) (a : ℂ) (f : ℕ → ℂ) :
    mean L (fun j ↦ a * f j) = a * mean L f := by
  simp only [mean, ← mul_sum]
  ring

private lemma mean_const {L : ℕ} (hL : 0 < L) (a : ℂ) : mean L (fun _ ↦ a) = a := by
  simp only [mean, sum_const, card_range, nsmul_eq_mul, ← mul_assoc]
  rw [inv_mul_cancel₀ (by exact_mod_cast hL.ne' : (L : ℂ) ≠ 0), one_mul]

private lemma mean_norm_le {L : ℕ} {z : ℕ → ℂ} {C : ℝ}
    (hL : 0 < L) (h : ∀ j < L, ‖z j‖ ≤ C) : ‖mean L z‖ ≤ C := by
  calc
    ‖mean L z‖ = (L : ℝ)⁻¹ * ‖∑ j ∈ range L, z j‖ := by
      simp [mean, norm_inv]
    _ ≤ (L : ℝ)⁻¹ * ∑ _j ∈ range L, C := by
      gcongr
      exact (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ h i (mem_range.1 hi))
    _ = C := by
      simp only [sum_const, card_range, nsmul_eq_mul, ← mul_assoc]
      rw [inv_mul_cancel₀ (by exact_mod_cast hL.ne' : (L : ℝ) ≠ 0), one_mul]

private lemma phase_geom (L : ℕ) (a b : ℝ) :
    (1 - phase b) * ∑ j ∈ range L, phase (a + b * j) = phase a - phase (a + b * L) := by
  simp only [phase_add, phase_nat_mul, ← mul_sum]
  rw [← mul_assoc, mul_comm (1 - phase b) (phase a), mul_assoc, mul_comm (1 - phase b),
    geom_sum_mul_neg, mul_sub, mul_one]

private lemma phase_mean_mul_norm (L : ℕ) (a b : ℝ) :
    ‖1 - phase b‖ * ‖mean L (fun j ↦ phase (a + b * j))‖ ≤ 2 / L := by
  calc
    _ = (L : ℝ)⁻¹ * ‖(1 - phase b) * ∑ j ∈ range L, phase (a + b * j)‖ := by
      simp only [mean, norm_mul, norm_inv, Complex.norm_natCast, mul_left_comm]
    _ ≤ 2 / L := by
      rw [phase_geom, div_eq_mul_inv, mul_comm 2]
      gcongr
      simpa only [phase_norm, one_add_one_eq_two] using
        (norm_sub_le (phase a) (phase (a + b * L)))

private def poly (W n : ℕ) : ℕ := W * n ^ 2 + n

private def gap (W n : ℕ) : ℕ := W * (2 * n + 1) + 1

private lemma poly_succ (W n : ℕ) : poly W (n + 1) = poly W n + gap W n := by
  unfold poly gap
  ring

private lemma gap_pos (W n : ℕ) : 0 < gap W n := by simp [gap]

private lemma poly_strictMono (W : ℕ) : StrictMono (poly W) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [poly_succ]
  exact Nat.lt_add_of_pos_right (gap_pos W n)

private lemma weighted_telescoping (z : ℕ → ℂ) (w : ℕ → ℝ) (L : ℕ)
    (hz : ∀ j, ‖z j‖ ≤ 1) (hw : Antitone w) (hw₀ : ∀ j, 0 ≤ w j) :
    ‖∑ j ∈ range L, (w j : ℂ) * (z j - z (j + 1))‖ ≤ 2 * w 0 := by
  let s (m : ℕ) := ∑ j ∈ range m, (w j : ℂ) * (z j - z (j + 1))
  have h (m : ℕ) : ‖s m + (w m : ℂ) * z m - (w 0 : ℂ) * z 0‖ ≤ w 0 - w m := by
    induction m with
    | zero => simp [s]
    | succ m ih =>
      have hstep : s (m + 1) + (w (m + 1) : ℂ) * z (m + 1) - (w 0 : ℂ) * z 0 =
          (s m + (w m : ℂ) * z m - (w 0 : ℂ) * z 0) +
            ((w (m + 1) : ℂ) - w m) * z (m + 1) := by
        rw [show s (m + 1) = s m + (w m : ℂ) * (z m - z (m + 1)) by
          exact sum_range_succ _ _]
        ring
      rw [hstep]
      refine (norm_add_le _ _).trans ?_
      have hmono := hw (Nat.le_succ m)
      have hterm : ‖((w (m + 1) : ℂ) - w m) * z (m + 1)‖ ≤ w m - w (m + 1) := by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.2 hmono)]
        nlinarith [hz (m + 1), norm_nonneg (z (m + 1))]
      linarith
  change ‖s L‖ ≤ _
  have hterm (j : ℕ) : ‖(w j : ℂ) * z j‖ ≤ w j := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw₀ j)]
    nlinarith [hw₀ j, hz j]
  calc
    ‖s L‖ = ‖(s L + (w L : ℂ) * z L - (w 0 : ℂ) * z 0) +
        ((w 0 : ℂ) * z 0 - (w L : ℂ) * z L)‖ := by congr 1; ring
    _ ≤ _ := by
      have hs := norm_sub_le ((w 0 : ℂ) * z 0) ((w L : ℂ) * z L)
      exact (norm_add_le _ _).trans (by linarith [h L, hterm 0, hterm L])

/-! ## Shift averaging and the correlation bound -/

private lemma norm_mean (L : ℕ) (z : ℕ → ℂ) :
    ‖mean L z‖ = ‖∑ j ∈ range L, z j‖ / (L : ℝ) := by
  simp [mean, div_eq_mul_inv, mul_comm, norm_inv]

private lemma norm_sum_unit {z : ℕ → ℂ} (L : ℕ) (h : ∀ j < L, ‖z j‖ ≤ 1) :
    ‖∑ j ∈ range L, z j‖ ≤ L := by
  refine (norm_sum_le _ _).trans ?_
  simpa using sum_le_sum (s := range L) (g := fun _ ↦ (1 : ℝ)) fun j hj ↦ h j (mem_range.1 hj)

private lemma mean_translate (L d : ℕ) (z : ℕ → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    ‖mean L (fun j ↦ z (j + d)) - mean L z‖ ≤ 2 * (d : ℝ) / L := by
  have hs := (sum_range_add z d L).symm.trans (by rw [Nat.add_comm d L, sum_range_add])
  have heq : (∑ j ∈ range L, z (j + d)) - ∑ j ∈ range L, z j =
      (∑ j ∈ range d, z (L + j)) - ∑ j ∈ range d, z j := by
    simp only [add_comm _ d] at ⊢
    linear_combination hs
  rw [mean, mean, ← mul_sub, heq, norm_mul, norm_inv, Complex.norm_natCast, div_eq_mul_inv,
    mul_comm (2 * (d : ℝ))]
  gcongr
  have ha := norm_sum_unit (z := fun j ↦ z (L + j)) d (fun j _ ↦ hz (L + j))
  have hb := norm_sum_unit d (fun j _ ↦ hz j)
  exact (norm_sub_le _ _).trans (by linarith)

private lemma mean_sq_le {L : ℕ} (hL : 0 < L) (f : ℕ → ℂ) :
    ‖mean L f‖ ^ 2 ≤ (∑ j ∈ range L, ‖f j‖ ^ 2) / (L : ℝ) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have h : (∑ j ∈ range L, ‖f j‖) ^ 2 ≤ (L : ℝ) * ∑ j ∈ range L, ‖f j‖ ^ 2 := by
    simpa using sum_mul_sq_le_sq_mul_sq (range L) (fun _ ↦ (1 : ℝ)) (fun j ↦ ‖f j‖)
  rw [norm_mean, div_pow, div_le_div_iff₀ (sq_pos_of_pos hLp) hLp]
  have hn := norm_sum_le (range L) f
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  calc
    ‖∑ j ∈ range L, f j‖ ^ 2 * (L : ℝ) ≤
        ((L : ℝ) * ∑ j ∈ range L, ‖f j‖ ^ 2) * L := by gcongr; exact hs.trans h
    _ = _ := by ring

private lemma cast_norm_sq (z : ℂ) : (↑(‖z‖ ^ 2) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma average_correlation {L H : ℕ} (hL : 0 < L) (hH : 0 < H)
    (z : ℕ → ℕ → ℂ) (hz : ∀ h j, ‖z h j‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ∀ h < H, ∀ k < H, h ≠ k → ‖mean L (fun j ↦ z h j * conj (z k j))‖ ≤ δ) :
    ‖mean L (fun j ↦ mean H (fun h ↦ z h j))‖ ^ 2 ≤ (H : ℝ)⁻¹ + δ := by
  let C (h k : ℕ) := mean L (fun j ↦ z h j * conj (z k j))
  have hdiag (h : ℕ) : C h h = 1 := by
    change mean L (fun j ↦ z h j * conj (z h j)) = _
    rw [mean_congr (g := fun _ ↦ (1 : ℂ)), mean_const hL]
    intro j _
    rw [← cast_norm_sq, hz, one_pow, Complex.ofReal_one]
  have h_expand : (↑((∑ j ∈ range L, ‖mean H (fun h ↦ z h j)‖ ^ 2) / (L : ℝ)) : ℂ) =
      (H : ℂ)⁻¹ ^ 2 * ∑ h ∈ range H, ∑ k ∈ range H, C h k := by
    have hpoint (j : ℕ) : (↑(‖mean H (fun h ↦ z h j)‖ ^ 2) : ℂ) =
        (H : ℂ)⁻¹ ^ 2 * ∑ h ∈ range H, ∑ k ∈ range H, z h j * conj (z k j) := by
      rw [cast_norm_sq]
      simp only [mean, map_mul, map_inv₀, Complex.conj_natCast, map_sum]
      rw [show ∀ A B : ℂ, (H : ℂ)⁻¹ * A * ((H : ℂ)⁻¹ * B) = (H : ℂ)⁻¹ ^ 2 * (A * B) by
        intros; ring, sum_mul]
      congr 1
      exact sum_congr rfl fun _ _ ↦ mul_sum ..
    simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum, hpoint]
    rw [← mul_sum, sum_comm (s := range L) (t := range H)]
    have hswap (h : ℕ) : ∑ j ∈ range L, ∑ k ∈ range H, z h j * conj (z k j) =
        ∑ k ∈ range H, ∑ j ∈ range L, z h j * conj (z k j) := sum_comm
    rw [sum_congr (s₁ := range H) rfl (fun h _ ↦ hswap h)]
    simp only [C, mean, ← mul_sum, div_eq_mul_inv]
    ring
  have h_bound (h : ℕ) (hh : h < H) : ∑ k ∈ range H, ‖C h k‖ ≤ 1 + (H : ℝ) * δ := by
    have hsum := sum_erase_add (range H) (fun k ↦ ‖C h k‖) (mem_range.2 hh)
    have hcard : (((range H).erase h).card : ℝ) ≤ H := by
      exact_mod_cast (card_le_card (erase_subset h (range H))).trans_eq (card_range H)
    have hsum' : ∑ k ∈ (range H).erase h, ‖C h k‖ ≤ ((range H).erase h).card * δ := by
      simpa only [sum_const, nsmul_eq_mul] using
        sum_le_sum (g := fun _ ↦ δ) (fun k hk ↦
          hc h hh k (mem_range.1 (mem_of_mem_erase hk)) (ne_of_mem_erase hk).symm)
    rw [← hsum, hdiag, norm_one]
    linarith [mul_le_mul_of_nonneg_right hcard hδ]
  refine (mean_sq_le hL _).trans ?_
  have hpos : 0 ≤ (∑ j ∈ range L, ‖mean H (fun h ↦ z h j)‖ ^ 2) / (L : ℝ) := by positivity
  have heq := congrArg norm h_expand
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos,
    norm_mul, norm_pow, norm_inv, Complex.norm_natCast] at heq
  rw [heq]
  have hp : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  calc
    _ ≤ (H : ℝ)⁻¹ ^ 2 * (H * (1 + (H : ℝ) * δ)) := by
      gcongr
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ _h ∈ range H, (1 + (H : ℝ) * δ) := by
          refine sum_le_sum fun h hh ↦ (norm_sum_le _ _).trans (h_bound h (mem_range.1 hh))
        _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]
    _ = _ := by field_simp

private lemma mean_double_comm (L H : ℕ) (z : ℕ → ℕ → ℂ) :
    mean L (fun j ↦ mean H (fun h ↦ z h j)) = mean H (fun h ↦ mean L (z h)) := by
  simp only [mean, ← mul_sum]
  rw [sum_comm (s := range L) (t := range H)]
  ring

private lemma shifted_mean_distance {L H : ℕ} (hH : 0 < H) (d : ℕ) (z : ℕ → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ‖mean L (fun j ↦ mean H (fun h ↦ z (j + h * d))) - mean L z‖ ≤
      2 * (H : ℝ) * d / L := by
  rw [mean_double_comm, ← mean_const hH (mean L z), ← mean_sub]
  refine mean_norm_le hH fun h hh ↦ (mean_translate L (h * d) z (fun j ↦ (hz j).le)).trans ?_
  push_cast
  rw [← mul_assoc]
  have hle : (h : ℝ) ≤ H := by exact_mod_cast hh.le
  gcongr

private lemma mean_vanish_of_shifts {L d : ℕ → ℕ} {z : ℕ → ℕ → ℂ}
    (hL : Tendsto L atTop atTop) (hz : ∀ n j, ‖z n j‖ = 1)
    (hd : Tendsto (fun n ↦ (d n : ℝ) / (L n : ℝ)) atTop (𝓝 0))
    (hc : ∀ h k : ℕ, h ≠ k → Tendsto
      (fun n ↦ ‖mean (L n) (fun j ↦ z n (j + h * d n) * conj (z n (j + k * d n)))‖)
      atTop (𝓝 0)) : Tendsto (fun n ↦ ‖mean (L n) (z n)‖) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  let δ := (ε / 2) ^ 2 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H, hH⟩ := exists_nat_gt δ⁻¹
  have hh : 0 < H := by
    exact_mod_cast (inv_pos.mpr hδ).trans hH
  have hInv : (H : ℝ)⁻¹ < δ := (inv_lt_comm₀ (by exact_mod_cast hh) hδ).2 hH
  have heasy' : Tendsto (fun n ↦ 2 * (H : ℝ) * ((d n : ℝ) / (L n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := 2 * (H : ℝ))).mul hd
  have heasy := heasy'.eventually_lt_const (half_pos hε)
  have hpair : ∀ᶠ n in atTop, ∀ (h k : Fin H), h ≠ k →
      ‖mean (L n) (fun j ↦ z n (j + h.val * d n) * conj (z n (j + k.val * d n)))‖ ≤ δ := by
    refine eventually_all.2 fun h ↦ eventually_all.2 fun k ↦ ?_
    by_cases hne : h = k
    · exact Eventually.of_forall fun _ hh' ↦ (hh' hne).elim
    · exact ((hc h k (fun hval ↦ hne (Fin.ext hval))).eventually_le_const hδ).mono (fun _ h _ ↦ h)
  filter_upwards [heasy, hpair, hL.eventually (eventually_gt_atTop 0)] with n hsmall hp hLn
  let m := mean (L n) (fun j ↦ mean H (fun h ↦ z n (j + h * d n)))
  have hb : ‖m‖ ^ 2 ≤ (H : ℝ)⁻¹ + δ := by
    refine average_correlation hLn hh _ (fun _ _ ↦ hz n _) hδ.le ?_
    intro h hh' k hk' hne
    exact hp ⟨h, hh'⟩ ⟨k, hk'⟩ (fun he ↦ hne (congrArg Fin.val he))
  have hm : ‖m‖ < ε / 2 := by
    by_contra! hn
    have he := pow_le_pow_left₀ (by positivity : 0 ≤ ε / 2) hn 2
    linarith [hInv, show 2 * δ = (ε / 2) ^ 2 by dsimp [δ]; ring]
  have ht := shifted_mean_distance (L := L n) hh (d n) (z n) (hz n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖mean (L n) (z n)‖ = ‖m - (m - mean (L n) (z n))‖ := by congr 1; abel
    _ ≤ ‖m‖ + ‖m - mean (L n) (z n)‖ := norm_sub_le _ _
    _ < ε := by rw [mul_div_assoc] at ht; linarith

/-! ## Atomic averages and their block averages -/

private def atoms (W N : ℕ) (θ : ℝ) : ℂ :=
  mean (2 * N) (fun j ↦ phase (θ * poly W (N + j)))

private def spread (W N : ℕ) (θ : ℝ) : ℂ :=
  mean (2 * N) (fun j ↦
    mean (gap W (N + j)) (fun k ↦ phase (θ * (poly W (N + j) + k : ℕ))))

private lemma gap_mono (W : ℕ) : Monotone (gap W) := by
  intro a b h
  unfold gap
  gcongr

private lemma gap_ge_n {W N : ℕ} (hW : 0 < W) : N ≤ gap W N := by
  have h := Nat.mul_le_mul_right (2 * N + 1) (show 1 ≤ W by omega)
  simp [gap] at ⊢
  omega

private lemma gap_upper {W N j : ℕ} (hW : 0 < W) (hj : j < 2 * N) :
    gap W (N + j) ≤ 6 * W * N := by
  unfold gap
  have h : 2 * (N + j) + 1 + 1 ≤ 6 * N := by omega
  have h' := Nat.mul_le_mul_left W h
  rw [Nat.mul_add, Nat.mul_one] at h'
  nlinarith

private lemma spread_mul_norm (W N : ℕ) (θ : ℝ) :
    ‖1 - phase θ‖ * ‖spread W N θ‖ ≤ 2 / ((2 * N : ℕ) : ℝ) / (gap W N : ℝ) := by
  have hstep (j : ℕ) : (1 - phase θ) *
      (∑ k ∈ range (gap W (N + j)), phase (θ * (poly W (N + j) + k : ℕ))) =
        phase (θ * poly W (N + j)) - phase (θ * poly W (N + (j + 1))) := by
    have heq (k : ℕ) : θ * (poly W (N + j) + k : ℕ) = θ * poly W (N + j) + θ * k := by
      push_cast
      ring
    simp only [heq, phase_geom]
    rw [← heq, ← poly_succ, Nat.add_assoc]
  have hanti : Antitone (fun j : ℕ ↦ (gap W (N + j) : ℝ)⁻¹) := by
    intro a b hab
    apply inv_anti₀ (by exact_mod_cast gap_pos W (N + a))
    exact_mod_cast gap_mono W (Nat.add_le_add_left hab N)
  have hw (j : ℕ) : 0 ≤ (gap W (N + j) : ℝ)⁻¹ := by positivity
  have htel := weighted_telescoping (fun j ↦ phase (θ * poly W (N + j)))
    (fun j ↦ (gap W (N + j) : ℝ)⁻¹) (2 * N) (fun j ↦ (phase_norm _).le) hanti hw
  calc
    _ = ‖(1 - phase θ) * spread W N θ‖ := (norm_mul _ _).symm
    _ = ‖mean (2 * N) (fun j ↦ (1 - phase θ) *
          mean (gap W (N + j)) (fun k ↦ phase (θ * (poly W (N + j) + k : ℕ))))‖ := by
          rw [mean_mul]
          rfl
    _ = ‖mean (2 * N) (fun j ↦ (gap W (N + j) : ℂ)⁻¹ *
          (phase (θ * poly W (N + j)) - phase (θ * poly W (N + (j + 1)))))‖ := by
          congr 1
          apply mean_congr
          intro j _
          rw [mean, mul_left_comm, hstep]
    _ ≤ _ := by
      rw [norm_mean, div_div, mul_comm ((↑(2 * N) : ℝ)), ← div_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [Nat.add_zero, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
        using htel

private lemma atoms_sub_spread_integer {W N : ℕ} (hN : 0 < N) (hW : 0 < W)
    (θ : ℝ) (m : ℤ) :
    ‖atoms W N θ - spread W N θ‖ ≤ 2 * Real.pi * (6 * W : ℝ) * (N : ℝ) * |θ - m| := by
  rw [atoms, spread, ← mean_sub]
  refine mean_norm_le (by omega) fun j hj ↦ ?_
  let p := poly W (N + j)
  let l := gap W (N + j)
  have hl : 0 < l := gap_pos _ _
  change ‖phase (θ * (p : ℝ)) - mean l (fun k ↦ phase (θ * (p + k : ℕ)))‖ ≤ _
  rw [← mean_const hl (phase (θ * (p : ℝ))), ← mean_sub]
  refine mean_norm_le hl fun k hk ↦ ?_
  have hphase (t : ℕ) : phase (θ * (t : ℝ)) = phase ((θ - m) * (t : ℝ)) := by
    rw [show θ * (t : ℝ) = (θ - m) * (t : ℝ) + (m * (t : ℤ) : ℤ) by push_cast; ring,
      phase_add, phase_int, mul_one]
  rw [hphase, hphase]
  apply (phase_dist_le _ _).trans
  rw [show (θ - m) * (p : ℝ) - (θ - m) * (p + k : ℕ) = -((θ - m) * (k : ℝ)) by push_cast; ring,
    abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ))]
  have h' : (k : ℝ) ≤ 6 * W * N := by exact_mod_cast hk.le.trans (gap_upper hW hj)
  calc
    _ = (2 * Real.pi * |θ - m|) * k := by ring
    _ ≤ (2 * Real.pi * |θ - m|) * (6 * W * N) := by gcongr
    _ = _ := by ring

/-! ## Cancellation away from bounded rational scales -/

private lemma grows_mul {f g : ℕ → ℝ} {c : ℝ} (hf : Tendsto f atTop atTop)
    (hc : 0 < c) (hg : ∀ᶠ n in atTop, c ≤ g n) :
    Tendsto (fun n ↦ f n * g n) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [hg, hf.eventually (eventually_ge_atTop (max 0 (b / c)))] with n hgn hfn
  have hf₀ : 0 ≤ f n := (le_max_left _ _).trans hfn
  exact ((div_le_iff₀ hc).1 ((le_max_right _ _).trans hfn)).trans
    (mul_le_mul_of_nonneg_left hgn hf₀)

private lemma geom_vanish {L : ℕ → ℕ} {a b : ℕ → ℝ}
    (h : Tendsto (fun n ↦ (L n : ℝ) * ‖1 - phase (b n)‖) atTop atTop) :
    Tendsto (fun n ↦ ‖mean (L n) (fun j ↦ phase (a n + b n * j))‖) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_const_nhds.div_atTop h (a := 2))
  filter_upwards [h.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  have hl : 0 < (L n : ℝ) := by
    by_contra! hl
    exact (not_le_of_gt hn) (mul_nonpos_of_nonpos_of_nonneg hl (norm_nonneg _))
  have hb := phase_mean_mul_norm (L n) (a n) (b n)
  rw [le_div_iff₀ hn]
  calc
    _ = (‖1 - phase (b n)‖ * ‖mean (L n) (fun j ↦ phase (a n + b n * j))‖) * L n := by ring
    _ ≤ (2 / (L n : ℝ)) * L n := by gcongr
    _ = _ := by field_simp

private lemma tendsto_double {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n ↦ 2 * N n) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [hN.eventually (eventually_ge_atTop b)] with n hn
  omega

private lemma correlation_poly (W N d j h k : ℕ) (θ : ℝ) :
    phase (θ * poly W (N + (j + h * d))) * conj (phase (θ * poly W (N + (j + k * d)))) =
      phase (θ * ((poly W (N + h * d) : ℝ) - poly W (N + k * d)) +
        (2 * (W : ℝ) * ((h : ℝ) - k) * (d : ℝ) * θ) * j) := by
  rw [← phase_sub]
  congr 1
  simp only [poly]
  push_cast
  ring

private lemma atoms_vanish_irrational {W : ℕ} (hW : 0 < W) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) {θ : ℕ → ℝ} {α : ℝ} (hθ : Tendsto θ atTop (𝓝 α))
    (hi : ¬ ∃ x : ℚ, α = x) : Tendsto (fun n ↦ ‖atoms W (N n) (θ n)‖) atTop (𝓝 0) := by
  have hL := tendsto_double hN
  have hLc : Tendsto (fun n ↦ ((2 * N n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hL
  refine mean_vanish_of_shifts (d := fun _ ↦ 1) hL (fun _ _ ↦ phase_norm _) ?_ ?_
  · simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hLc
  intro h k hk
  let c : ℝ := 2 * (W : ℝ) * ((h : ℝ) - k)
  have hc : c ≠ 0 := by
    have hne : (h : ℝ) ≠ k := by exact_mod_cast hk
    exact mul_ne_zero (by positivity) (sub_ne_zero.mpr hne)
  have hne : phase (c * α) ≠ 1 := by
    intro he
    obtain ⟨m, hm⟩ := phase_eq_one.1 he
    apply hi
    refine ⟨(m : ℚ) / (2 * (W : ℚ) * ((h : ℚ) - k)), ?_⟩
    push_cast
    change α = (m : ℝ) / c
    apply (eq_div_iff hc).2
    rw [mul_comm, hm]
  have hpc : 0 < ‖1 - phase (c * α)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hlim : Tendsto (fun n ↦ ‖1 - phase (c * θ n)‖) atTop (𝓝 ‖1 - phase (c * α)‖) :=
    (tendsto_const_nhds.sub (phase_continuous.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := c)).mul hθ))).norm
  have hp : ∀ᶠ n in atTop, ‖1 - phase (c * α)‖ / 2 < ‖1 - phase (c * θ n)‖ :=
    hlim.eventually (lt_mem_nhds (half_lt_self hpc))
  have hgood := grows_mul hLc (half_pos hpc) (hp.mono fun _ h ↦ h.le)
  have hgeo := geom_vanish (a := fun n ↦ θ n * ((poly W (N n + h) : ℝ) - poly W (N n + k))) hgood
  convert hgeo using 1
  funext n
  congr 1
  apply mean_congr
  intro j _
  simpa only [c, Nat.cast_one, mul_one] using correlation_poly W (N n) 1 j h k (θ n)

private lemma sqrt_scale {N : ℕ → ℕ} {β : ℕ → ℝ}
    (hg : Tendsto (fun n ↦ (N n : ℝ) ^ 2 * |β n|) atTop atTop) :
    Tendsto (fun n ↦ (N n : ℝ) * √|β n|) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [hg.eventually (eventually_ge_atTop (b ^ 2))] with n hn
  have hn₀ : 0 ≤ (N n : ℝ) * √|β n| := by positivity
  have hsq : ((N n : ℝ) * √|β n|) ^ 2 = (N n : ℝ) ^ 2 * |β n| := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  by_cases hb : 0 ≤ b
  · exact le_of_pow_le_pow_left₀ two_ne_zero hn₀ (hsq ▸ hn)
  · exact (le_of_not_ge hb).trans hn₀

private lemma floor_sqrt_mul {β : ℕ → ℝ} (hβ : Tendsto β atTop (𝓝 0))
    (hnz : ∀ᶠ n in atTop, β n ≠ 0) :
    Tendsto (fun n ↦ (⌊(√|β n|)⁻¹⌋₊ : ℝ) * √|β n|) atTop (𝓝 1) := by
  have hs : Tendsto (fun n ↦ √|β n|) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt (x := (0 : ℝ))
    have hl := hβ.abs
    rw [abs_zero] at hl
    have hp := ht.tendsto.comp hl
    rw [Real.sqrt_zero] at hp
    exact hp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n ↦ 1 - √|β n|)
    (h := fun _ ↦ 1) (by simpa only [sub_zero] using tendsto_const_nhds.sub hs) tendsto_const_nhds
  · filter_upwards [hnz] with n hn
    have hp : 0 < √|β n| := Real.sqrt_pos.2 (abs_pos.2 hn)
    have h := Nat.lt_floor_add_one (√|β n|)⁻¹
    have hm := mul_lt_mul_of_pos_right h hp
    rw [inv_mul_cancel₀ hp.ne', add_mul, one_mul] at hm
    linarith
  · filter_upwards [hnz] with n hn
    have hp : 0 < √|β n| := Real.sqrt_pos.2 (abs_pos.2 hn)
    have hm := mul_le_mul_of_nonneg_right (Nat.floor_le (inv_nonneg.2 hp.le)) hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at hm

private lemma atoms_vanish_rational_far {W : ℕ} (hW : 0 < W) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) {θ : ℕ → ℝ} (a : ℤ) {q : ℕ} (hq : 0 < q)
    (hθ : Tendsto θ atTop (𝓝 ((a : ℝ) / q)))
    (hg : Tendsto (fun n ↦ (N n : ℝ) ^ 2 * |θ n - (a : ℝ) / q|) atTop atTop) :
    Tendsto (fun n ↦ ‖atoms W (N n) (θ n)‖) atTop (𝓝 0) := by
  let β (n : ℕ) := θ n - (a : ℝ) / q
  let s (n : ℕ) := √|β n|
  let D (n : ℕ) := ⌊(s n)⁻¹⌋₊
  let d (n : ℕ) := q * D n
  have hβ : Tendsto β atTop (𝓝 0) := by
    simpa only [sub_self] using hθ.sub (tendsto_const_nhds (x := (a : ℝ) / q))
  have hβnz : ∀ᶠ n in atTop, β n ≠ 0 := by
    filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    change 0 < (N n : ℝ) ^ 2 * |β n| at hn
    intro h
    simp [h] at hn
  have hs₀ : ∀ᶠ n in atTop, 0 < s n := hβnz.mono fun n hn ↦ Real.sqrt_pos.2 (abs_pos.2 hn)
  have hs : Tendsto s atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt (x := (0 : ℝ))
    have hl := hβ.abs
    rw [abs_zero] at hl
    have hp := ht.tendsto.comp hl
    rw [Real.sqrt_zero] at hp
    exact hp
  have hDs : Tendsto (fun n ↦ (D n : ℝ) * s n) atTop (𝓝 1) := floor_sqrt_mul hβ hβnz
  have hNs : Tendsto (fun n ↦ (N n : ℝ) * s n) atTop atTop := sqrt_scale hg
  have hd : Tendsto (fun n ↦ (d n : ℝ) / ((2 * N n : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (q : ℝ) / 2)).mul hDs).div_atTop hNs
    apply h.congr'
    filter_upwards [hs₀] with n hn
    simp only [d, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hn.ne']
  refine mean_vanish_of_shifts (d := d) (tendsto_double hN) (fun _ _ ↦ phase_norm _) hd ?_
  intro h k hk
  let c : ℝ := 2 * (W : ℝ) * ((h : ℝ) - k) * q
  let b (n : ℕ) := c * (D n : ℝ) * β n
  have hc : c ≠ 0 := by
    have hne : (h : ℝ) ≠ k := by exact_mod_cast hk
    have hwq : (0 : ℝ) < W ∧ (0 : ℝ) < q := ⟨by exact_mod_cast hW, by exact_mod_cast hq⟩
    dsimp [c]
    exact mul_ne_zero (mul_ne_zero (by positivity) (sub_ne_zero.mpr hne)) hwq.2.ne'
  have habs (n : ℕ) : |b n| = (|c| * ((D n : ℝ) * s n)) * s n := by
    simp only [b, abs_mul, abs_of_nonneg (show 0 ≤ (D n : ℝ) by positivity)]
    have he : s n * s n = |β n| := by
      rw [← pow_two, Real.sq_sqrt (abs_nonneg _)]
    rw [← he]
    ring
  have hb : Tendsto (fun n ↦ |b n|) atTop (𝓝 0) := by
    simpa only [habs, mul_one, mul_zero] using ((tendsto_const_nhds (x := |c|)).mul hDs).mul hs
  have hbig : Tendsto (fun n ↦ ((2 * N n : ℕ) : ℝ) * ‖1 - phase (b n)‖) atTop atTop := by
    have hprod := grows_mul hNs (g := fun _ ↦ |c|) (abs_pos.2 hc)
      (Eventually.of_forall fun _ ↦ le_rfl)
    refine tendsto_atTop.2 fun M ↦ ?_
    have hMn := hprod.eventually (eventually_ge_atTop M)
    filter_upwards [hb.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
      hDs.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)), hMn] with n hbn hDn hM
    have hsmall := phase_small (b n) hbn
    rw [norm_sub_rev, habs] at hsmall
    have hspos : 0 ≤ s n := Real.sqrt_nonneg _
    have hle : 2 * |c| * s n ≤ ‖1 - phase (b n)‖ := by
      refine le_trans ?_ hsmall
      calc
        _ = 4 * (|c| * (1 / 2)) * s n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDn.le (abs_nonneg _))
            (by norm_num)) hspos |>.trans_eq (by ring)
    apply hM.trans
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    have hcs : 0 ≤ (N n : ℝ) * s n * |c| := by positivity
    calc
      _ ≤ (N n : ℝ) * (2 * |c| * s n) := by nlinarith
      _ ≤ (N n : ℝ) * ‖1 - phase (b n)‖ := by gcongr
      _ ≤ _ := by nlinarith [norm_nonneg (1 - phase (b n))]
  have hgeo := geom_vanish (a := fun n ↦ θ n *
    ((poly W (N n + h * d n) : ℝ) - poly W (N n + k * d n))) hbig
  convert hgeo using 1
  funext n
  congr 1
  apply mean_congr
  intro j _
  rw [correlation_poly]
  have heq : 2 * (W : ℝ) * ((h : ℝ) - k) * (d n : ℝ) * θ n * j =
      b n * j + ((2 * (W : ℤ) * ((h : ℤ) - k) * D n * a * j : ℤ) : ℝ) := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simp only [b, β, c, d]
    push_cast
    field_simp
    ring
  rw [heq, ← add_assoc, phase_add, phase_int, mul_one]

/-! ## Complete quadratic sums -/

section Characters

-- Keep the simplifier's auxiliary congruence lemmas private to this module.
private def residueChar {q : ℕ} [NeZero q] : AddChar (ZMod q) ℂ := ZMod.stdAddChar

variable {q : ℕ} [NeZero q]

private lemma char_norm (x : ZMod q) : ‖residueChar x‖ = 1 :=
  Circle.norm_coe _

private lemma char_int (a : ℤ) : residueChar (a : ZMod q) = phase ((a : ℝ) / q) := by
  change ZMod.stdAddChar (a : ZMod q) = phase ((a : ℝ) / q)
  rw [ZMod.stdAddChar_coe, phase]
  congr 1
  push_cast
  ring

private lemma char_nat (m : ℕ) : residueChar (m : ZMod q) = phase ((m : ℝ) / q) := by
  simpa only [Int.cast_natCast] using char_int (q := q) (m : ℤ)

private lemma char_neg (x : ZMod q) : conj (residueChar x) = residueChar (-x) := by
  have hx : ((x.val : ℤ) : ZMod q) = x := by simp
  rw [← hx, ← Int.cast_neg, char_int, char_int, phase_conj, Int.cast_neg, neg_div]

private lemma char_sub (x y : ZMod q) :
    residueChar (x - y) = residueChar x * conj (residueChar y) := by
  rw [char_neg, sub_eq_add_neg, AddChar.map_add_eq_mul]

private lemma char_ortho (t : ZMod q) :
    ∑ x : ZMod q, residueChar (t * x) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

omit [NeZero q] in
private lemma cast_int_unit (a : ℤ) (h : a.natAbs.Coprime q) : IsUnit (a : ZMod q) := by
  have hu := (ZMod.isUnit_iff_coprime a.natAbs q).2 h
  cases a with
  | ofNat n => simpa using hu
  | negSucc n =>
    change IsUnit ((Int.negSucc n : ℤ) : ZMod q)
    change IsUnit ((Int.negSucc n).natAbs : ZMod q) at hu
    have hnat : (Int.negSucc n).natAbs = n + 1 := rfl
    rw [hnat] at hu
    simpa only [Int.negSucc_eq, Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast,
      Nat.cast_add, Nat.cast_one] using hu.neg

private def polyMod (W : ℕ) (n : ZMod q) : ZMod q := (W : ZMod q) * n ^ 2 + n

omit [NeZero q] in
private lemma poly_mod (W n : ℕ) : (poly W n : ZMod q) = polyMod W (n : ZMod q) := by
  simp [poly, polyMod]

private def gauss (W : ℕ) (a : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j : ZMod q, residueChar (a * polyMod W j)

private lemma gauss_zero_of_nonunit {W : ℕ} {a : ZMod q} (ha : IsUnit a)
    (hW : ¬ IsUnit (W : ZMod q)) : gauss W a = 0 := by
  classical
  let f (x : ZMod q) := (W : ZMod q) * x
  have hn : ¬ Function.Injective f := by
    intro h
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective h 1
    exact hW (isUnit_iff_exists_inv.2 ⟨b, hb⟩)
  unfold Function.Injective at hn
  push Not at hn
  obtain ⟨x, y, hxy, hne⟩ := hn
  let u := x - y
  have hu : u ≠ 0 := sub_ne_zero.2 hne
  have hmul : (W : ZMod q) * u = 0 := by
    change (W : ZMod q) * x = (W : ZMod q) * y at hxy
    simp [u, mul_sub, hxy]
  have ht : residueChar (a * u) ≠ 1 := by
    intro h
    rw [← (residueChar (q := q)).map_zero_eq_one] at h
    apply hu
    apply ha.mul_left_cancel
    simpa only [mul_zero] using ZMod.injective_stdAddChar h
  let F (j : ZMod q) := residueChar (a * polyMod W j)
  have hshift (j : ZMod q) : F (j + u) = residueChar (a * u) * F j := by
    have hp : polyMod W (j + u) = u + polyMod W j := by
      dsimp [polyMod]
      linear_combination (2 * j + u) * hmul
    simp only [F, hp, mul_add, AddChar.map_add_eq_mul]
  have he : (∑ j, F j) = ∑ j, F (j + u) :=
    (Fintype.sum_equiv (Equiv.addRight u) (fun j ↦ F (j + u)) F (fun _ ↦ rfl)).symm
  simp only [hshift, ← mul_sum] at he
  have hz : (∑ j, F j) = 0 := by
    apply (mul_eq_zero.1 (show (1 - residueChar (a * u)) * (∑ j, F j) = 0 by
      rw [sub_mul, one_mul, ← he, sub_self])).resolve_left
    exact sub_ne_zero.2 ht.symm
  exact mul_eq_zero_of_right _ hz

private lemma twice_zero_card : #{j : ZMod q | (2 : ZMod q) * j = 0} ≤ 2 := by
  classical
  refine (card_le_card (t := {0, ((q / 2 : ℕ) : ZMod q)}) ?_).trans card_le_two
  intro j hj
  have hz := (mem_filter.1 hj).2
  have hd : q ∣ 2 * j.val := by
    apply (ZMod.natCast_eq_zero_iff _ q).1
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hz
  obtain ⟨m, hm⟩ := hd
  have hv := ZMod.val_lt j
  have hm' : m ≤ 1 := by
    by_contra! h
    have hh := Nat.mul_le_mul_left q (show 2 ≤ m by omega)
    omega
  rcases (show m = 0 ∨ m = 1 by omega) with h | h
  · rw [h, Nat.mul_zero] at hm
    have hj0 : j.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val j, hj0]
    simp
  · rw [h, Nat.mul_one] at hm
    have hj0 : j.val = q / 2 := by omega
    rw [← ZMod.natCast_zmod_val j, hj0]
    simp

private lemma gauss_sq_le {W : ℕ} {a : ZMod q} (ha : IsUnit a) :
    ‖gauss W a‖ ^ 2 ≤ 2 / (q : ℝ) := by
  classical
  by_cases hu : IsUnit (W : ZMod q)
  · let F (j : ZMod q) := residueChar (a * polyMod W j)
    let S : ℂ := ∑ j, F j
    have hexpand : (↑(‖S‖ ^ 2) : ℂ) = ∑ h : ZMod q, ∑ j : ZMod q, F (j + h) * conj (F j) := by
      rw [cast_norm_sq]
      simp only [S, map_sum, sum_mul]
      trans ∑ j : ZMod q, ∑ k : ZMod q, F k * conj (F j)
      · rw [sum_comm]
        exact sum_congr rfl (fun _ _ ↦ mul_sum ..)
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro j _
      exact Fintype.sum_equiv (Equiv.addRight j).symm _ _ fun k ↦ by
        simp
    have hline (h j : ZMod q) : F (j + h) * conj (F j) =
        F h * residueChar (((2 : ZMod q) * h * (a * (W : ZMod q))) * j) := by
      simp only [F, ← char_sub, ← AddChar.map_add_eq_mul]
      congr 1
      dsimp [polyMod]
      ring
    have helim (h : ZMod q) :
        ((2 : ZMod q) * h * (a * (W : ZMod q))) = 0 ↔ (2 : ZMod q) * h = 0 := by
      constructor
      · intro hzero
        exact (ha.mul hu).mul_right_cancel (hzero.trans (zero_mul _).symm)
      · intro hh
        rw [hh, zero_mul]
    simp only [hline, ← mul_sum, char_ortho, helim, mul_ite, mul_zero, ← sum_filter] at hexpand
    have hsq := congrArg norm hexpand
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hsq
    have hb : ‖S‖ ^ 2 ≤ 2 * (q : ℝ) := by
      rw [hsq]
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_mul, char_norm, Complex.norm_natCast, one_mul, sum_const, nsmul_eq_mul, F]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast twice_zero_card (q := q)) (by positivity)
    change ‖(q : ℂ)⁻¹ * S‖ ^ 2 ≤ _
    rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    calc
      _ ≤ ((q : ℝ)⁻¹) ^ 2 * (2 * (q : ℝ)) := by gcongr
      _ = _ := by field_simp
  · rw [gauss_zero_of_nonunit ha hu, norm_zero]
    have : (0 : ℝ) ≤ 2 / (q : ℝ) := by positivity
    simpa using this

private lemma gauss_zero_of_dvd {W : ℕ} {a : ZMod q} (ha : IsUnit a)
    (hq : 1 < q) (hd : q ∣ W) : gauss W a = 0 := by
  have hW : (W : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff W q).2 hd
  let : Fact (1 < q) := ⟨hq⟩
  exact gauss_zero_of_nonunit ha (hW ▸ not_isUnit_zero)

private lemma char_rational_mul (a : ℤ) (m : ℕ) :
    phase (((a : ℝ) / q) * (m : ℝ)) = residueChar ((a : ZMod q) * (m : ZMod q)) := by
  rw [← Int.cast_natCast (R := ZMod q) m, ← Int.cast_mul, char_int]
  push_cast
  ring_nf

private lemma gauss_shift (W : ℕ) (a : ZMod q) (n : ℕ) :
    mean q (fun h ↦ residueChar (a * polyMod W ((n + h : ℕ) : ZMod q))) = gauss W a := by
  simp only [mean, gauss, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Fintype.sum_equiv ((ZMod.finEquiv q).toEquiv.trans (Equiv.addLeft (n : ZMod q)))
  intro h
  have he : ZMod.finEquiv q h = (h.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
      apply ZMod.val_injective (n + 1)
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h.isLt]
      rfl
  change _ = residueChar (a * polyMod W ((n : ZMod q) + ZMod.finEquiv q h))
  rw [he, Nat.cast_add]

end Characters

/-! ## Comparison at bounded rational scales -/

private lemma poly_add_le {W N j h q : ℕ} (hN : 0 < N) (hj : j < 2 * N) (hh : h < q) :
    (poly W (N + j + h) : ℝ) - poly W (N + j) ≤
      ((q : ℝ) * ((W : ℝ) * (6 + q) + 1)) * N := by
  have hq : (h : ℝ) ≤ q := by exact_mod_cast hh.le
  have hj' : (j : ℝ) ≤ 2 * N := by exact_mod_cast hj.le
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have haux : 2 * ((N : ℝ) + j) + h ≤ (6 + (q : ℝ)) * N := by
    have hqN : (q : ℝ) ≤ (q : ℝ) * N := by nlinarith [Nat.cast_nonneg (α := ℝ) q]
    linarith
  have hincr : (poly W (N + j + h) : ℝ) - poly W (N + j) =
      (h : ℝ) * ((W : ℝ) * (2 * ((N : ℝ) + j) + h) + 1) := by
    simp only [poly]
    push_cast
    ring
  rw [hincr]
  calc
    _ ≤ (q : ℝ) * ((W : ℝ) * ((6 + (q : ℝ)) * N) + (N : ℝ)) := by gcongr
    _ = _ := by ring

private lemma atoms_near_rational {W N : ℕ} (hN : 0 < N) {q : ℕ} [NeZero q]
    (a : ℤ) (θ : ℝ) :
    ‖atoms W N θ‖ ≤ ‖gauss W (a : ZMod q)‖ +
      (2 * Real.pi * ((q : ℝ) * ((W : ℝ) * (6 + q) + 1))) * (N : ℝ) * |θ - (a : ℝ) / q| +
      (q : ℝ) / N := by
  let z (j : ℕ) := phase (θ * poly W (N + j))
  let β := θ - (a : ℝ) / q
  let v (j : ℕ) := phase (β * poly W (N + j)) * gauss W (a : ZMod q)
  let B := 2 * Real.pi * ((q : ℝ) * ((W : ℝ) * (6 + q) + 1)) * (N : ℝ) * |β|
  let m := mean (2 * N) (fun j ↦ mean q (fun h ↦ z (j + h)))
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hshift : ‖m - atoms W N θ‖ ≤ (q : ℝ) / N := by
    have hs := shifted_mean_distance (L := 2 * N) hq 1 z fun _ ↦ phase_norm _
    change ‖m - atoms W N θ‖ ≤ _
    simpa [m, atoms, z, mul_div_mul_left, div_eq_mul_inv, mul_comm, mul_left_comm] using hs
  have hnorm : ‖mean (2 * N) v‖ ≤ ‖gauss W (a : ZMod q)‖ := by
    refine mean_norm_le (by omega) fun j _ ↦ ?_
    dsimp only [v]
    rw [norm_mul, phase_norm, one_mul]
  have hdiff : ‖m - mean (2 * N) v‖ ≤ B := by
    unfold m
    rw [← mean_sub]
    refine mean_norm_le (by omega) fun j hj ↦ ?_
    have hv : v j = mean q (fun h ↦ phase (β * poly W (N + j)) *
        residueChar ((a : ZMod q) * polyMod W ((N + j + h : ℕ) : ZMod q))) := by
      rw [mean_mul, gauss_shift]
    rw [hv, ← mean_sub]
    refine mean_norm_le hq fun h hh ↦ ?_
    have ht (l : ℕ) : phase (θ * poly W l) =
        phase (β * poly W l) * residueChar ((a : ZMod q) * polyMod W (l : ZMod q)) := by
      rw [← poly_mod, ← char_rational_mul, ← phase_add]
      congr 1
      dsimp [β]
      ring
    dsimp only [z]
    rw [ht, ← Nat.add_assoc, ← sub_mul, norm_mul, char_norm, mul_one]
    apply (phase_dist_le _ _).trans
    have hi : 0 ≤ (poly W (N + j + h) : ℝ) - poly W (N + j) := by
      apply sub_nonneg.2
      exact_mod_cast (poly_strictMono W).monotone (Nat.le_add_right (N + j) h)
    rw [← mul_sub, abs_mul, abs_of_nonneg hi]
    calc
      _ ≤ 2 * Real.pi * (|β| * (((q : ℝ) * ((W : ℝ) * (6 + q) + 1)) * N)) := by
        gcongr
        exact poly_add_le hN hj hh
      _ = B := by dsimp [B]; ring
  calc
    _ = ‖mean (2 * N) v + ((m - mean (2 * N) v) - (m - atoms W N θ))‖ := by congr 1; abel
    _ ≤ _ := by
      refine (norm_add_le _ _).trans ?_
      have hh := norm_sub_le (m - mean (2 * N) v) (m - atoms W N θ)
      change ‖mean (2 * N) v‖ + ‖(m - mean (2 * N) v) - (m - atoms W N θ)‖ ≤ _
      change _ ≤ ‖gauss W (a : ZMod q)‖ + B + (q : ℝ) / N
      linarith

/-! ## The uniform comparison -/

private lemma spread_vanish_of_growth {W : ℕ} (hW : 0 < W) {N : ℕ → ℕ} {θ : ℕ → ℝ}
    (hg : Tendsto (fun n ↦ (N n : ℝ) ^ 2 * ‖1 - phase (θ n)‖) atTop atTop) :
    Tendsto (fun n ↦ ‖spread W (N n) (θ n)‖) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_const_nhds.div_atTop hg (a := 1))
  filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with n hpos
  have hN : (0 : ℝ) < N n := by
    by_contra! hn
    have hz : (N n : ℝ) = 0 := le_antisymm hn (by positivity)
    simp [hz] at hpos
  have hgN : (N n : ℝ) ≤ gap W (N n) := by exact_mod_cast gap_ge_n hW (N := N n)
  have hgpos : (0 : ℝ) < gap W (N n) := hN.trans_le hgN
  have hb := spread_mul_norm W (N n) (θ n)
  have ht : 2 / ((2 * N n : ℕ) : ℝ) / (gap W (N n) : ℝ) ≤ 1 / (N n : ℝ) ^ 2 := by
    push_cast
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hgN hN.le]
  rw [le_div_iff₀ hpos]
  calc
    _ = (‖1 - phase (θ n)‖ * ‖spread W (N n) (θ n)‖) * (N n : ℝ) ^ 2 := by ring
    _ ≤ (1 / (N n : ℝ) ^ 2) * (N n : ℝ) ^ 2 := by gcongr; exact hb.trans ht
    _ = _ := by field_simp

private lemma spread_vanish_noninteger {W : ℕ} (hW : 0 < W) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) {θ : ℕ → ℝ} {α : ℝ} (hθ : Tendsto θ atTop (𝓝 α))
    (ha : ¬ ∃ m : ℤ, α = m) : Tendsto (fun n ↦ ‖spread W (N n) (θ n)‖) atTop (𝓝 0) := by
  have hpos : 0 < ‖1 - phase α‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (fun h ↦ ha (phase_eq_one.1 h.symm)))
  have hc : Tendsto (fun n ↦ ‖1 - phase (θ n)‖) atTop (𝓝 ‖1 - phase α‖) :=
    (tendsto_const_nhds.sub (phase_continuous.continuousAt.tendsto.comp hθ)).norm
  have hl : ∀ᶠ n in atTop, ‖1 - phase α‖ / 2 < ‖1 - phase (θ n)‖ :=
    hc.eventually (lt_mem_nhds (half_lt_self hpos))
  have hn : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hn2 : Tendsto (fun n ↦ (N n : ℝ) ^ 2) atTop atTop := by
    simpa only [pow_two] using grows_mul hn one_pos (hn.eventually (eventually_ge_atTop 1))
  exact spread_vanish_of_growth hW (grows_mul hn2 (half_pos hpos) (hl.mono fun _ h ↦ h.le))

private lemma spread_vanish_integer_far {W : ℕ} (hW : 0 < W) {N : ℕ → ℕ} {θ : ℕ → ℝ}
    (m : ℤ) (hθ : Tendsto θ atTop (𝓝 (m : ℝ)))
    (hg : Tendsto (fun n ↦ (N n : ℝ) ^ 2 * |θ n - m|) atTop atTop) :
    Tendsto (fun n ↦ ‖spread W (N n) (θ n)‖) atTop (𝓝 0) := by
  apply spread_vanish_of_growth hW
  refine tendsto_atTop.2 fun B ↦ ?_
  have ht : Tendsto (fun n ↦ |θ n - m|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hθ.sub (tendsto_const_nhds (x := (m : ℝ)))).abs
  filter_upwards [hg.eventually (eventually_ge_atTop B),
    ht.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)] with n hB hn
  have hsmall := phase_small (θ n - m) hn
  have heq : phase (θ n - m) = phase (θ n) := by
    have hh := phase_add (θ n - m) (m : ℝ)
    simpa only [sub_add_cancel, phase_int, mul_one] using hh.symm
  rw [heq, norm_sub_rev] at hsmall
  refine hB.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  linarith [abs_nonneg (θ n - m)]

private lemma scaled_tends_zero {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {β : ℕ → ℝ}
    {B : ℝ} (hB : ∀ᶠ n in atTop, (N n : ℝ) ^ 2 * |β n| ≤ B) :
    Tendsto (fun n ↦ (N n : ℝ) * |β n|) atTop (𝓝 0) := by
  have hn : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    (tendsto_const_nhds.div_atTop hn (a := B))
  filter_upwards [hB, hn.eventually (eventually_gt_atTop (0 : ℝ))] with n hb hp
  apply (le_div_iff₀ hp).2
  convert hb using 1
  ring

private lemma extract_growth (f : ℕ → ℝ) (h : ¬ ∃ C, ∀ᶠ n in atTop, f n ≤ C) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ Tendsto (f ∘ k) atTop atTop := by
  classical
  have hex (j : ℕ) : ∃ n ≥ j, (j : ℝ) ≤ f n := by
    by_contra! hn
    apply h
    exact ⟨j, (eventually_ge_atTop j).mono (fun n hn' ↦ (hn n hn').le)⟩
  choose k hk hfk using hex
  refine ⟨k, tendsto_atTop.2 fun b ↦ (eventually_ge_atTop b).mono (fun n hn ↦ hn.trans (hk n)), ?_⟩
  refine tendsto_atTop.2 fun b ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hm.le.trans ((by exact_mod_cast hn : (m : ℝ) ≤ n).trans (hfk n))

private lemma uniform_discrepancy {K : ℕ} (hK : 2 ≤ K) {ε : ℝ} (hε : 0 < ε)
    (hscale : 2 / (K : ℝ) < ε ^ 2) :
    ∀ᶠ N in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖atoms K.factorial N θ - spread K.factorial N θ‖ < ε := by
  classical
  let W := K.factorial
  have hW : 0 < W := Nat.factorial_pos K
  by_contra! hbad
  rw [frequently_atTop] at hbad
  choose N hN θ hθ hεbad using hbad
  obtain ⟨α, _, k, hk, hlim⟩ := isCompact_Icc.tendsto_subseq (x := θ) hθ
  let M := N ∘ k
  let t := θ ∘ k
  have hM : Tendsto M atTop atTop := (tendsto_atTop.2 fun b ↦
    (eventually_ge_atTop b).mono (fun n hn ↦ hn.trans (hN n))).comp hk.tendsto_atTop
  have hfail (n : ℕ) : ε ≤ ‖atoms W (M n) (t n) - spread W (M n) (t n)‖ := hεbad (k n)
  have contradiction {L : ℕ → ℕ} {u : ℕ → ℝ} (hlarge : ∀ n,
      ε ≤ ‖atoms W (L n) (u n) - spread W (L n) (u n)‖)
      (ha : Tendsto (fun n ↦ ‖atoms W (L n) (u n)‖) atTop (𝓝 0))
      (hs : Tendsto (fun n ↦ ‖spread W (L n) (u n)‖) atTop (𝓝 0)) : False := by
    have ht : Tendsto (fun n ↦ ‖atoms W (L n) (u n)‖ + ‖spread W (L n) (u n)‖) atTop (𝓝 0) :=
      by simpa only [add_zero] using ha.add hs
    have hsmall := ht.eventually_lt_const hε
    obtain ⟨n, hn⟩ := hsmall.exists
    exact (not_lt_of_ge ((hlarge n).trans (norm_sub_le _ _))) hn
  by_cases hr : ∃ x : ℚ, α = x
  · obtain ⟨x, rfl⟩ := hr
    let q := x.den
    let a := x.num
    have hq : 0 < q := x.den_pos
    let : NeZero q := ⟨hq.ne'⟩
    have hx : (x : ℝ) = (a : ℝ) / q := Rat.cast_def x
    have hlim' : Tendsto t atTop (𝓝 ((a : ℝ) / q)) := hx ▸ hlim
    let f (n : ℕ) := (M n : ℝ) ^ 2 * |t n - (a : ℝ) / q|
    by_cases hbdd : ∃ C : ℝ, ∀ᶠ n in atTop, f n ≤ C
    · obtain ⟨C, hC⟩ := hbdd
      have hβ := scaled_tends_zero hM hC
      by_cases hq1 : q = 1
      · have hxa : (a : ℝ) / q = (a : ℝ) := by simp [hq1]
        have hβ' : Tendsto (fun n ↦ (M n : ℝ) * |t n - a|) atTop (𝓝 0) := by
          simpa only [hxa] using hβ
        have he := (tendsto_const_nhds (x := 2 * Real.pi * (6 * W : ℝ))).mul hβ'
        have he' : Tendsto (fun n ↦ 2 * Real.pi * (6 * W : ℝ) * (M n : ℝ) * |t n - a|)
            atTop (𝓝 0) := by simpa only [mul_zero, mul_assoc] using he
        obtain ⟨n, hn, hsmall⟩ := ((hM.eventually (eventually_gt_atTop 0)).and
          (he'.eventually_lt_const hε)).exists
        exact (not_lt_of_ge ((hfail n).trans (atoms_sub_spread_integer hn hW (t n) a))) hsmall
      have hq2 : 1 < q := by omega
      have hint : ¬ ∃ m : ℤ, (x : ℝ) = m := by
        rintro ⟨m, hm⟩
        have he : x = (m : ℚ) := Rat.cast_injective (by simpa using hm)
        exact hq1 (by simpa only [q, he] using Rat.den_intCast m)
      have hsp := spread_vanish_noninteger hW hM hlim hint
      have hau : IsUnit (a : ZMod q) := cast_int_unit a x.reduced
      have hG : ‖gauss W (a : ZMod q)‖ < ε := by
        by_cases hqK : q ≤ K
        · rw [gauss_zero_of_dvd hau hq2 (Nat.dvd_factorial hq hqK), norm_zero]
          exact hε
        have hk' : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
        have hle : (K : ℝ) ≤ q := by exact_mod_cast (by omega : K ≤ q)
        have hsq := (gauss_sq_le (W := W) hau).trans_lt
          ((div_le_div_of_nonneg_left (by norm_num) hk' hle).trans_lt hscale)
        by_contra! hbad'
        linarith [pow_le_pow_left₀ hε.le hbad' 2]
      let c : ℝ := 2 * Real.pi * ((q : ℝ) * ((W : ℝ) * (6 + q) + 1))
      have hMc : Tendsto (fun n ↦ (M n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
      have hErr : Tendsto (fun n ↦ c * (M n : ℝ) * |t n - (a : ℝ) / q| + (q : ℝ) / M n +
          ‖spread W (M n) (t n)‖) atTop (𝓝 0) := by
        simpa only [mul_zero, zero_add, mul_assoc] using
          (((tendsto_const_nhds (x := c)).mul hβ).add
            ((tendsto_const_nhds (x := (q : ℝ))).div_atTop hMc)).add hsp
      have hev := hErr.eventually_lt_const (sub_pos.2 hG)
      obtain ⟨n, hn, herr⟩ := ((hM.eventually (eventually_gt_atTop 0)).and hev).exists
      have hc := atoms_near_rational (W := W) (q := q) hn a (t n)
      have hl := (hfail n).trans (norm_sub_le (atoms W (M n) (t n)) (spread W (M n) (t n)))
      dsimp [c] at herr
      linarith
    · obtain ⟨j, hj, hgrow⟩ := extract_growth f hbdd
      let L := M ∘ j
      let u := t ∘ j
      have hL : Tendsto L atTop atTop := hM.comp hj
      have hu : Tendsto u atTop (𝓝 ((a : ℝ) / q)) := hlim'.comp hj
      have ha := atoms_vanish_rational_far hW hL a hq hu hgrow
      refine contradiction (fun n ↦ hfail (j n)) ha ?_
      by_cases hm : ∃ m : ℤ, (a : ℝ) / q = m
      · obtain ⟨m, hm⟩ := hm
        rw [hm] at hu
        apply spread_vanish_integer_far hW m hu
        change Tendsto (fun n ↦ (M (j n) : ℝ) ^ 2 * |t (j n) - (m : ℝ)|) atTop atTop
        rw [← hm]
        exact hgrow
      · exact spread_vanish_noninteger hW hL hu hm
  · refine contradiction hfail (atoms_vanish_irrational hW hM hlim hr) ?_
    apply spread_vanish_noninteger hW hM hlim
    rintro ⟨m, hm⟩
    exact hr ⟨(m : ℚ), by simpa using hm⟩

/-! ## Fourier inversion for the pair count -/

private def pairCount (A : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ A, if a + b = t then 1 else 0

private lemma pairCount_nonneg (A : Finset ℕ) (t : ℕ) : 0 ≤ pairCount A t := by
  unfold pairCount
  exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

private def realMean (L : ℕ) (f : ℕ → ℝ) : ℝ := (∑ j ∈ range L, f j) / (L : ℝ)

private lemma cast_realMean (L : ℕ) (f : ℕ → ℝ) :
    (↑(realMean L f) : ℂ) = mean L (fun j ↦ (f j : ℂ)) := by
  rw [realMean, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum,
    div_eq_mul_inv, mul_comm, mean]

private lemma mean_sum {α : Type*} (L : ℕ) (s : Finset α) (f : α → ℕ → ℂ) :
    mean L (fun j ↦ ∑ x ∈ s, f x j) = ∑ x ∈ s, mean L (f x) := by
  simp only [mean, ← mul_sum]
  rw [sum_comm]

section Fourier

variable {Q : ℕ} [NeZero Q]

private def freq (A : Finset ℕ) (k : ZMod Q) : ℂ :=
  ∑ a ∈ A, residueChar (-(a : ZMod Q) * k)

private lemma char_freq_phase (k : ZMod Q) (t : ℕ) :
    residueChar ((t : ZMod Q) * k) = phase (((k.val : ℝ) / Q) * t) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul, char_nat]
  push_cast
  congr 1
  ring

omit [NeZero Q] in
private lemma zmod_nat_eq {x y : ℕ} (hx : x < Q) (hy : y < Q) :
    ((x : ZMod Q) = (y : ZMod Q)) ↔ x = y := by
  constructor
  · intro h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      using congrArg ZMod.val h
  · exact fun h ↦ congrArg (fun n : ℕ ↦ (n : ZMod Q)) h

private lemma pair_inversion (A : Finset ℕ) {t : ℕ} (ht : t < Q)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a + b < Q) :
    (↑(pairCount A t) : ℂ) = (Q : ℂ)⁻¹ *
      ∑ k : ZMod Q, freq A k ^ 2 * residueChar ((t : ZMod Q) * k) := by
  classical
  have hp (k : ZMod Q) : freq A k ^ 2 * residueChar ((t : ZMod Q) * k) =
      ∑ a ∈ A, ∑ b ∈ A, residueChar (((t : ZMod Q) - ((a + b : ℕ) : ZMod Q)) * k) := by
    simp only [pow_two, freq, sum_mul]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun b _ ↦ ?_
    simp only [← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring
  simp only [hp, pairCount, Complex.ofReal_sum]
  rw [sum_comm (s := univ) (t := A), mul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [sum_comm (s := univ) (t := A), mul_sum]
  refine sum_congr rfl fun b hb ↦ ?_
  simp only [char_ortho, sub_eq_zero, zmod_nat_eq ht (hA a ha b hb)]
  by_cases he : a + b = t
  · simp [he, show (Q : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne Q)]
  · simp [he, Ne.symm he]

private lemma parseval_freq (A : Finset ℕ) (hA : ∀ a ∈ A, a < Q) :
    ∑ k : ZMod Q, ‖freq A k‖ ^ 2 = (Q : ℝ) * A.card := by
  classical
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, cast_norm_sq]
  have hp (k : ZMod Q) : freq A k * conj (freq A k) =
      ∑ a ∈ A, ∑ b ∈ A, residueChar (((b : ZMod Q) - (a : ZMod Q)) * k) := by
    simp only [freq, map_sum, sum_mul]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [char_neg, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hp]
  rw [sum_comm (s := univ) (t := A)]
  trans ∑ _a ∈ A, (Q : ℂ)
  · refine sum_congr rfl fun a ha ↦ ?_
    rw [sum_comm (s := univ) (t := A)]
    have hval (b : ℕ) (hb : b ∈ A) :
        (∑ k : ZMod Q, residueChar (((b : ZMod Q) - (a : ZMod Q)) * k)) =
          if b = a then (Q : ℂ) else 0 := by
      simp only [char_ortho, sub_eq_zero, zmod_nat_eq (hA b hb) (hA a ha)]
    rw [sum_congr rfl hval]
    simp [ha]
  · simp [mul_comm]

private lemma mean_pair_inversion (A : Finset ℕ) {L : ℕ} (f : ℕ → ℕ)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a + b < Q) (hf : ∀ j < L, f j < Q) :
    (↑(realMean L (fun j ↦ pairCount A (f j))) : ℂ) = (Q : ℂ)⁻¹ *
      ∑ k : ZMod Q, freq A k ^ 2 * mean L (fun j ↦ phase (((k.val : ℝ) / Q) * f j)) := by
  rw [cast_realMean]
  trans mean L (fun j ↦ (Q : ℂ)⁻¹ *
    ∑ k : ZMod Q, freq A k ^ 2 * phase (((k.val : ℝ) / Q) * f j))
  · refine mean_congr fun j hj ↦ ?_
    rw [pair_inversion A (hf j hj) hA]
    simp only [char_freq_phase]
  rw [mean_mul, mean_sum]
  congr 1
  exact sum_congr rfl fun k _ ↦ mean_mul L _ _

private def atomicCount (W N : ℕ) (A : Finset ℕ) : ℝ :=
  realMean (2 * N) (fun j ↦ pairCount A (poly W (N + j)))

private def spreadCount (W N : ℕ) (A : Finset ℕ) : ℝ :=
  realMean (2 * N) (fun j ↦ realMean (gap W (N + j)) (fun k ↦ pairCount A (poly W (N + j) + k)))

private lemma count_comparison {W N : ℕ} (A : Finset ℕ)
    (hQ : poly W (3 * N) ≤ Q) (hA : ∀ a ∈ A, a < Q)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, a + b < Q) {ε : ℝ}
    (hε : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖atoms W N θ - spread W N θ‖ ≤ ε) :
    |atomicCount W N A - spreadCount W N A| ≤ ε * A.card := by
  classical
  have hat (j : ℕ) (hj : j < 2 * N) : poly W (N + j) < Q :=
    ((poly_strictMono W) (by omega : N + j < 3 * N)).trans_le hQ
  have hsp (j : ℕ) (hj : j < 2 * N) (k : ℕ) (hk : k < gap W (N + j)) :
      poly W (N + j) + k < Q := by
    apply lt_of_lt_of_le (Nat.add_lt_add_left hk _)
    rw [← poly_succ]
    exact ((poly_strictMono W).monotone (by omega : N + j + 1 ≤ 3 * N)).trans hQ
  have hAtom : (↑(atomicCount W N A) : ℂ) = (Q : ℂ)⁻¹ *
      ∑ k : ZMod Q, freq A k ^ 2 * atoms W N ((k.val : ℝ) / Q) :=
    mean_pair_inversion A _ hAA hat
  have hSpread : (↑(spreadCount W N A) : ℂ) = (Q : ℂ)⁻¹ *
      ∑ k : ZMod Q, freq A k ^ 2 * spread W N ((k.val : ℝ) / Q) := by
    rw [spreadCount, cast_realMean]
    trans mean (2 * N) (fun j ↦ (Q : ℂ)⁻¹ * ∑ k : ZMod Q, freq A k ^ 2 *
      mean (gap W (N + j)) (fun l ↦ phase (((k.val : ℝ) / Q) * (poly W (N + j) + l : ℕ))))
    · refine mean_congr fun j hj ↦ ?_
      exact mean_pair_inversion A _ hAA (hsp j hj)
    rw [mean_mul, mean_sum]
    congr 1
    exact sum_congr rfl fun k _ ↦ mean_mul (2 * N) _ _
  have hQp : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hθ (k : ZMod Q) : (k.val : ℝ) / (Q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one hQp).2 ?_⟩
    exact_mod_cast (ZMod.val_lt k).le
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, hAtom, hSpread,
    ← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Q : ℝ)⁻¹ * ∑ k : ZMod Q, ‖freq A k ^ 2 *
        (atoms W N ((k.val : ℝ) / Q) - spread W N ((k.val : ℝ) / Q))‖ := by
      simp only [mul_sub]
      gcongr
      exact norm_sum_le _ _
    _ ≤ (Q : ℝ)⁻¹ * ∑ k : ZMod Q, ‖freq A k‖ ^ 2 * ε := by
      gcongr with k
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hε _ (hθ k)) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, parseval_freq A hA]; field_simp

end Fourier

/-! ## From pair counts to a distinct monochromatic pair -/

private lemma sum_blocks {M : Type*} [AddCommMonoid M] (W N L : ℕ) (f : ℕ → M) :
    (∑ j ∈ range L, ∑ k ∈ range (gap W (N + j)), f (poly W (N + j) + k)) =
      ∑ t ∈ Ico (poly W N) (poly W (N + L)), f t := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih, ← Nat.add_assoc, ← sum_Ico_consecutive f
      ((poly_strictMono W).monotone (Nat.le_add_right N L))
      ((poly_strictMono W).monotone (Nat.le_succ (N + L))), sum_Ico_eq_sum_range f (poly W (N + L)),
      poly_succ, Nat.add_sub_cancel_left]

private lemma sum_pairCount (A : Finset ℕ) {a b : ℕ}
    (h : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ Ico a b) :
    (∑ t ∈ Ico a b, pairCount A t) = (A.card : ℝ) ^ 2 := by
  classical
  simp only [pairCount]
  rw [sum_comm (s := Ico a b) (t := A)]
  trans ∑ _x ∈ A, ∑ _y ∈ A, (1 : ℝ)
  · refine sum_congr rfl fun x hx ↦ ?_
    rw [sum_comm (s := Ico a b) (t := A)]
    refine sum_congr rfl fun y hy ↦ ?_
    simp [h x hx y hy]
  · simp [pow_two]

private lemma spread_count_lower {W N : ℕ} (hW : 0 < W) (hN : 0 < N) (A : Finset ℕ)
    (h : ∀ a ∈ A, ∀ b ∈ A, a + b ∈ Ico (poly W N) (poly W (3 * N))) :
    (A.card : ℝ) ^ 2 / (12 * W * (N : ℝ) ^ 2) ≤ spreadCount W N A := by
  let S (j : ℕ) := ∑ k ∈ range (gap W (N + j)), pairCount A (poly W (N + j) + k)
  have hh (j : ℕ) (hj : j ∈ range (2 * N)) : S j / (6 * (W : ℝ) * N) ≤
      realMean (gap W (N + j)) (fun k ↦ pairCount A (poly W (N + j) + k)) := by
    change S j / _ ≤ S j / _
    refine div_le_div_of_nonneg_left (sum_nonneg fun _ _ ↦ pairCount_nonneg _ _) ?_ ?_
    · exact_mod_cast gap_pos W (N + j)
    · exact_mod_cast gap_upper hW (mem_range.1 hj)
  have hS : (∑ j ∈ range (2 * N), S j) = (A.card : ℝ) ^ 2 := by
    dsimp [S]
    rw [sum_blocks, show N + 2 * N = 3 * N by omega]
    exact sum_pairCount A h
  unfold spreadCount realMean
  apply le_trans _ (div_le_div_of_nonneg_right (sum_le_sum (fun j hj ↦ hh j hj)) (by positivity))
  rw [← sum_div, hS, div_div]
  push_cast
  rw [show 6 * (W : ℝ) * N * (2 * N) = 12 * W * (N : ℝ) ^ 2 by ring]

private lemma pairCount_le_one_of_diag (A : Finset ℕ) (t : ℕ)
    (h : ∀ a ∈ A, ∀ b ∈ A, a + b = t → a = b) : pairCount A t ≤ 1 := by
  classical
  have hh : pairCount A t = ∑ a ∈ A, if a + a = t then (1 : ℝ) else 0 := by
    unfold pairCount
    refine sum_congr rfl fun a ha ↦ ?_
    calc
      _ = ∑ b ∈ A, if a = b then (if a + a = t then (1 : ℝ) else 0) else 0 := by
        refine sum_congr rfl fun b hb ↦ ?_
        by_cases he : a = b
        · subst b
          simp
        · have hne : a + b ≠ t := fun hs ↦ he (h a ha b hb hs)
          simp [he, hne]
      _ = _ := by simp [ha]
  rw [hh]
  by_cases hr : ∃ a ∈ A, a + a = t
  · obtain ⟨a, ha, hat⟩ := hr
    rw [sum_eq_single_of_mem a ha]
    · simp [hat]
    · intro b _ hba
      have hne : b + b ≠ t := by omega
      simp [hne]
  · push Not at hr
    have hz : ∑ a ∈ A, (if a + a = t then (1 : ℝ) else 0) = 0 :=
      sum_eq_zero fun a ha ↦ ite_eq_right (hr a ha)
    rw [hz]
    norm_num

private lemma atomic_count_le_one {W N : ℕ} (A : Finset ℕ)
    (h : ∀ j < 2 * N, ∀ a ∈ A, ∀ b ∈ A, a + b = poly W (N + j) → a = b) :
    atomicCount W N A ≤ 1 := by
  have hS : ∑ j ∈ range (2 * N), pairCount A (poly W (N + j)) ≤ ((2 * N : ℕ) : ℝ) := by
    simpa using sum_le_sum (s := range (2 * N)) (g := fun _ ↦ (1 : ℝ))
      (fun j hj ↦ pairCount_le_one_of_diag A _ (h j (mem_range.1 hj)))
  by_cases hN : N = 0
  · simp [atomicCount, realMean, hN]
  · exact (div_le_iff₀ (by positivity)).2 (by simpa using hS)

private lemma large_fiber {r D : ℕ} (f : ℕ → Fin r) :
    ∃ i : Fin r, D ≤ r * ((Ico D (2 * D)).filter (fun x ↦ f x = i)).card := by
  classical
  let I := Ico D (2 * D)
  have hcard : I.card = D := by simp [I, two_mul]
  have hsum : (∑ i : Fin r, (I.filter (fun x ↦ f x = i)).card) = D := by
    simpa [hcard] using
      (sum_fiberwise I f (fun _ ↦ (1 : ℕ)))
  by_contra! hn
  have hstrict : ∑ i : Fin r, r * (I.filter (fun x ↦ f x = i)).card < ∑ _ : Fin r, D := by
    have : Nonempty (Fin r) := ⟨f 0⟩
    exact sum_lt_sum_of_nonempty univ_nonempty (fun i _ ↦ hn i)
  rw [← mul_sum, hsum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hstrict
  exact (lt_irrefl _ hstrict)

private lemma poly_three_large {W N : ℕ} (hW : 0 < W) (hN : 0 < N) :
    4 * poly W N < poly W (3 * N) := by
  have h : N ≤ W * N ^ 2 := by
    calc
      N ≤ N ^ 2 := by nlinarith
      _ ≤ W * N ^ 2 := by simpa using Nat.mul_le_mul_right (N ^ 2) hW
  unfold poly
  nlinarith

private lemma same_color_poly_pair {r : ℕ} (c : ℕ → Fin r) :
    ∃ W a b n : ℕ, 0 < W ∧ a ≠ b ∧ c (2 + 16 * W * a) = c (2 + 16 * W * b) ∧
      a + b = poly W n := by
  classical
  have hr : 0 < r := Nat.zero_lt_of_lt (c 0).isLt
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let ε : ℝ := 1 / (24 * r)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (max 2 (2 / ε ^ 2))
  have hK₂ : 2 ≤ K := by exact_mod_cast ((le_max_left _ _).trans hK.le : (2 : ℝ) ≤ K)
  have hscale : 2 / (K : ℝ) < ε ^ 2 := by
    have hpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    apply (div_lt_iff₀ hpos).2
    have hh := (div_lt_iff₀ (sq_pos_of_pos hε)).1 ((le_max_right _ _).trans_lt hK)
    linarith
  obtain ⟨N, hlarge, hdiscrep⟩ := ((eventually_gt_atTop (24 * r * r)).and
    (uniform_discrepancy hK₂ hε hscale)).exists
  let W := K.factorial
  have hW : 0 < W := Nat.factorial_pos _
  have hN : 0 < N := by omega
  let D := poly W N
  let f (a : ℕ) := c (2 + 16 * W * a)
  obtain ⟨i, hi⟩ := large_fiber (D := D) f
  let A := (Ico D (2 * D)).filter (fun a ↦ f a = i)
  have hmem (a : ℕ) (ha : a ∈ A) : (D ≤ a ∧ a < 2 * D) ∧ f a = i := by
    simpa only [A, mem_filter, mem_Ico] using ha
  have hD : N ≤ D := by simp [D, poly]
  have hsize : 24 * r < A.card := by
    by_contra! h
    have hh := Nat.mul_le_mul_left r h
    rw [mul_comm r (24 * r)] at hh
    exact (not_le_of_gt hlarge) (hD.trans (hi.trans hh))
  have hsmall (a : ℕ) (ha : a ∈ A) : a < poly W (3 * N) := by
    have hh := (hmem a ha).1.2
    have hp := poly_three_large hW hN
    change a < 2 * poly W N at hh
    omega
  have hsum (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ A) :
      a + b ∈ Ico D (poly W (3 * N)) := by
    have ha' := (hmem a ha).1
    have hb' := (hmem b hb).1
    have hp : 4 * D < poly W (3 * N) := poly_three_large hW hN
    exact mem_Ico.2 ⟨by omega, by omega⟩
  let Q := poly W (3 * N) + 1
  have : NeZero Q := ⟨by dsimp [Q]; omega⟩
  have hcomp := count_comparison (Q := Q) A (Nat.le_succ (poly W (3 * N)))
    (fun a ha ↦ (hsmall a ha).trans (Nat.lt_succ_self _))
    (fun a ha b hb ↦ (mem_Ico.1 (hsum a ha b hb)).2.trans (Nat.lt_succ_self _))
    (fun θ hθ ↦ (hdiscrep θ hθ).le)
  have hlo := spread_count_lower hW hN A hsum
  have hA'' : (W : ℝ) * (N : ℝ) ^ 2 ≤ r * (A.card : ℝ) := by
    exact_mod_cast (show W * N ^ 2 ≤ D by simp [D, poly]).trans hi
  have hlower : (A.card : ℝ) / (12 * r) ≤ (A.card : ℝ) ^ 2 / (12 * W * (N : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hA'' (show (0 : ℝ) ≤ 12 * A.card by positivity)
    linarith only [show (A.card : ℝ) * (12 * (W : ℝ) * (N : ℝ) ^ 2) ≤
      (A.card : ℝ) ^ 2 * (12 * r) by linear_combination hh]
  have hgt : (1 : ℝ) < (A.card : ℝ) / (24 * r) := by
    apply (lt_div_iff₀ (by positivity)).2
    simp only [one_mul]
    exact_mod_cast hsize
  have heq : (A.card : ℝ) / (12 * r) - ε * A.card = (A.card : ℝ) / (24 * r) := by
    dsimp [ε]
    field_simp
    ring
  have hc : 1 < atomicCount W N A := by
    have hAbs := (abs_le.1 hcomp).1
    linarith [hlower.trans hlo]
  have hex : ∃ j < 2 * N, ∃ a ∈ A, ∃ b ∈ A, a + b = poly W (N + j) ∧ a ≠ b := by
    by_contra! hno
    exact (not_le_of_gt hc) (atomic_count_le_one A hno)
  obtain ⟨j, _, a, ha, b, hb, hab, hne⟩ := hex
  exact ⟨W, a, b, N + j, hW, hne, (hmem a ha).2.trans (hmem b hb).2.symm, hab⟩

private lemma square_witnesses {r : ℕ} (c : ℕ → Fin r) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ IsSquare (x + y) := by
  obtain ⟨W, a, b, n, hW, hab, hcol, hsum⟩ := same_color_poly_pair c
  refine ⟨2 + 16 * W * a, 2 + 16 * W * b, by positivity, by positivity, ?_, hcol,
    ⟨2 + 4 * W * n, ?_⟩⟩
  · intro h
    apply hab
    exact Nat.eq_of_mul_eq_mul_left (show 0 < 16 * W by positivity) (Nat.add_left_cancel h)
  calc
    _ = 4 + 16 * W * (a + b) := by ring
    _ = (2 + 4 * W * n) * (2 + 4 * W * n) := by rw [hsum]; unfold poly; ring

end

@[expose] public section

/-- **Erdős Problem 439 for squares.** The statement that for every colouring of the positive
integers with finitely many colours there are distinct positive integers $x$ and $y$ of the same
colour such that $x + y$ is a perfect square. -/
def monochromaticSquareSum : Prop :=
  ∀ r : ℕ, ∀ c : ℕ → Fin r, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ IsSquare (x + y)

/--
**Erdős Problem 439 for squares is true.** For every colouring of the positive integers with
finitely many colours there are distinct positive integers $x$ and $y$ of the same colour such
that $x + y$ is a perfect square.

This is the case $f(z) = z^2$ of a theorem of Khalfalah and Szemerédi on monochromatic
solutions of $x + y = f(z)$; Erdős, Sárközy and Sós had proved the cases of $2$ and $3$ colours.

Source: T. F. Bloom, Erdős Problems, Problem #439,
https://www.erdosproblems.com/439 (status PROVED); resolution: A. Khalfalah and E. Szemerédi, On the
number of monochromatic solutions of x + y = z², Combin. Probab. Comput. (2006), 213-227, main
theorem (a conjecture of Erdős, Roth, Sárközy and Sós): for every nonconstant f ∈ ℤ[z] with 2 ∣ f(z)
for some z ∈ ℤ, every finite colouring of the integers has x ≠ y of the same colour with x + y =
f(z) (abstract; erdosproblems.com/439), https://doi.org/10.1017/S0963548305007169.
-/
public theorem monochromaticSquareSum_holds : monochromaticSquareSum := by
  intro r c
  exact square_witnesses c

end

end MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted
