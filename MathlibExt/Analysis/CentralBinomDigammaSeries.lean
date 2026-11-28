/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Data.Nat.Choose.Central
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Series from Nörlund's digamma identity

This module evaluates a central binomial series for complex $h$ with $\operatorname{Re} h > -1/2$
and $h$ not a nonnegative integer. It also evaluates the product series for $\pi \cot(\pi/k)$
for integers $k \ge 2$. Both results use Nörlund's expansion of a digamma difference.

## References

* Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of Nörlund*,
  INTEGERS 25 (2025), Article A18, pp. 1–12, Theorems 1 and 8 (identity (19) in Theorem 8).
  <https://math.colgate.edu/~integers/z18/z18.pdf>
* Einar Hille, *On the Logarithmic Derivatives of the Gamma Function*,
  Mathematisk-fysiske Meddelelser 8 (1927), no. 1, 58 pp., §2, p. 6, equation (22).
  This is identity (2) in Adegoke and Frontczak; Hille cites N. E. Nörlund,
  *Vorlesungen über Differenzenrechnung*, Springer (1924), p. 251.
-/

open Filter Finset Topology

namespace MetaMathlibExt

namespace CentralBinomDigammaSeries

private def rising {K : Type*} [Field K] (a : K) (n : ℕ) : K :=
  ∏ j ∈ range n, (a + j)

private lemma rising_succ {K : Type*} [Field K] (a : K) (n : ℕ) :
    rising a (n + 1) = rising a n * (a + n) := prod_range_succ _ _

private lemma rising_shift (w : ℝ) (n : ℕ) :
    rising w (n + 1) = rising (w + 1) n * w := by
  simp only [rising, prod_range_succ', Nat.cast_succ, Nat.cast_zero, add_zero]
  congr 1
  exact prod_congr rfl fun j _ ↦ by ring

private lemma rising_pos {w : ℝ} (hw : 0 < w) (n : ℕ) : 0 < rising w n :=
  prod_pos fun _ _ ↦ by positivity

private lemma rising_cast (w : ℝ) (n : ℕ) : ((rising w n : ℝ) : ℂ) = rising (w : ℂ) n := by
  simp [rising]

private noncomputable def ratio (a : ℂ) (w : ℝ) (n : ℕ) : ℂ := rising a n / rising w n

-- Euler's limit for Gamma controls the growth of the rising-factorial ratio.
private lemma ratio_bound {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ‖ratio a w (n + 1)‖ ≤ C * (n : ℝ) ^ (a.re - w) := by
  have hlim := (Complex.GammaSeq_tendsto_Gamma w).div (Complex.GammaSeq_tendsto_Gamma a)
    (Complex.Gamma_ne_zero ha)
  refine ⟨‖Complex.Gamma w / Complex.Gamma a‖ + 1, ?_⟩
  filter_upwards [hlim.norm.eventually (Iio_mem_nhds (lt_add_one _)), eventually_gt_atTop 0]
    with n hC hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : rising a (n + 1) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ ↦ fun e ↦ ha j (eq_neg_of_add_eq_zero_left e)
  have heq : ratio a w (n + 1) =
      Complex.GammaSeq w n / Complex.GammaSeq a n * (n : ℂ) ^ (a - w) := by
    rw [Complex.cpow_sub _ _ hn', Complex.GammaSeq, Complex.GammaSeq, ratio, rising_cast]
    have hw' : rising (w : ℂ) (n + 1) ≠ 0 := by
      rw [← rising_cast]; exact_mod_cast (rising_pos hw _).ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    unfold rising at hp hw' ⊢
    field_simp [hp, hw', hf, Complex.cpow_eq_zero_iff, hn']
  rw [heq, norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.sub_re, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (le_of_lt hC) (by positivity)

private lemma ratio_tendsto {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {w : ℝ}
    (hw : 0 < w) (haw : a.re < w) :
    Tendsto (fun n ↦ ratio a w (n + 1)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := ratio_bound ha hw
  apply squeeze_zero_norm' hC
  simpa [neg_sub] using tendsto_const_nhds (x := C) |>.mul
    ((tendsto_rpow_neg_atTop (sub_pos.mpr haw)).comp tendsto_natCast_atTop_atTop)

private lemma summable_ratio {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {w : ℝ}
    (hw : 0 < w) (haw : a.re < w) :
    Summable (fun n : ℕ ↦ ratio a w (n + 1) / ((n : ℂ) + 1)) := by
  obtain ⟨C, hC⟩ := ratio_bound ha hw
  have hs := (Real.summable_nat_rpow.mpr (show a.re - w - 1 < -1 by linarith)).mul_left C
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hC, eventually_gt_atTop 0] with n h hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [norm_div, show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ‖ratio a w (n + 1)‖ / n :=
      div_le_div_of_nonneg_left (norm_nonneg _) hn' (by linarith)
    _ ≤ (C * (n : ℝ) ^ (a.re - w)) / n := by gcongr
    _ = _ := by rw [Real.rpow_sub hn' (a.re - w) 1, Real.rpow_one, mul_div_assoc]

-- Summing down a column telescopes the reciprocal rising factorials.
private lemma column {w : ℝ} (hw : 0 < w) (n : ℕ) :
    HasSum (fun k : ℕ ↦ (rising (w + k) (n + 2))⁻¹)
      ((rising w (n + 1))⁻¹ / (n + 1 : ℝ)) := by
  let f (k : ℕ) := (rising (w + k) (n + 1))⁻¹ / ((n : ℝ) + 1)
  have hstep (k : ℕ) : (rising (w + k) (n + 2))⁻¹ = f k - f (k + 1) := by
    have hx : 0 < w + k := by positivity
    have h := rising_shift (w + k) (n + 1)
    rw [rising_succ] at h
    dsimp [f]
    push_cast
    rw [← add_assoc, rising_succ]
    have hx' : 0 < w + k + 1 := by positivity
    field_simp [ne_of_gt (rising_pos hx _), ne_of_gt (rising_pos hx' _)]
    push_cast at h ⊢
    nlinarith only [h]
  have hzero : Tendsto f atTop (𝓝 0) := by
    have h (j : ℕ) : Tendsto (fun k : ℕ ↦ (w + k + j)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp <|
        (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
    simpa [f, rising, prod_inv_distrib] using
      (tendsto_finsetProd (range (n + 1)) (fun j _ ↦ h j)).div_const (n + 1 : ℝ)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ inv_nonneg.mpr (rising_pos (by positivity) _).le)
    _).mpr
  simp_rw [hstep, sum_range_sub' f]
  simpa [f] using (tendsto_const_nhds (x := f 0)).sub hzero

private noncomputable def term (a : ℂ) (w : ℝ) (n : ℕ) : ℂ :=
  rising a (n + 1) / rising w (n + 2)

private lemma column_sum (a : ℂ) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    HasSum (fun k : ℕ ↦ term a (w + k) n) (ratio a w (n + 1) / ((n : ℂ) + 1)) := by
  simpa [term, ratio, div_eq_mul_inv, mul_assoc] using
    (Complex.hasSum_ofReal.mpr (column hw n)).mul_left (rising a (n + 1))

private lemma column_norm (a : ℂ) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    HasSum (fun k : ℕ ↦ ‖term a (w + k) n‖) ‖ratio a w (n + 1) / ((n : ℂ) + 1)‖ := by
  have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
  have hpos (k : ℕ) := (rising_pos (show 0 < w + k by positivity) (n + 2)).le
  simp only [term, ratio, norm_div, hn, Complex.norm_real, Real.norm_of_nonneg (rising_pos hw _).le,
    Real.norm_of_nonneg (hpos _)]
  simpa only [div_eq_mul_inv, mul_assoc] using
    (column hw n).mul_left ‖rising a (n + 1)‖

-- Across a row the difference of successive ratios has the constant factor w - a.
private lemma row_sum {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {w : ℝ} (hw : 0 < w)
    (haw : a.re < w) (hs : Summable (term a w)) :
    HasSum (term a w) (1 / ((w : ℂ) - a) - 1 / w) := by
  have hwa : (w : ℂ) - a ≠ 0 := sub_ne_zero.mpr fun h ↦ haw.ne (congrArg Complex.re h.symm)
  have hstep (n : ℕ) : term a w n =
      ratio a w (n + 1) / (w - a) - ratio a w (n + 2) / (w - a) := by
    simp only [ratio, term, rising_succ _ (n + 1), Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_natCast]
    have hpos : ((rising w (n + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (rising_pos hw _).ne'
    have hne : (w : ℂ) + (n + 1 : ℕ) ≠ 0 := by
      exact_mod_cast (show (0 : ℝ) < w + (n + 1 : ℕ) by positivity).ne'
    field_simp [hwa, hpos, hne]
    ring
  apply hs.hasSum_iff_tendsto_nat.mpr
  simp_rw [hstep, sum_range_sub' (fun n ↦ ratio a w (n + 1) / (w - a))]
  have hl := (tendsto_const_nhds (x := ratio a w 1 / (w - a))).sub
    ((ratio_tendsto ha hw haw).div_const ((w : ℂ) - a))
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  convert hl using 2
  simp [ratio, rising]
  field_simp [hwa, hw']
  ring

private lemma digamma_gap {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasSum (fun k : ℕ ↦ 1 / (u + k) - 1 / (v + k)) (Complex.digamma v - Complex.digamma u) := by
  have hp {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s ≠ -m := by
    intro h
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hs := (Complex.hasSum_digamma_series (v + 1) (by simp; linarith)).sub
    (Complex.hasSum_digamma_series (u + 1) (by simp; linarith))
  rw [Complex.digamma_apply_add_one _ (hp hv), Complex.digamma_apply_add_one _ (hp hu)] at hs
  rw [← hasSum_nat_add_iff' 1]
  convert hs.congr_fun (g := fun k : ℕ ↦ 1 / (u + (k + 1 : ℕ)) - 1 / (v + (k + 1 : ℕ)))
    (fun k ↦ by unfold Complex.digammaSeriesTerm; push_cast; ring_nf) using 1
  simp only [sum_range_one, Nat.cast_zero, add_zero, one_div]
  ring

private lemma norlund {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) {w : ℝ} (hw : 0 < w) (haw : a.re < w) :
    ∑' n : ℕ, ratio a w (n + 1) / ((n : ℂ) + 1) =
      Complex.digamma w - Complex.digamma (w - a) := by
  have hnorm : Summable (fun p : ℕ × ℕ ↦ ‖term a (w + p.2) p.1‖) := by
    apply (summable_prod_of_nonneg fun _ ↦ norm_nonneg _).mpr
    refine ⟨fun n ↦ (column_norm a hw n).summable, ?_⟩
    simpa only [(column_norm a hw _).tsum_eq] using (summable_ratio ha hw haw).norm
  have hs := hnorm.of_norm
  have hrow (k : ℕ) := row_sum (a := a) (w := w + k) ha (by positivity)
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (hs.prod_symm.prod_factor k)
  have h := Summable.tsum_comm (f := fun n k : ℕ ↦ term a (w + k) n) hs
  simp_rw [(column_sum a hw _).tsum_eq, (hrow _).tsum_eq] at h
  rw [← h]
  convert (digamma_gap (u := w - a) (v := w) (by simpa using sub_pos.mpr haw) hw).tsum_eq using 2
  funext k
  push_cast
  ring_nf

private lemma rising_half (n : ℕ) :
    rising (1 / 2 : ℝ) n * 4 ^ n = n.factorial * (n.centralBinom : ℝ) := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    have h : ((n : ℝ) + 1) * (n + 1).centralBinom =
        2 * (2 * (n : ℝ) + 1) * n.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [rising_succ, pow_succ, Nat.factorial_succ]
    push_cast
    linear_combination 2 * (2 * (n : ℝ) + 1) * ih - (n.factorial : ℝ) * h

private lemma gamma_shift {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (n : ℕ) :
    Complex.Gamma (a + n) = rising a n * Complex.Gamma a := by
  have hp : rising a n = (ascPochhammer ℂ n).eval a := by
    induction n with
    | zero => simp [rising]
    | succ n ih => rw [rising_succ, ascPochhammer_succ_eval, ih]
  rw [hp, ← Complex.Gamma_add_nat_div_Gamma_eq a ha,
    div_mul_cancel₀ _ (Complex.Gamma_ne_zero ha)]

private lemma binom_term {h : ℂ} (ha : ∀ k : ℕ, -h ≠ -k) (n : ℕ) :
    (4 : ℂ) ^ n * (Complex.Gamma (h + 1) * Complex.Gamma (n - h + 1) / n.factorial) /
        (((n + 1).centralBinom : ℂ) * ((n : ℂ) + 1) ^ 2) =
      Complex.Gamma (h + 1) * Complex.Gamma (-h) / 4 *
        (ratio (-h) (1 / 2) (n + 1) / ((n : ℂ) + 1)) := by
  have hr := (eq_div_iff (show (4 : ℝ) ^ (n + 1) ≠ 0 by positivity)).mpr (rising_half (n + 1))
  rw [show (n : ℂ) - h + 1 = -h + (n + 1 : ℕ) by push_cast; ring, gamma_shift ha, ratio, hr]
  push_cast [Nat.factorial_succ, pow_succ]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc : ((n + 1).centralBinom : ℂ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero _
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp [hn, hc, hf]

end CentralBinomDigammaSeries

open CentralBinomDigammaSeries

/-- **Digamma evaluation of a central binomial series with a complex binomial parameter.** Let
$\Gamma$ be the Gamma function and $\psi$ the digamma function, and let $h$ be a complex number
that is not a nonnegative integer and has $\operatorname{Re} h > -1/2$. Writing $\binom{n}{h}^{-1}$
for $\Gamma(h+1)\,\Gamma(n-h+1)/n!$, we have
$$\sum_{n=0}^{\infty} \frac{4^n}{\binom{n}{h} \binom{2(n+1)}{n+1} (n+1)^2} =
\frac{\pi}{4} \cdot \frac{\psi(h + \tfrac12) - \psi(\tfrac12)}{\sin(\pi h)}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identity (19)
(`integers-2025-A18-thm-8`). -/
public theorem tsum_four_pow_div_binom_mul_centralBinom_mul_sq {h : ℂ}
    (hh : ∀ m : ℕ, h ≠ m) (hre : -1 / 2 < h.re) :
    ∑' n : ℕ, (4 : ℂ) ^ n * (Complex.Gamma (h + 1) * Complex.Gamma (n - h + 1) / n.factorial) /
        (((n + 1).centralBinom : ℂ) * ((n : ℂ) + 1) ^ 2) =
      Real.pi / 4 * (Complex.digamma (h + 1 / 2) - Complex.digamma (1 / 2)) /
        Complex.sin (Real.pi * h) := by
  have ha (m : ℕ) : -h ≠ -m := fun e ↦ hh m (neg_inj.mp e)
  have hs := norlund (w := 1 / 2) ha (by norm_num) (by simp; linarith)
  have href := Complex.Gamma_mul_Gamma_one_sub (-h)
  rw [sub_neg_eq_add, add_comm 1 h, mul_neg, Complex.sin_neg, div_neg] at href
  simp_rw [binom_term ha]
  rw [tsum_mul_left, hs, mul_comm (Complex.Gamma (h + 1)), href]
  push_cast
  rw [sub_neg_eq_add, add_comm (1 / 2 : ℂ) h]
  ring

/-- **A product series for $\pi \cot(\pi/k)$.** For every integer $k \ge 2$,
$$(k - 2)\Bigl(1 + \sum_{n=1}^{\infty} \frac{1}{n + 1}
\prod_{j=1}^{n} \frac{kj - (k - 2)}{kj + 1}\Bigr) = \pi \cot\frac{\pi}{k}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 1 (`integers-2025-A18-thm-1`). -/
public theorem sub_two_mul_one_add_tsum_prod_eq_pi_mul_cot {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) - 2) * (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) *
        ∏ j ∈ Finset.Icc 1 (n + 1), ((k : ℝ) * j - (k - 2)) / (k * j + 1)) =
      Real.pi * Real.cot (Real.pi / k) := by
  by_cases he : k = 2
  · subst k
    norm_num [Real.cot_eq_cos_div_sin, Real.cos_pi_div_two]
  have hk₂ : (2 : ℝ) < k := by exact_mod_cast (lt_of_le_of_ne hk (Ne.symm he))
  have hk₀ : (0 : ℝ) < k := by linarith
  let w : ℝ := 1 / k
  let a : ℝ := 2 * w - 1
  have hw : 0 < w := one_div_pos.mpr hk₀
  have hw₂ : w < 1 / 2 := (div_lt_iff₀ hk₀).mpr (by linarith)
  have ha₀ : a < 0 := by dsimp [a]; linarith
  have ha₁ : -1 < a := by dsimp [a]; linarith
  have ha (m : ℕ) : (a : ℂ) ≠ -m := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hm₀ : (0 : ℝ) < m := by linarith
    have hm₁ : (m : ℝ) < 1 := by linarith
    exact (not_lt_of_ge (Nat.succ_le_of_lt (by exact_mod_cast hm₀))) (by exact_mod_cast hm₁)
  have haw : (a : ℂ).re < w := Complex.ofReal_re a ▸ ha₀.trans hw
  have hwint (m : ℤ) : (w : ℂ) ≠ m := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.intCast_re] at hr
    have hm₀ : (0 : ℤ) < m := by exact_mod_cast (hr ▸ hw)
    have hm₁ : m < (1 : ℤ) := by exact_mod_cast (hr ▸ (show w < 1 by linarith))
    omega
  have harg : (w : ℂ) - (a : ℂ) = 1 - (w : ℂ) := by
    simp only [a, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  let f (n : ℕ) : ℝ :=
    1 / ((n : ℝ) + 1) * ∏ j ∈ Icc 1 n, ((k : ℝ) * j - (k - 2)) / (k * j + 1)
  -- Scaling numerator and denominator by k writes each rising-factorial factor as in the paper.
  have hfactor (j : ℕ) : (a + j) / (w + j) =
      ((k : ℝ) * j - (k - 2)) / (k * j + 1) := by
    rw [← mul_div_mul_left _ _ hk₀.ne']
    congr 1 <;> dsimp [a, w] <;> field_simp <;> ring
  have hratio (n : ℕ) : rising a (n + 1) / rising w (n + 1) =
      (2 - (k : ℝ)) * (∏ j ∈ Icc 1 n, ((k : ℝ) * j - (k - 2)) / (k * j + 1)) := by
    rw [← show Ico 1 (n + 1) = Icc 1 n from Ico_succ_right_eq_Icc 1 n,
      prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    simp only [rising, prod_range_succ', Nat.cast_zero, add_zero, mul_div_mul_comm,
      ← prod_div_distrib, hfactor, add_comm 1]
    rw [show a / w = 2 - (k : ℝ) by dsimp [a, w]; field_simp]
    exact mul_comm _ _
  have hterm (n : ℕ) : ratio (a : ℂ) w (n + 1) / ((n : ℂ) + 1) =
      (2 - (k : ℂ)) * (f n : ℂ) := by
    have hreal : ratio (a : ℂ) w (n + 1) / ((n : ℂ) + 1) =
        (↑(rising a (n + 1) / rising w (n + 1) / ((n : ℝ) + 1)) : ℂ) := by
      simp only [Complex.ofReal_div, rising_cast a, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one, ratio]
    rw [hreal, hratio]
    simp only [f, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hf₀ : f 0 = 1 := by simp [f]
  -- Split off n = 0 before applying the reflection formula to the digamma difference.
  have hsum := (summable_ratio ha hw haw).tsum_eq_zero_add
  rw [norlund ha hw haw, harg, Complex.digamma_one_sub hwint] at hsum
  simp_rw [hterm] at hsum
  rw [tsum_mul_left, hf₀, Complex.ofReal_one] at hsum
  have hshift (n : ℕ) : f (n + 1) = 1 / ((n : ℝ) + 2) *
      ∏ j ∈ Icc 1 (n + 1), ((k : ℝ) * j - (k - 2)) / (k * j + 1) := by
    simp only [f, Nat.cast_succ, add_assoc, one_add_one_eq_two]
  simp_rw [← hshift]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_tsum, Complex.ofReal_cot,
    Complex.ofReal_div]
  rw [show (Real.pi : ℂ) / k = (Real.pi : ℂ) * (w : ℂ) by simp [w, div_eq_mul_inv]]
  linear_combination hsum

end MetaMathlibExt
