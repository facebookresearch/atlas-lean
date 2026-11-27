/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelSequence
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Decay of the Göbel error term

The error between the exponential of the logarithmic series and the powered ratio of normalized
Göbel roots decays faster than any inverse power of the index.
-/

namespace MetaMathlibExt

open Filter Topology Asymptotics

namespace gobelSequence_error_isBigO

private theorem real_recurrence (k l n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * (gobelSequence k l (n + 1) : ℝ) =
      (gobelSequence k l n : ℝ) * ((n : ℝ) + (gobelSequence k l n : ℝ) ^ (k - 1)) := by
  exact_mod_cast gobelSequence_succ k l n hn

-- The lower bound by `n + 1` makes the recurrence grow by a factor of at least `3 / 2`.
private theorem growth {k l n : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hn : 1 ≤ n) :
    (n : ℝ) + 1 ≤ (gobelSequence k l n : ℝ) ∧
      (3 / 2 : ℝ) ^ n ≤ (gobelSequence k l n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [gobelSequence_one]
    have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
    norm_num
    constructor <;> linarith
  | succ n hn ih =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hg : 1 ≤ (gobelSequence k l n : ℝ) := by linarith [ih.1]
    have hp := le_self_pow₀ hg (show k - 1 ≠ 0 by omega)
    have hstep : (3 / 2 : ℝ) * (gobelSequence k l n : ℝ) ≤ gobelSequence k l (n + 1) := by
      apply (mul_le_mul_iff_right₀ (show 0 < (n : ℝ) + 1 by positivity)).mp
      rw [real_recurrence k l n hn]
      calc
        _ = (gobelSequence k l n : ℝ) * ((3 / 2) * ((n : ℝ) + 1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [ih.1]) (zero_le_one.trans hg)
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_succ]
      calc
        _ ≤ (3 / 2 : ℝ) * ((n : ℝ) + 1) := by linarith
        _ ≤ _ := (mul_le_mul_of_nonneg_left ih.1 (by norm_num)).trans hstep
    · rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left ih.2 (by norm_num)).trans hstep

private noncomputable def root (k l n : ℕ) : ℝ :=
  (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)

private noncomputable def weight (k m : ℕ) : ℝ := ((k : ℝ) ^ (m + 1))⁻¹

private noncomputable def logTerm (k n m : ℕ) : ℝ :=
  weight k m * Real.log ((m + 1 : ℝ) + n)

private noncomputable def correction (k l n : ℕ) : ℝ :=
  Real.log (1 + (n : ℝ) / (gobelSequence k l n : ℝ) ^ (k - 1))

private theorem summable_weights {k : ℕ} (hk : 2 ≤ k) :
    Summable (weight k) ∧ (∑' m, weight k m) ≤ 1 ∧
      Summable (fun m : ℕ => weight k m * (m + 1 : ℝ)) := by
  let r : ℝ := (k : ℝ)⁻¹
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 ≤ r := by positivity
  have hrhalf : r ≤ 1 / 2 := by
    simpa only [r, one_div] using (inv_le_inv₀ (by linarith : 0 < (k : ℝ))
      (by norm_num : 0 < (2 : ℝ))).mpr hk'
  have hr' : r < 1 := by linarith
  have hw (m : ℕ) : weight k m = r * r ^ m := by
    rw [weight, ← inv_pow, pow_succ']
  have hgeom := summable_geometric_of_lt_one hr hr'
  have hwSum := (hgeom.mul_left r).congr fun m => (hw m).symm
  refine ⟨hwSum, ?_, ?_⟩
  · simp_rw [hw]
    rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hr hr', ← div_eq_mul_inv,
      div_le_iff₀ (sub_pos.mpr hr')]
    linarith
  · have hm := (hasSum_coe_mul_geometric_of_norm_lt_one
      (by rwa [Real.norm_of_nonneg hr] : ‖r‖ < 1)).summable
    refine ((hgeom.add hm).mul_left r).congr fun m => ?_
    rw [hw]
    ring

private theorem logTerm_le {k n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    logTerm k n m ≤ Real.log n * weight k m + weight k m * (m + 1 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by positivity
  have hlog : Real.log ((m + 1 : ℝ) + n) ≤ Real.log n + (m + 1 : ℝ) := by
    have heq : (m + 1 : ℝ) + n = n * (1 + (m + 1 : ℝ) / n) := by
      field_simp
      ring
    rw [heq, Real.log_mul hn₀.ne' (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (m + 1 : ℝ) / n by positivity)
    have hdiv : (m + 1 : ℝ) / n ≤ m + 1 := div_le_self (by positivity) hn'
    linarith
  calc
    _ ≤ weight k m * (Real.log n + (m + 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by unfold weight; positivity)
    _ = _ := by ring

private theorem correction_bounds {k l n : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hn : 1 ≤ n)
    (m : ℕ) :
    0 ≤ correction k l (m + n) ∧
      correction k l (m + n) ≤ ((n : ℝ) * (2 / 3 : ℝ) ^ n) * (m + 1 : ℝ) := by
  have hg := growth hk hl (show 1 ≤ m + n by omega)
  have hg' : 1 ≤ (gobelSequence k l (m + n) : ℝ) := by
    linarith [hg.1, Nat.cast_nonneg (α := ℝ) (m + n)]
  have hpow : (3 / 2 : ℝ) ^ n ≤ (gobelSequence k l (m + n) : ℝ) ^ (k - 1) :=
    (pow_le_pow_right₀ (by norm_num) (show n ≤ m + n by omega)).trans
      (hg.2.trans (le_self_pow₀ hg' (by omega)))
  have hfrac : 0 ≤ ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1) :=
    div_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hg') _)
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  unfold correction
  calc
    _ ≤ ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1) := by
      simpa only [add_sub_cancel_left] using
        (Real.log_le_sub_one_of_pos (by linarith : 0 <
          1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1)))
    _ ≤ ((m + n : ℕ) : ℝ) / (3 / 2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ ≤ _ := by
      have hmn : ((m + n : ℕ) : ℝ) ≤ (n : ℝ) * (m + 1 : ℝ) := by
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.mpr hn') (Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
      have hrat : ((3 / 2 : ℝ) ^ n)⁻¹ = (2 / 3 : ℝ) ^ n := by rw [← inv_pow]; norm_num
      rw [div_eq_mul_inv, hrat, mul_right_comm]
      gcongr

private theorem log_root_step {k l n : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) (hn : 1 ≤ n) :
    Real.log (root k l n) - Real.log (root k l (n + 1)) =
      (Real.log ((n : ℝ) + 1) - correction k l n) / (k : ℝ) ^ (n + 1) := by
  let g (i : ℕ) := (gobelSequence k l i : ℝ)
  have hg : 0 < g n := by
    exact (show (0 : ℝ) < (n : ℝ) + 1 by positivity).trans_le (growth hk hl hn).1
  have hf : 0 < 1 + (n : ℝ) / g n ^ (k - 1) := by positivity
  have hrec : g (n + 1) = g n ^ k * (1 + (n : ℝ) / g n ^ (k - 1)) / ((n : ℝ) + 1) := by
    apply (eq_div_iff (show (n : ℝ) + 1 ≠ 0 by positivity)).mpr
    rw [mul_comm (g (n + 1)), real_recurrence k l n hn]
    change g n * ((n : ℝ) + g n ^ (k - 1)) = g n ^ k * _
    have hpow : g n ^ k = g n ^ (k - 1) * g n := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega), pow_succ]
    rw [hpow]
    field_simp
    ring
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  change Real.log (g n ^ _) - Real.log (g (n + 1) ^ _) = _
  rw [hrec, Real.log_rpow hg, Real.log_rpow (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hf.ne',
    Real.log_pow, correction]
  change 1 / (k : ℝ) ^ n * Real.log (g n) -
    1 / (k : ℝ) ^ (n + 1) * ((k : ℝ) * Real.log (g n) + _ - _) =
      (Real.log ((n : ℝ) + 1) - Real.log (1 + (n : ℝ) / g n ^ (k - 1))) / (k : ℝ) ^ (n + 1)
  rw [pow_succ]
  field_simp
  ring

private theorem sum_log_difference {k l n : ℕ} {C : ℝ}
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hC : Tendsto (root k l) atTop (𝓝 C)) (hC₀ : 0 < C)
    (hn : 1 ≤ n) (ha : Summable (logTerm k n))
    (hb : Summable (fun m : ℕ => weight k m * correction k l (m + n))) :
    (∑' m, logTerm k n m) - (∑' m : ℕ, weight k m * correction k l (m + n)) =
      (k : ℝ) ^ n * (Real.log (root k l n) - Real.log C) := by
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm (m : ℕ) :
      logTerm k n m - weight k m * correction k l (m + n) =
        (k : ℝ) ^ n * (Real.log (root k l (m + n)) - Real.log (root k l (m + n + 1))) := by
    rw [log_root_step hk hl (show 1 ≤ m + n by omega), logTerm, weight,
      show m + n + 1 = (m + 1) + n by omega, pow_add]
    rw [Nat.cast_add, add_right_comm (m : ℝ) 1]
    field_simp
    ring
  -- The logarithms of the normalized roots cancel in successive terms.
  have hpartial (N : ℕ) :
      (∑ m ∈ Finset.range N, (logTerm k n m - weight k m * correction k l (m + n))) =
        (k : ℝ) ^ n * (Real.log (root k l n) - Real.log (root k l (N + n))) := by
    simp_rw [hterm, ← Finset.mul_sum]
    simpa only [Nat.zero_add, Nat.add_right_comm] using
      congrArg ((k : ℝ) ^ n * ·) (Finset.sum_range_sub' (fun m => Real.log (root k l (m + n))) N)
  have hlimit : Tendsto (fun N : ℕ => Real.log (root k l (N + n))) atTop (𝓝 (Real.log C)) :=
    (Real.continuousAt_log hC₀.ne').tendsto.comp (hC.comp (tendsto_add_atTop_nat n))
  have hs := (ha.hasSum.sub hb.hasSum).tendsto_sum_nat
  simp_rw [hpartial] at hs
  exact tendsto_nhds_unique hs (tendsto_const_nhds.mul (tendsto_const_nhds.sub hlimit))

private theorem polynomial_mul_geometric (R : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-R)) := by
  have he := ((isLittleO_exp_neg_mul_rpow_atTop
    (Real.log_pos (by norm_num : 1 < (3 / 2 : ℝ))) (-R - 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).isBigO
  have hg : (fun n : ℕ => (2 / 3 : ℝ) ^ n) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-R - 2)) := by
    refine he.congr_left fun n => ?_
    change Real.exp (-Real.log (3 / 2 : ℝ) * n) = _
    rw [neg_mul, mul_comm (Real.log _), Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num), ← inv_pow]
    norm_num
  refine ((isBigO_refl (fun n : ℕ => (n : ℝ) ^ 2) atTop).mul hg).congr'
    EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change (n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-R - 2) = _
  rw [← Real.rpow_natCast, ← Real.rpow_add (Nat.cast_pos.mpr hn)]
  norm_num

end gobelSequence_error_isBigO

open gobelSequence_error_isBigO in
/-- **The logarithmic identity behind the Göbel error.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C > 0$ be a real number such that the real
numbers $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every natural
number $n \ge 1$ for which the two series below converge,

$$\sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m} - \sum_{m=1}^{\infty} \frac{1}{k^m}
\log\Bigl(1 + \frac{m + n - 1}{g_{k,l}(m + n - 1)^{k-1}}\Bigr) =
k^n \bigl(\log C_{k,l}(n) - \log C\bigr).$$

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, proof of Theorem 11 (`jis-2024-24.8.1-thm-11`). -/
public theorem gobelSequence_log_series_sub_correction_series {k l n : ℕ} {C : ℝ}
    (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (hC₀ : 0 < C) (hn : 1 ≤ n)
    (ha : Summable (fun m : ℕ => Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)))
    (hb : Summable (fun m : ℕ => Real.log (1 + ((m + n : ℕ) : ℝ) /
      (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1))) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) -
        (∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) /
          (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1)) =
      (k : ℝ) ^ n * (Real.log ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)) -
        Real.log C) := by
  have hlog : (fun m : ℕ => Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) = logTerm k n := by
    funext m
    simp only [logTerm, weight, div_eq_inv_mul]
  have hcorr : (fun m : ℕ => Real.log (1 + ((m + n : ℕ) : ℝ) /
      (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1)) =
      fun m => weight k m * correction k l (m + n) := by
    funext m
    simp only [weight, correction, div_eq_inv_mul]
  rw [hlog] at ha ⊢
  rw [hcorr] at hb ⊢
  exact sum_log_difference hk hl hC hC₀ hn ha hb

open gobelSequence_error_isBigO in
-- The geometric estimate works for all real exponents, so the source hypothesis is unused.
set_option linter.unusedVariables false in
/-- **The Göbel error term decays faster than every power of $n$.** Let $k, l \ge 2$ be natural
numbers, let $g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C$ be a real number such that the
real numbers $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every real
number $R > 0$, as $n \to \infty$,

$$\exp\Bigl(\sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m}\Bigr) -
\Bigl(\frac{C_{k,l}(n)}{C}\Bigr)^{k^n} = O(n^{-R}).$$

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Theorem 11 (`jis-2024-24.8.1-thm-11`). -/
public theorem gobelSequence_error_isBigO (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (R : ℝ) (hR : 0 < R) :
    (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n) / C) ^ (k ^ n))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-R)) := by
  have hroot (n : ℕ) (hn : 1 ≤ n) : 1 ≤ root k l n := by
    apply Real.one_le_rpow _ (by positivity)
    linarith [(growth hk hl hn).1, Nat.cast_nonneg (α := ℝ) n]
  have hC₀ : 0 < C :=
    zero_lt_one.trans_le (ge_of_tendsto hC (eventually_ge_atTop 1 |>.mono fun n hn => hroot n hn))
  obtain ⟨hw, hw_le, hw_linear⟩ := summable_weights hk
  let M := ∑' m : ℕ, weight k m * (m + 1 : ℝ)
  have hM : 0 ≤ M := tsum_nonneg fun m => by unfold weight; positivity
  have hbound :
      (fun n : ℕ => Real.exp (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
          - (root k l n / C) ^ (k ^ n))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ 2 * (2 / 3 : ℝ) ^ n) := by
    refine IsBigO.of_bound (Real.exp M * M) ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    let A := ∑' m, logTerm k n m
    let B := ∑' m : ℕ, weight k m * correction k l (m + n)
    -- Bound both series using the first moment of the geometric weights.
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hmajorA := (hw.mul_left (Real.log n)).add hw_linear
    have hnonnegA (m : ℕ) : 0 ≤ logTerm k n m := by
      unfold logTerm weight
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    have ha : Summable (logTerm k n) := hmajorA.of_nonneg_of_le hnonnegA (logTerm_le hn)
    have hA : A ≤ Real.log n + M := by
      refine (Summable.tsum_le_tsum (logTerm_le hn) ha hmajorA).trans ?_
      rw [(hw.mul_left (Real.log n)).tsum_add hw_linear, hw.tsum_mul_left]
      simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left hw_le hlogn) (le_refl M)
    let d := (n : ℝ) * (2 / 3 : ℝ) ^ n
    have hcorrection (m : ℕ) := correction_bounds hk hl hn m
    have hmajorB (m : ℕ) : weight k m * correction k l (m + n) ≤
        d * (weight k m * (m + 1 : ℝ)) := by
      rw [mul_left_comm d]
      exact mul_le_mul_of_nonneg_left (hcorrection m).2 (by unfold weight; positivity)
    have hnonnegB (m : ℕ) : 0 ≤ weight k m * correction k l (m + n) :=
      mul_nonneg (by unfold weight; positivity) (hcorrection m).1
    have hb := (hw_linear.mul_left d).of_nonneg_of_le hnonnegB hmajorB
    have hB₀ : 0 ≤ B := tsum_nonneg hnonnegB
    have hB : B ≤ d * M := by
      have h := Summable.tsum_le_tsum hmajorB hb (hw_linear.mul_left d)
      rwa [hw_linear.tsum_mul_left] at h
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hExpA : Real.exp A ≤ n * Real.exp M := by
      rw [← Real.exp_log hn₀, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hA
    have hroot₀ : 0 < root k l n := zero_lt_one.trans_le (hroot n hn)
    have hratio : (root k l n / C) ^ (k ^ n) = Real.exp (A - B) := by
      rw [sum_log_difference hk hl hC hC₀ hn ha hb, ← Nat.cast_pow, Real.exp_nat_mul,
        ← Real.log_div hroot₀.ne' hC₀.ne', Real.exp_log (div_pos hroot₀ hC₀)]
    change ‖Real.exp (∑' m : ℕ, _) - (root k l n / C) ^ (k ^ n)‖ ≤ _
    have hsum : (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) = A := by
      simp only [A, logTerm, weight, div_eq_inv_mul]
    rw [hsum, hratio, Real.norm_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      Real.norm_of_nonneg (by positivity)]
    calc
      _ = Real.exp A * (1 - Real.exp (-B)) := by rw [sub_eq_add_neg A B, Real.exp_add]; ring
      _ ≤ Real.exp A * B := by
        have h := Real.add_one_le_exp (-B)
        gcongr
        linarith
      _ ≤ (n * Real.exp M) * (d * M) := mul_le_mul hExpA hB hB₀ (by positivity)
      _ = _ := by dsimp [d]; ring
  exact hbound.trans (polynomial_mul_geometric R)

end MetaMathlibExt
