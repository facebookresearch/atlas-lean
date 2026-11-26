/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Reciprocal totients of primes between two powers

Subtracting Mertens' reciprocal-prime estimates at the two cutoffs cancels the constant.
Replacing the reciprocal prime by the reciprocal totient changes the constant but not the limit
of this difference.
-/

open Filter Finset Real Topology
open ArithmeticFunction (vonMangoldt vonMangoldt_apply_prime vonMangoldt_nonneg)

namespace MetaMathlibExt

namespace calzado_sum_inv_totient_fifth_to_half_tendsto

/-- The bounded error in Mertens' weighted prime sum, discarding higher prime powers. -/
private lemma exists_abs_sum_log_prime_div_sub_log_le :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ p ∈ n.primesLE, log p / (p : ℝ)) - log n| ≤ C := by
  obtain ⟨K, hK⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le (q := 1) 1 isUnit_one
  have hS := vonMangoldt.summable_residueClass_non_primes_div (1 : ZMod 1)
  simp only [Nat.totient_one, Nat.cast_one, div_one, vonMangoldt.residueClass,
    Set.indicator_apply, Set.mem_ofPred_eq, Subsingleton.elim (_ : ZMod 1) 1, ite_true] at hK
  simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
    Subsingleton.elim (_ : ZMod 1) 1, ite_true] at hS
  let r (n : ℕ) := (if n.Prime then 0 else vonMangoldt n) / (n : ℝ)
  have hr (n : ℕ) : 0 ≤ r n := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    split_ifs <;> simp [vonMangoldt_nonneg]
  refine ⟨K + ∑' n, r n, fun n hn ↦ ?_⟩
  have h := hK n (by exact_mod_cast hn)
  rw [Nat.floor_natCast] at h
  have hsum : (∑ p ∈ n.primesLE, log p / (p : ℝ)) =
      (∑ p ∈ Ioc 0 n, vonMangoldt p / (p : ℝ)) - ∑ p ∈ Ioc 0 n, r p := by
    rw [Nat.primesLE_eq_filter_Ioc_zero, sum_filter, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp [r, hp, vonMangoldt_apply_prime]
  rw [hsum, sub_right_comm]
  exact (abs_sub _ _).trans (add_le_add h
    (by rw [abs_of_nonneg (sum_nonneg fun p _ ↦ hr p)]; exact hS.sum_le_tsum _ fun p _ ↦ hr p))

/-- Bounds for a logarithmic increment by its two endpoint slopes. -/
private lemma log_sub_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) * y⁻¹ ≤ log y - log x ∧ log y - log x ≤ (y - x) * x⁻¹ := by
  have hlo := one_sub_inv_le_log_of_pos (div_pos hy hx)
  have hhi := log_le_sub_one_of_pos (div_pos hy hx)
  rw [log_div hy.ne' hx.ne', inv_div] at hlo
  rw [log_div hy.ne' hx.ne'] at hhi
  simpa only [← div_eq_mul_inv, sub_div, div_self hx.ne', div_self hy.ne'] using ⟨hlo, hhi⟩

/-- Discrete partial summation gives the convergent remainder in Mertens' second theorem. -/
private lemma exists_tendsto_sum_prime_recip_sub_loglog :
    ∃ C : ℝ, Tendsto (fun n : ℕ ↦ (∑ p ∈ n.primesLE, 1 / (p : ℝ)) - log (log n))
      atTop (𝓝 C) := by
  obtain ⟨K, hK⟩ := exists_abs_sum_log_prime_div_sub_log_le
  -- Clip the logarithm below two so that all inverse-log weights are defined and positive.
  let L (n : ℕ) := log (max (n : ℝ) 2)
  let w (n : ℕ) := (L n)⁻¹
  let a (n : ℕ) := if n.Prime then log n / (n : ℝ) else 0
  have hL (n : ℕ) : 0 < L n := log_pos (one_lt_two.trans_le (le_max_right _ _))
  have hLmono : Monotone L := fun m n hmn ↦ log_le_log (by positivity)
    (max_le_max (Nat.cast_le.mpr hmn) le_rfl)
  have hw : Antitone w := fun m n hmn ↦ inv_anti₀ (hL m) (hLmono hmn)
  have hw₀ : Tendsto (fun n : ℕ ↦ w (n + 1)) atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    apply tendsto_log_atTop.comp
    exact tendsto_atTop_mono (fun n ↦ (Nat.cast_le.mpr (Nat.le_succ n)).trans (le_max_left _ _))
      tendsto_natCast_atTop_atTop
  have hsum (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
      (∑ i ∈ range n, f (i + 1)) = ∑ i ∈ range (n + 1), f i := by
    rw [sum_range_succ', hf, add_zero]
  have hdiff (n : ℕ) :
      ‖∑ i ∈ range n, (a (i + 1) - (L (i + 1) - L i))‖ ≤ max K 0 + L 0 := by
    rw [norm_eq_abs, sum_sub_distrib, sum_range_sub, hsum a (by simp [a])]
    rw [show (∑ i ∈ range (n + 1), a i) = ∑ p ∈ n.primesLE, log p / (p : ℝ) by
      rw [Nat.primesLE_eq_filter_range, sum_filter]]
    by_cases hn : 2 ≤ n
    · rw [show L n = log n from congrArg log (max_eq_left (by exact_mod_cast hn))]
      have heq : (∑ p ∈ n.primesLE, log p / (p : ℝ)) - (log n - L 0) =
          ((∑ p ∈ n.primesLE, log p / (p : ℝ)) - log n) + L 0 := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add ((hK n (by omega)).trans (le_max_left _ _))
        (by rw [abs_of_pos (hL 0)]))
    · have hempty : n.primesLE = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact hn ((Nat.two_le_of_mem_primesLE hp).trans (Nat.le_of_mem_primesLE hp))
      have hLn : L n = L 0 := by
        have hn₂ : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
        simp [L, max_eq_right hn₂]
      rw [hempty, sum_empty, hLn, sub_self, sub_zero, abs_zero]
      exact add_nonneg (le_max_right _ _) (hL 0).le
  have hw' : Antitone (fun i : ℕ ↦ w (i + 1)) :=
    hw.comp_monotone fun _ _ h ↦ Nat.succ_le_succ h
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (hw'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hw₀ hdiff)
  -- The inverse-log weighted increments differ from log-log increments by a summable series.
  let d (i : ℕ) := log (L (i + 1)) - log (L i) - w (i + 1) * (L (i + 1) - L i)
  have hd (i : ℕ) : 0 ≤ d i ∧ d i ≤ log 2 * (w i - w (i + 1)) := by
    have h := log_sub_bounds (hL i) (hL (i + 1))
    have hstep : L (i + 1) - L i ≤ log 2 := by
      have hle : max ((↑(i + 1) : ℝ)) 2 ≤ 2 * max (i : ℝ) 2 := by
        have h1 := le_max_left (i : ℝ) 2
        have h2 := le_max_right (i : ℝ) 2
        rw [Nat.cast_add, Nat.cast_one, max_le_iff]
        constructor <;> linarith
      have hlog := log_le_log (by positivity) hle
      rw [log_mul two_ne_zero (by positivity : max (i : ℝ) 2 ≠ 0)] at hlog
      dsimp [L]
      linarith
    refine ⟨sub_nonneg.mpr (by simpa only [w, mul_comm] using h.1), ?_⟩
    calc
      d i ≤ (L (i + 1) - L i) * (w i - w (i + 1)) := by
        rw [mul_sub, mul_comm _ (w (i + 1))]
        exact sub_le_sub_right h.2 _
      _ ≤ _ := mul_le_mul_of_nonneg_right hstep (sub_nonneg.mpr (hw (Nat.le_succ i)))
  have hd_sum : Summable d := by
    refine summable_of_sum_range_le (fun i ↦ (hd i).1) (c := log 2 * w 0) fun n ↦ ?_
    calc
      (∑ i ∈ range n, d i) ≤ ∑ i ∈ range n, log 2 * (w i - w (i + 1)) :=
        sum_le_sum fun i _ ↦ (hd i).2
      _ = log 2 * (w 0 - w n) := by rw [← mul_sum, sum_range_sub']
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (log_nonneg one_le_two)
        exact sub_le_self _ (inv_nonneg.mpr (hL n).le)
  have hterm (i : ℕ) :
      w i • (a i) = if i.Prime then 1 / (i : ℝ) else 0 := by
    by_cases hi : i.Prime
    · have h₂ : (2 : ℝ) ≤ i := by exact_mod_cast hi.two_le
      simp only [w, L, max_eq_left h₂, a, hi, ite_true, smul_eq_mul, ← mul_div_assoc,
        inv_mul_cancel₀ (log_pos (one_lt_two.trans_le h₂)).ne']
    · simp [a, hi]
  refine ⟨c - (∑' i, d i) - log (L 0),
    ((hc.sub hd_sum.hasSum.tendsto_sum_nat).sub_const _).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [← sum_sub_distrib]
  have htel : (∑ i ∈ range n, (log (L (i + 1)) - log (L i))) = log (L n) - log (L 0) :=
    sum_range_sub (log ∘ L) n
  have hstep (i : ℕ) : w (i + 1) • (a (i + 1) - (L (i + 1) - L i)) - d i =
      w (i + 1) • a (i + 1) - (log (L (i + 1)) - log (L i)) := by
    simp only [d, smul_eq_mul]
    ring
  simp_rw [hstep]
  rw [sum_sub_distrib, htel]
  simp_rw [hterm]
  rw [hsum (fun p : ℕ ↦ if p.Prime then (1 : ℝ) / p else 0) (by simp) n,
    ← sum_filter, ← Nat.primesLE_eq_filter_range]
  rw [show L n = log n from congrArg log (max_eq_left (by exact_mod_cast hn))]
  ring

/-- Rounding a real cutoff down changes its log-log term by an error tending to zero. -/
private lemma tendsto_loglog_sub_loglog_floor :
    Tendsto (fun x : ℝ ↦ log (log x) - log (log (⌊x⌋₊ : ℝ))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have hi : Tendsto (fun x : ℝ ↦ (log (⌊x⌋₊ : ℝ))⁻¹) atTop (𝓝 0) :=
    (tendsto_log_atTop.comp hcast).inv_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hi.const_mul (log 2)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (n := 2) (by simpa using hx)
    have h := log_le_log (by linarith : (0 : ℝ) < ⌊x⌋₊) (Nat.floor_le (by linarith : 0 ≤ x))
    exact sub_nonneg.mpr (log_le_log (log_pos (by linarith)) h)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hn : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (n := 2) (by simpa using hx)
    have hn₀ : (0 : ℝ) < ⌊x⌋₊ := by linarith
    have hle : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one x]
    have hb := log_le_log (by linarith : 0 < x) hle
    rw [log_mul two_ne_zero hn₀.ne'] at hb
    have hlog : 0 < log (⌊x⌋₊ : ℝ) := log_pos (by linarith)
    exact (log_sub_bounds hlog (log_pos (by linarith))).2.trans
      (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hlog.le))

/-- The reciprocal-totient correction converges by comparison with the sum of `2 / p²`. -/
private lemma exists_tendsto_totient_correction :
    ∃ D : ℝ, Tendsto (fun n : ℕ ↦ ∑ p ∈ n.primesLE,
      (1 / (Nat.totient p : ℝ) - 1 / (p : ℝ))) atTop (𝓝 D) := by
  let f (p : ℕ) := if p.Prime then 1 / (Nat.totient p : ℝ) - 1 / (p : ℝ) else 0
  have hf (p : ℕ) : 0 ≤ f p ∧ f p ≤ 2 * (1 / (p : ℝ) ^ 2) := by
    by_cases hp : p.Prime
    · have h₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h₁ : 0 < (p : ℝ) - 1 := by linarith
      have h₀ : 0 < (p : ℝ) := by linarith
      simp only [f, hp, ite_true, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
      refine ⟨sub_nonneg.mpr (one_div_le_one_div_of_le h₁ (by linarith)), ?_⟩
      calc
        _ = 1 / (((p : ℝ) - 1) * p) := by field_simp; ring
        _ ≤ 2 * (1 / (p : ℝ) ^ 2) := by
          rw [mul_one_div, div_le_div_iff₀ (mul_pos h₁ h₀) (sq_pos_of_pos h₀)]
          nlinarith [mul_nonneg h₀.le (sub_nonneg.mpr h₂)]
    · simp [f, hp]
  have hs : Summable f := Summable.of_nonneg_of_le (fun p ↦ (hf p).1) (fun p ↦ (hf p).2)
    (((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).mul_left 2)
  refine ⟨_, (hs.hasSum.tendsto_sum_nat.comp (tendsto_atTop_mono
    (fun n : ℕ ↦ Nat.le_succ n) tendsto_id)).congr fun n ↦ ?_⟩
  rw [Nat.primesLE_eq_filter_range, sum_filter]
  rfl

end calzado_sum_inv_totient_fifth_to_half_tendsto

open calzado_sum_inv_totient_fifth_to_half_tendsto in
/-- **Reciprocal totients of the primes between $x^{1/5}$ and $x^{1/2}$.** As the real number $x$
tends to infinity, the sum of $1/\varphi(p)$ over the primes $p$ with $x^{1/5} < p \le x^{1/2}$
tends to $\log(5/2)$, where $\varphi$ is Euler's totient function.

The paper prints the limit as $0.916\ldots$; the exact value $\log(5/2) = 0.91629\ldots$ is
forced by Mertens' theorem.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem calzado_sum_inv_totient_fifth_to_half_tendsto :
    Tendsto (fun x : ℝ =>
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ))
      atTop (𝓝 (Real.log (5 / 2))) := by
  obtain ⟨C, hC⟩ := exists_tendsto_sum_prime_recip_sub_loglog
  obtain ⟨D, hD⟩ := exists_tendsto_totient_correction
  let T (y : ℝ) := (∑ p ∈ (⌊y⌋₊ : ℕ).primesLE, 1 / (Nat.totient p : ℝ)) - log (log y)
  have hT : Tendsto T atTop (𝓝 (C + D)) := by
    have h := ((hC.add hD).comp (tendsto_nat_floor_atTop (α := ℝ))).sub
      tendsto_loglog_sub_loglog_floor
    rw [sub_zero] at h
    refine h.congr fun y ↦ ?_
    dsimp only [Function.comp_apply, T]
    rw [sum_sub_distrib]
    ring
  have htop := hT.comp (tendsto_rpow_atTop (show 0 < (1 : ℝ) / 2 by norm_num))
  have hbot := hT.comp (tendsto_rpow_atTop (show 0 < (1 : ℝ) / 5 by norm_num))
  have hlim : Tendsto (fun x : ℝ ↦ T (x ^ ((1 : ℝ) / 2)) - T (x ^ ((1 : ℝ) / 5)) + log (5 / 2))
      atTop (𝓝 (log (5 / 2))) := by
    simpa only [Function.comp_apply, sub_self, zero_add] using
      (htop.sub hbot).add_const (log (5 / 2))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  let y := x ^ ((1 : ℝ) / 5)
  let z := x ^ ((1 : ℝ) / 2)
  have hx₀ := zero_lt_one.trans hx
  have hy₀ : 0 ≤ y := rpow_nonneg hx₀.le _
  have hyz : y ≤ z := rpow_le_rpow_of_exponent_le hx.le (by norm_num)
  have hzx : z ≤ x := rpow_le_self_of_one_le hx.le (by norm_num)
  have hsub : (⌊y⌋₊ : ℕ).primesLE ⊆ (⌊z⌋₊ : ℕ).primesLE := fun p hp ↦
    Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.floor_le_floor hyz),
      Nat.prime_of_mem_primesLE hp⟩
  -- A prime equal to the lower cutoff is subtracted, while equality at the upper cutoff remains.
  have hinterval : (⌊z⌋₊ : ℕ).primesLE \ (⌊y⌋₊ : ℕ).primesLE =
      (range (⌊x⌋₊ + 1)).filter (fun p : ℕ ↦ p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ z) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, mem_filter, mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨hpz, hp⟩, hpy⟩
      have hlt : ⌊y⌋₊ < p := lt_of_not_ge fun h ↦ hpy ⟨h, hp⟩
      exact ⟨hpz.trans (Nat.floor_le_floor hzx), hp, (Nat.floor_lt hy₀).mp hlt,
        (Nat.le_floor_iff (hy₀.trans hyz)).mp hpz⟩
    · rintro ⟨_, hp, hpy, hpz⟩
      exact ⟨⟨Nat.le_floor hpz, hp⟩, fun h ↦ ((Nat.floor_lt hy₀).mpr hpy).not_ge h.1⟩
  have hlog : log (log z) - log (log y) = log (5 / 2) := by
    have hL := log_pos hx
    dsimp only [y, z]
    rw [log_rpow hx₀, log_rpow hx₀, ← log_div (mul_pos (by norm_num) hL).ne'
      (mul_pos (by norm_num) hL).ne']
    congr 1
    field_simp
  change T z - T y + log (5 / 2) = _
  rw [← hinterval, sum_sdiff_eq_sub hsub]
  dsimp only [T]
  linarith only [hlog]

end MetaMathlibExt
