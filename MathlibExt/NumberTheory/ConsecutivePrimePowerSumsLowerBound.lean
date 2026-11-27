/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import MathlibExt.NumberTheory.PrimeNumberTheorem

/-!
# Lower bounds for sums of consecutive prime powers

We bound the number of admissible blocks of consecutive prime powers below by half the square of
the longest admissible length, and give an asymptotic lower bound for that square.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

namespace card_consecutivePrimePowerSums_ge

private noncomputable def prefixSum (k n : ℕ) : ℕ :=
  ∑ i ∈ range n, Nat.nth Nat.Prime i ^ k

private noncomputable def maxLength (k x : ℕ) : ℕ :=
  Nat.findGreatest (fun n => ∑ i ∈ range n, Nat.nth Nat.Prime i ^ k ≤ x) x

private lemma prefixSum_spec (k x : ℕ) : prefixSum k (maxLength k x) ≤ x :=
  Nat.findGreatest_spec (P := fun n => prefixSum k n ≤ x) (Nat.zero_le _)
    (by simp [prefixSum])

private lemma length_le_prefixSum (k n : ℕ) : n ≤ prefixSum k n := calc
  n = ∑ _i ∈ range n, 1 := by simp
  _ ≤ prefixSum k n := sum_le_sum fun i _ =>
    Nat.one_le_pow _ _ (Nat.prime_nth_prime i).pos

private lemma lt_next_prefixSum (k x : ℕ) : x < prefixSum k (maxLength k x + 1) := by
  by_cases h : maxLength k x + 1 ≤ x
  · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun n => prefixSum k n ≤ x)
      (Nat.lt_succ_self (maxLength k x)) h)
  · exact (lt_of_not_ge h).trans_le (length_le_prefixSum _ _)

private lemma tendsto_maxLength (k : ℕ) : Tendsto (maxLength k) atTop atTop := by
  refine tendsto_atTop.2 fun n => ?_
  filter_upwards [eventually_ge_atTop (prefixSum k n)] with x hx
  exact Nat.le_findGreatest ((length_le_prefixSum k n).trans hx) hx

private lemma count_ge (k x : ℕ) :
    (maxLength k x : ℝ) ^ 2 / 2 ≤
      (((range x ×ˢ Icc 1 x).filter (fun lm =>
        ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ k ≤ x)).card : ℝ) := by
  let n := maxLength k x
  let ends := range (n + 1)
  let pairs := (ends ×ˢ ends).filter fun ab => ab.1 < ab.2
  let blocks := (range x ×ˢ Icc 1 x).filter (fun lm =>
    ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ k ≤ x)
  have hn : n ≤ x := (length_le_prefixSum k n).trans (prefixSum_spec k x)
  -- Each ordered pair of endpoints in the first n terms gives an admissible block.
  have hcard : pairs.card ≤ blocks.card := by
    refine card_le_card_of_injOn (fun ab : ℕ × ℕ => (ab.1, ab.2 - ab.1)) ?_ ?_
    · rintro ⟨a, b⟩ hab
      change (a, b) ∈ pairs at hab
      have hab' : a < b := (mem_filter.1 hab).2
      have hbn : b ≤ n := Nat.lt_succ_iff.mp (mem_range.1 (mem_product.1
        (mem_filter.1 hab).1).2)
      have hsum : (∑ i ∈ range (b - a), Nat.nth Nat.Prime (a + i) ^ k) ≤ prefixSum k n := by
        rw [← sum_Ico_eq_sum_range (fun i => Nat.nth Nat.Prime i ^ k) a b]
        refine sum_le_sum_of_subset ?_
        intro i hi
        exact mem_range.2 ((mem_Ico.1 hi).2.trans_le hbn)
      change (a, b - a) ∈ blocks
      exact mem_filter.2
        ⟨mem_product.2 ⟨mem_range.2 (by omega), mem_Icc.2 ⟨by omega, by omega⟩⟩,
          hsum.trans (prefixSum_spec k x)⟩
    · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
      have hab' : a < b := (mem_filter.1 (show (a, b) ∈ pairs from hab)).2
      have hcd' : c < d := (mem_filter.1 (show (c, d) ∈ pairs from hcd)).2
      have hac : a = c := congrArg Prod.fst heq
      have hbd : b - a = d - c := congrArg Prod.snd heq
      exact Prod.ext hac (by omega)
  have hchoose : (n + 1).choose 2 ≤ blocks.card := by
    simpa [pairs, ends, card_product_filter_lt] using hcard
  have hdouble : 2 * (n + 1).choose 2 = (n + 1) * n := by
    simpa [Nat.choose_one_right, Nat.mul_comm 2] using (Nat.add_one_mul_choose_eq n 1).symm
  have hprod : (n + 1) * n ≤ 2 * blocks.card :=
    hdouble ▸ Nat.mul_le_mul_left 2 hchoose
  have hreal : ((n : ℝ) + 1) * n ≤ 2 * (blocks.card : ℝ) := by exact_mod_cast hprod
  change (n : ℝ) ^ 2 / 2 ≤ (blocks.card : ℝ)
  nlinarith only [hreal, Nat.cast_nonneg (α := ℝ) n]

private lemma nth_prime_isEquivalent :
    (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) ~[atTop]
      fun n => (n : ℝ) * Real.log n := by
  let p : ℕ → ℝ := fun n => Nat.nth Nat.Prime n
  have hp := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hp' : Tendsto p atTop atTop := tendsto_natCast_atTop_iff.mpr hp
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] fun n => p n / Real.log (p n) := by
    apply (MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem.comp_tendsto
      hp).congr_left
    exact Eventually.of_forall fun n => by
      simp [Nat.primeCounting, Nat.primeCounting',
        Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
  have hlog : (fun x : ℝ => Real.log (x / Real.log x)) ~[atTop] Real.log := by
    have ho := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    refine (IsEquivalent.refl.sub_isLittleO ho).congr_left ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.log_div (by positivity) (Real.log_pos hx).ne').symm
  have hlog' : (fun n => Real.log (p n)) ~[atTop] fun n : ℕ => Real.log ((n : ℝ) + 1) :=
    (hlog.comp_tendsto hp').symm.trans (hc.symm.log hn)
  have hs : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] fun n => (n : ℝ) :=
    IsEquivalent.refl.add_const_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  refine ((hc.symm.mul hlog').congr_left ?_).trans
    (hs.mul (hs.log tendsto_natCast_atTop_atTop))
  filter_upwards [hp'.eventually_gt_atTop 1] with n hn
  exact div_mul_cancel₀ _ (Real.log_pos hn).ne'

private lemma monotoneOn_pow (k n : ℕ) :
    MonotoneOn (fun t : ℝ => t ^ k) (Set.Icc 0 (0 + (n : ℝ))) :=
  fun _ ha _ _ hab => pow_le_pow_left₀ ha.1 hab _

private lemma prefixSum_lower (k n : ℕ) :
    (n : ℝ) ^ (k + 1) / ((k : ℝ) + 1) ≤ prefixSum k n := by
  have h := (monotoneOn_pow k n).integral_le_sum (x₀ := 0) (a := n)
  simp only [zero_add, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero] at h
  refine h.trans ?_
  simp only [prefixSum, Nat.cast_sum, Nat.cast_pow]
  exact sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast (show i + 1 ≤ Nat.nth Nat.Prime i from
      (Nat.le_succ _).trans (Nat.add_two_le_nth_prime i))) _

private lemma eventually_prefixSum_le (k : ℕ) (hk : 0 < k) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ n : ℕ in atTop, (prefixSum k n : ℝ) ≤
      c * ((n : ℝ) ^ (k + 1) / ((k : ℝ) + 1) * Real.log n ^ k) := by
  let b (i : ℕ) := ((i : ℝ) * Real.log i) ^ k
  have hb (i : ℕ) : 0 ≤ b i := by dsimp [b]; positivity
  have hb_lim : Tendsto b atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).atTop_pow₀ hk.ne'
  have hs_lim : Tendsto (fun n => ∑ i ∈ range n, b i) atTop atTop := by
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_atTop_mono (fun n => ?_) hb_lim)
    rw [sum_range_succ]
    exact le_add_of_nonneg_left (sum_nonneg fun i _ => hb i)
  have hsum : (fun n => (prefixSum k n : ℝ)) ~[atTop] fun n => ∑ i ∈ range n, b i := by
    have h := ((nth_prime_isEquivalent.pow k).isLittleO).sum_range hb hs_lim
    simpa only [IsEquivalent, Pi.sub_def, Pi.pow_apply, sum_sub_distrib, prefixSum, Nat.cast_sum,
      Nat.cast_pow, b] using h
  filter_upwards [hsum.isLittleO.bound (sub_pos.mpr hc)] with n hn
  have hnonneg : 0 ≤ ∑ i ∈ range n, b i := sum_nonneg fun i _ => hb i
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  have hsum_le : (prefixSum k n : ℝ) ≤ c * ∑ i ∈ range n, b i := by
    linarith only [hn, le_abs_self ((prefixSum k n : ℝ) - ∑ i ∈ range n, b i)]
  refine hsum_le.trans (mul_le_mul_of_nonneg_left ?_ (zero_lt_one.trans hc).le)
  have hpow := (monotoneOn_pow k n).sum_le_integral (x₀ := 0) (a := n)
  simp only [zero_add, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero] at hpow
  calc
    ∑ i ∈ range n, b i ≤ ∑ i ∈ range n, (i : ℝ) ^ k * Real.log n ^ k := by
      refine sum_le_sum fun i hi => ?_
      dsimp only [b]
      rw [mul_pow]
      by_cases hi₀ : i = 0
      · simp [hi₀, hk.ne']
      · refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_natCast_nonneg i) ?_ _)
          (by positivity)
        exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi₀))
          (Nat.cast_le.mpr (mem_range.1 hi).le)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)

private lemma eventually_div_log_pow_le (k : ℕ) (hk : 0 < k) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / Real.log x ^ k ≤ c * ((maxLength k x : ℝ) / ((k : ℝ) + 1)) ^ (k + 1) := by
  let d : ℝ := (k : ℝ) + 1
  let a : ℝ := (1 + c) / 2
  let C : ℝ := Real.log d + d * Real.log 2
  let R (x : ℕ) := 1 + 1 / (maxLength k x : ℝ)
  let L (x : ℕ) := 1 + C / Real.log x
  have ha : 1 < a := by dsimp [a]; linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hR : Tendsto R atTop (𝓝 1) := by
    simpa only [R, add_zero, Function.comp_apply] using
      tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_maxLength k))
  have hL : Tendsto L atTop (𝓝 1) := by
    simpa only [L, add_zero, Function.comp_apply] using tendsto_const_nhds.add
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop C)
  have hfactor : Tendsto (fun x => a * (R x ^ (k + 1) * L x ^ k)) atTop (𝓝 a) := by
    simpa only [one_pow, one_mul, mul_one] using ((hR.pow _).mul (hL.pow k)).const_mul a
  have hnext : Tendsto (fun x => maxLength k x + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_maxLength k)
  filter_upwards [hnext.eventually (eventually_prefixSum_le k hk ha),
    hfactor.eventually_le_const (show a < c by dsimp [a]; linarith), eventually_gt_atTop 1,
    (tendsto_maxLength k).eventually_ge_atTop 1] with x hupper hfac hx hn
  let n : ℝ := maxLength k x
  have hn₁ : 1 ≤ n := by simpa only [n, Nat.one_le_cast] using hn
  have hn₀ : 0 < n := zero_lt_one.trans_le hn₁
  have hx₁ : (1 : ℝ) < x := by exact_mod_cast hx
  have hx₀ : 0 < (x : ℝ) := zero_lt_one.trans hx₁
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos hx₁
  -- Admissibility bounds n^d by d*x, so log(n+1) is at most (log x + C)/d.
  have hpow : n ^ (k + 1) ≤ d * (x : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hd).mp ((prefixSum_lower k (maxLength k x)).trans
      (by exact_mod_cast prefixSum_spec k x))
  have hlog := Real.log_le_log (pow_pos hn₀ _) hpow
  rw [Real.log_pow, Nat.cast_add_one, Real.log_mul hd.ne' hx₀.ne'] at hlog
  change d * Real.log n ≤ _ at hlog
  have hlog_next : Real.log (n + 1) ≤ Real.log x / d * L x := calc
    _ ≤ Real.log (2 * n) := Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn₀.ne'
    _ ≤ (Real.log x + C) / d := by
      apply (le_div_iff₀ hd).2
      dsimp [C]
      linarith only [hlog]
    _ = _ := by dsimp [L]; field_simp
  have hn_succ : n + 1 = R x * n := by dsimp [R, n]; field_simp
  apply (div_le_iff₀ (pow_pos hlogx _)).2
  calc
    (x : ℝ) ≤ (prefixSum k (maxLength k x + 1) : ℝ) := by
      exact_mod_cast (lt_next_prefixSum k x).le
    _ ≤ a * ((n + 1) ^ (k + 1) / d * Real.log (n + 1) ^ k) := by
      simpa only [Function.comp_apply, Nat.cast_add_one] using hupper
    _ ≤ a * ((n + 1) ^ (k + 1) / d * (Real.log x / d * L x) ^ k) := by
      gcongr
      exact Real.log_nonneg (by linarith)
    _ = a * (R x ^ (k + 1) * L x ^ k) * ((n / d) ^ (k + 1) * Real.log x ^ k) := by
      rw [hn_succ]
      simp only [mul_pow, div_pow, pow_succ d]
      field_simp
    _ ≤ c * (n / d) ^ (k + 1) * Real.log x ^ k := by
      rw [mul_assoc c]
      exact mul_le_mul_of_nonneg_right hfac (by positivity)

private lemma eventually_sq_lower (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (1 - ε) * (((k : ℝ) + 1) ^ 2 * (x : ℝ) ^ ((2 : ℝ) / (k + 1)) /
        (2 * Real.log x ^ ((2 * k : ℝ) / (k + 1)))) ≤ (maxLength k x : ℝ) ^ 2 / 2 := by
  by_cases hε₁ : ε < 1
  swap
  · exact Eventually.of_forall fun x =>
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans (by positivity)
  let d : ℝ := (k : ℝ) + 1
  let q : ℝ := 2 / d
  let c : ℝ := ((1 - ε)⁻¹) ^ q⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := div_pos (by norm_num) hd
  have hε₀ : 0 < 1 - ε := sub_pos.mpr hε₁
  have hc : 1 < c := Real.one_lt_rpow (one_lt_inv₀ hε₀ |>.2 (by linarith)) (inv_pos.mpr hq)
  filter_upwards [eventually_div_log_pow_le k hk hc] with x hx
  let n : ℝ := maxLength k x
  have hpow := Real.rpow_le_rpow (by positivity) hx hq.le
  change ((x : ℝ) / Real.log x ^ k) ^ q ≤ (c * (n / d) ^ (k + 1)) ^ q at hpow
  have hkq : (k : ℝ) * q = (2 * k : ℝ) / d := by dsimp [q]; ring
  have hdq : ((k + 1 : ℕ) : ℝ) * q = 2 := by
    rw [Nat.cast_add_one]
    change d * (2 / d) = 2
    field_simp
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
    hkq, Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (by positivity),
    ← Real.rpow_natCast_mul (by positivity), hdq, Real.rpow_two,
    Real.rpow_inv_rpow (by positivity) hq.ne'] at hpow
  change (1 - ε) * (d ^ 2 * (x : ℝ) ^ q / (2 * Real.log x ^ ((2 * k : ℝ) / d))) ≤ n ^ 2 / 2
  calc
    _ = ((1 - ε) * (d ^ 2 / 2)) * ((x : ℝ) ^ q / Real.log x ^ ((2 * k : ℝ) / d)) := by ring
    _ ≤ ((1 - ε) * (d ^ 2 / 2)) * ((1 - ε)⁻¹ * (n / d) ^ 2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by field_simp

end card_consecutivePrimePowerSums_ge

/-- **Lower bound for the number of sums of consecutive prime powers.** Let $p_1 < p_2 < \cdots$
be the primes and let $k > 1$ be a natural number. For a natural number $x$ let $s_k(x)$ be the
number of pairs $(\ell, m)$ of integers with $0 \le \ell < x$ and $1 \le m \le x$ such that
$p_{\ell+1}^k + \cdots + p_{\ell+m}^k \le x$, and let $M(x, k)$ be the largest $m \le x$ with
$p_1^k + \cdots + p_m^k \le x$. Then $M(x, k)^2 / 2 \le s_k(x)$ for every $x$, and for every
real $\varepsilon > 0$, for all sufficiently large $x$,
$(1 - \varepsilon) (k + 1)^2 x^{2/(k+1)} / \bigl(2 (\log x)^{2k/(k+1)}\bigr) \le M(x, k)^2 / 2$.

The finite bound strengthens the bound $\binom{M(x, k)}{2} \le s_k(x)$ printed in Theorem 2 of the
source: $s_k(x)$ counts all $\binom{M(x, k) + 1}{2}$ blocks $p_i^k + \cdots + p_j^k$ with
$1 \le i \le j \le M(x, k)$, singletons included, and
$\binom{M(x, k)}{2} \le M(x, k)^2 / 2 \le \binom{M(x, k) + 1}{2}$. The asymptotic bound is
one-sided. It amounts to saying that for every $\delta > 0$, for all sufficiently large $x$,
$M(x, k) \ge (1 - \delta) (k + 1) x^{1/(k+1)} / (\log x)^{k/(k+1)}$: one direction of the
asymptotic equivalence $M(x, k) \sim (k + 1) x^{1/(k+1)} / (\log x)^{k/(k+1)}$ of Lemma 2 of the
source, without the matching upper bound on $M(x, k)$.

Source: Cathal O'Sullivan, Jonathan P. Sorenson, and Aryn Stahl, *Algorithms and Bounds on the
Sums of Powers of Consecutive Primes*, INTEGERS 24 (2024), Article A4, Theorem 2
(`integers-2024-A4-thm-2`). -/
public theorem card_consecutivePrimePowerSums_ge (k : ℕ) (hk : 1 < k) :
    let s : ℕ → ℝ := fun x =>
      (((range x ×ˢ Icc 1 x).filter (fun lm =>
          ∑ i ∈ range lm.2, Nat.nth Nat.Prime (lm.1 + i) ^ k ≤ x)).card : ℝ)
    let M : ℕ → ℝ := fun x =>
      (Nat.findGreatest (fun m => ∑ i ∈ range m, Nat.nth Nat.Prime i ^ k ≤ x) x : ℝ)
    (∀ x : ℕ, M x ^ 2 / 2 ≤ s x) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
        (1 - ε) * (((k : ℝ) + 1) ^ 2 * (x : ℝ) ^ ((2 : ℝ) / (k + 1)) /
          (2 * Real.log x ^ ((2 * k : ℝ) / (k + 1)))) ≤ M x ^ 2 / 2 := by
  exact ⟨card_consecutivePrimePowerSums_ge.count_ge k,
    card_consecutivePrimePowerSums_ge.eventually_sq_lower k (by omega)⟩

end MetaMathlibExt
