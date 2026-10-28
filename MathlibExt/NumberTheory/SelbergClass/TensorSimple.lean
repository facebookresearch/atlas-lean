/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Primitive
public import MathlibExt.NumberTheory.SelbergClass.RankinSelberg
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Prime.Int
import MathlibExt.NumberTheory.SelbergClass.Factorization

/-!
# `⊗`-simple functions and primitive functions

A member `F` of the Selberg class is `⊗`-simple when its Rankin–Selberg square `F ⊗ F̄` has a
simple pole at `s = 1` and no other singularity on `Re s ≥ 1/2`. Near `s = 1⁺` the logarithm
`log |(F ⊗ F̄)(1 + δ)|` equals `∑_p |a(p)|² p^{-1-δ}` up to a bounded error, and by partial
summation this sum is governed by the asymptotics of `∑_{p ≤ x} |a(p)|²/p`. Under Selberg's
conjectures (a) and (b) the latter is `(∑ e_i²) log log x + O(1)` for `F = ∏ F_i^{e_i}`, so the
order of the pole of `F ⊗ F̄` at `1` is `∑ e_i²`, which equals `1` exactly when `F` is primitive.

## Main statements

* `SelbergClass.isTensorSimple_iff_isSelbergPrimitive`: assuming Selberg's conjectures, if
  `F ∈ 𝒮` and `F ⊗ F̄ ∈ 𝒮`, then `F` is `⊗`-simple if and only if `F` is primitive.
-/

open ArithmeticFunction Complex Filter Topology

@[expose] public section

namespace SelbergClass


/-- Comparing growth rates along arbitrarily large `L`. -/
private lemma le_of_forall_exists_gt_mul_le (m E C : ℝ)
    (h : ∀ M : ℝ, ∃ L > M, m * L ≤ E * L + C) : m ≤ E := by
  by_contra hlt
  push Not at hlt
  obtain ⟨L, hL, h⟩ := h ((|C| + 1) / (m - E))
  have hme : 0 < m - E := by linarith
  have h1 : |C| + 1 < (m - E) * L := by
    rw [gt_iff_lt, div_lt_iff₀ hme] at hL
    linarith
  nlinarith [le_abs_self C]

/-- The approach `δ → 0⁺` along `1 + δ` lands in the punctured neighbourhood of `1`. -/
private lemma tendsto_one_add_ofReal_nhdsGT :
    Filter.Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 1 {1}ᶜ) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ)) (nhds 0)
        (nhds ((1 : ℂ) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < δ from hδ))

/-- A meromorphic function of order `n` at `1` has `log ‖H (1 + δ)‖ = n log δ + O(1)`. -/
private lemma exists_abs_log_norm_sub_le_of_meromorphicOrderAt (H : ℂ → ℂ) (hm : MeromorphicAt H 1)
    (n : ℤ)
    (hn : meromorphicOrderAt H 1 = n) :
    ∃ C : ℝ, ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |Real.log ‖H (1 + (δ : ℂ))‖ - n * Real.log δ| ≤ C := by
  obtain ⟨g, hga, hg0, hev⟩ := (meromorphicOrderAt_eq_int_iff hm).1 hn
  have hg1 : 0 < ‖g 1‖ := norm_pos_iff.2 hg0
  have hcont : ∀ᶠ z in nhds (1 : ℂ), ‖g z - g 1‖ < ‖g 1‖ / 2 := by
    have := hga.continuousAt.tendsto
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 this) _ (by linarith)
  refine ⟨|Real.log (‖g 1‖ / 2)| + |Real.log (3 * ‖g 1‖ / 2)|, ?_⟩
  have h2 : ∀ᶠ z in nhdsWithin (1 : ℂ) {1}ᶜ,
      H z = (z - 1) ^ n • g z ∧ ‖g z - g 1‖ < ‖g 1‖ / 2 :=
    hev.and (nhdsWithin_le_nhds hcont)
  filter_upwards [tendsto_one_add_ofReal_nhdsGT.eventually h2, self_mem_nhdsWithin]
    with δ ⟨hH, hgz⟩ hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  have hlo : ‖g 1‖ / 2 < ‖g (1 + δ)‖ := by
    have := norm_sub_norm_le (g 1) (g (1 + δ))
    rw [norm_sub_rev] at this
    linarith
  have hhi : ‖g (1 + δ)‖ < 3 * ‖g 1‖ / 2 := by
    have := norm_le_norm_add_norm_sub' (g (1 + δ)) (g 1)
    linarith
  have hgpos : 0 < ‖g (1 + δ)‖ := by linarith
  have hnorm : ‖H (1 + δ)‖ = δ ^ n * ‖g (1 + δ)‖ := by
    rw [hH, smul_eq_mul, norm_mul, add_sub_cancel_left, norm_zpow, Complex.norm_real,
      Real.norm_of_nonneg hδ0.le]
  rw [hnorm, Real.log_mul (zpow_pos hδ0 n).ne' hgpos.ne', Real.log_zpow, add_sub_cancel_left]
  have l1 := Real.log_lt_log (by positivity) hlo
  have l2 := Real.log_lt_log hgpos hhi
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (‖g 1‖ / 2)), abs_nonneg (Real.log (3 * ‖g 1‖ / 2))]
  · linarith [le_abs_self (Real.log (3 * ‖g 1‖ / 2)), abs_nonneg (Real.log (‖g 1‖ / 2))]

/-- Abelian comparison: `∑_{n ≤ x} c n = E log log x + O(1)` gives
`E L + O(1) ≥ ∑ c n n^{-δ} ≥ e^{-1/2} E L - O(1)` with `L = -log δ`. -/
private lemma exists_tsum_rpow_bounds_of_isBigO_log_log (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n)
    (hc00 : c 0 = 0) (E : ℝ) (hE : 0 ≤ E)
    (hO : (fun x : ℝ => ∑ n ∈ Finset.Iic ⌊x⌋₊, c n - E * Real.log (Real.log x))
      =O[Filter.atTop] (fun _ => (1 : ℝ))) :
    ∃ C₁ C₂ : ℝ, ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Summable (fun n : ℕ => c n * (n : ℝ) ^ (-δ)) ∧
      ∑' n : ℕ, c n * (n : ℝ) ^ (-δ) ≤ E * (-Real.log δ) + C₁ ∧
      Real.exp (-(1 / 2)) * E * (-Real.log δ) - C₂ ≤ ∑' n : ℕ, c n * (n : ℝ) ^ (-δ) := by
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 hC
  set A : ℝ → ℝ := fun x => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), c n with hAdef
  have hI : ∀ m : ℕ, Finset.Iic m = Finset.range (m + 1) := fun m => by
    ext n; simp
  have hAb : ∀ x ≥ x0, |A x - E * Real.log (Real.log x)| ≤ C := by
    intro x hx
    have := hx0 x hx
    rw [norm_one, mul_one, Real.norm_eq_abs, hI] at this
    exact this
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hAb (max x0 0) (le_max_left _ _))
  set δ₁ : ℝ := min (1 / 2) (1 / (2 * (|x0| + 1))) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by norm_num) (by positivity)
  refine ⟨E * Real.log 2 + 3 * C, E * Real.log 2 + C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ₁0] with δ ⟨hδ0, hδlt⟩
  have hδhalf : δ < 1 / 2 := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδx : δ < 1 / (2 * (|x0| + 1)) := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hbig : ∀ t : ℝ, 1 / 2 ≤ t → x0 ≤ Real.exp (t / δ) := by
    intro t ht
    have h1 : |x0| + 1 ≤ t / δ := by
      rw [le_div_iff₀ hδ0]
      rw [lt_div_iff₀ (by positivity)] at hδx
      nlinarith [abs_nonneg x0]
    have h2 := Real.add_one_le_exp (t / δ)
    linarith [le_abs_self x0]
  have hll : ∀ t : ℝ, 0 < t →
      Real.log (Real.log (Real.exp (t / δ))) = Real.log t - Real.log δ := by
    intro t ht
    rw [Real.log_exp, Real.log_div ht.ne' hδ0.ne']
  have hw : ∀ n : ℕ, 0 < n → (n : ℝ) ^ (-δ) = Real.exp (-(δ * Real.log n)) := by
    intro n hn
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
    ring_nf
  have hwnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-δ) := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hterm0 : ∀ n, 0 ≤ c n * (n : ℝ) ^ (-δ) := fun n => mul_nonneg (hc0 n) (hwnn n)
  set Y : ℕ → ℝ := fun j => Real.exp ((2 : ℝ) ^ j / δ) with hY
  have hYmono : ∀ j, Y j ≤ Y (j + 1) := by
    intro j
    simp only [hY]
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ hδ0.le)
    rw [pow_succ]
    have : (0 : ℝ) ≤ 2 ^ j := by positivity
    linarith
  have hYbig : ∀ j, x0 ≤ Y j := fun j => hbig _ (by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith)
  have hYll : ∀ j : ℕ, Real.log (Real.log (Y j)) = j * Real.log 2 - Real.log δ := by
    intro j
    rw [hY, hll _ (by positivity), Real.log_pow]
  have hK0 : 0 ≤ E * Real.log 2 + 2 * C := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hblock : ∀ N : ℕ, ∑ n ∈ Finset.range (⌊Y N⌋₊ + 1), c n * (n : ℝ) ^ (-δ) ≤
      A (Y 0) + (E * Real.log 2 + 2 * C) * (1 - (1 / 2) ^ N) := by
    intro N
    induction N with
    | zero =>
      simp only [pow_zero, sub_self, mul_zero, add_zero, hAdef]
      refine Finset.sum_le_sum (fun n _ => ?_)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hc00]
      · rw [hw n hn]
        have : Real.exp (-(δ * Real.log n)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
          nlinarith
        nlinarith [hc0 n]
    | succ N ih =>
      have hfl : ⌊Y N⌋₊ + 1 ≤ ⌊Y (N + 1)⌋₊ + 1 := by
        have := Nat.floor_le_floor (hYmono N); omega
      rw [← Finset.sum_range_add_sum_Ico _ hfl]
      have hIco : ∑ n ∈ Finset.Ico (⌊Y N⌋₊ + 1) (⌊Y (N + 1)⌋₊ + 1), c n * (n : ℝ) ^ (-δ) ≤
          Real.exp (-(2 : ℝ) ^ N) *
            ∑ n ∈ Finset.Ico (⌊Y N⌋₊ + 1) (⌊Y (N + 1)⌋₊ + 1), c n := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : ⌊Y N⌋₊ + 1 ≤ n := (Finset.mem_Ico.1 hn).1
        have hnY : Y N < n := by
          have := Nat.lt_floor_add_one (Y N)
          have h2 : ((⌊Y N⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
          push_cast at h2
          linarith
        have hYpos : 0 < Y N := Real.exp_pos _
        have hn0 : 0 < n := by
          have : (0 : ℝ) < n := by linarith
          exact_mod_cast this
        rw [hw n hn0, mul_comm]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hc0 n)
        have hlog : (2 : ℝ) ^ N / δ < Real.log n := by
          rw [Real.lt_log_iff_exp_lt (by linarith)]
          exact hnY
        rw [div_lt_iff₀ hδ0] at hlog
        linarith
      have hdiff : ∑ n ∈ Finset.Ico (⌊Y N⌋₊ + 1) (⌊Y (N + 1)⌋₊ + 1), c n =
          A (Y (N + 1)) - A (Y N) := by
        simp only [hAdef]
        rw [← Finset.sum_range_add_sum_Ico _ hfl]
        ring
      have hdb : A (Y (N + 1)) - A (Y N) ≤ E * Real.log 2 + 2 * C := by
        have h1 := hAb _ (hYbig (N + 1))
        have h2 := hAb _ (hYbig N)
        rw [hYll] at h1 h2
        rw [abs_le] at h1 h2
        push_cast at h1 h2
        nlinarith
      have hdnn : 0 ≤ A (Y (N + 1)) - A (Y N) := by
        rw [← hdiff]; exact Finset.sum_nonneg (fun n _ => hc0 n)
      have hexp : Real.exp (-(2 : ℝ) ^ N) ≤ (1 / 2) ^ (N + 1) := by
        have h1 : ((N : ℝ) + 1) ≤ 2 ^ N := by
          have := Nat.lt_two_pow_self (n := N)
          exact_mod_cast this
        calc Real.exp (-(2 : ℝ) ^ N) ≤ Real.exp (-((N : ℝ) + 1)) :=
              Real.exp_le_exp.2 (by linarith)
          _ = (Real.exp (-1)) ^ (N + 1) := by
              rw [← Real.exp_nat_mul]; push_cast; ring_nf
          _ ≤ (1 / 2) ^ (N + 1) := by
              refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ _
              have := Real.exp_neg_one_lt_d9
              linarith
      rw [hdiff] at hIco
      calc _ ≤ A (Y 0) + (E * Real.log 2 + 2 * C) * (1 - (1 / 2) ^ N) +
            Real.exp (-(2 : ℝ) ^ N) * (A (Y (N + 1)) - A (Y N)) := add_le_add ih hIco
        _ ≤ A (Y 0) + (E * Real.log 2 + 2 * C) * (1 - (1 / 2) ^ N) +
            (1 / 2) ^ (N + 1) * (E * Real.log 2 + 2 * C) := by
            gcongr
        _ = A (Y 0) + (E * Real.log 2 + 2 * C) * (1 - (1 / 2) ^ (N + 1)) := by ring
  have hA0 : A (Y 0) ≤ E * (-Real.log δ) + C := by
    have h := hAb _ (hYbig 0)
    rw [hYll, abs_le] at h
    push_cast at h
    linarith
  have hpart : ∀ M : ℕ, ∑ n ∈ Finset.range M, c n * (n : ℝ) ^ (-δ) ≤
      E * (-Real.log δ) + (E * Real.log 2 + 3 * C) := by
    intro M
    have hMY : M ≤ ⌊Y M⌋₊ + 1 := by
      have : (M : ℝ) ≤ Y M := by
        have h1 : (M : ℝ) + 1 ≤ 2 ^ M := by
          have := Nat.lt_two_pow_self (n := M)
          exact_mod_cast this
        have h2 : (2 : ℝ) ^ M ≤ 2 ^ M / δ := by
          rw [le_div_iff₀ hδ0]
          have : (0 : ℝ) ≤ 2 ^ M := by positivity
          nlinarith
        have h3 := Real.add_one_le_exp ((2 : ℝ) ^ M / δ)
        simp only [hY]
        linarith
      have := Nat.le_floor this
      omega
    calc ∑ n ∈ Finset.range M, c n * (n : ℝ) ^ (-δ)
        ≤ ∑ n ∈ Finset.range (⌊Y M⌋₊ + 1), c n * (n : ℝ) ^ (-δ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hMY)
            (fun i _ _ => hterm0 i)
      _ ≤ A (Y 0) + (E * Real.log 2 + 2 * C) * (1 - (1 / 2) ^ M) := hblock M
      _ ≤ A (Y 0) + (E * Real.log 2 + 2 * C) * 1 := by
          gcongr
          have : (0 : ℝ) ≤ (1 / 2) ^ M := by positivity
          linarith
      _ ≤ E * (-Real.log δ) + (E * Real.log 2 + 3 * C) := by linarith
  have hsum : Summable (fun n : ℕ => c n * (n : ℝ) ^ (-δ)) :=
    summable_of_sum_range_le hterm0 hpart
  refine ⟨hsum, Real.tsum_le_of_sum_range_le hterm0 hpart, ?_⟩
  set Z : ℝ := Real.exp ((1 / 2) / δ) with hZ
  have hZbig : x0 ≤ Z := hbig _ le_rfl
  have hZll : Real.log (Real.log Z) = Real.log (1 / 2) - Real.log δ := hll _ (by norm_num)
  have hZA := hAb _ hZbig
  rw [hZll, abs_le] at hZA
  have hlow : Real.exp (-(1 / 2)) * A Z ≤
      ∑ n ∈ Finset.range (⌊Z⌋₊ + 1), c n * (n : ℝ) ^ (-δ) := by
    simp only [hAdef]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hc00]
    · rw [hw n hn0, mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc0 n)
      have hnZ : (n : ℝ) ≤ Z := by
        have h1 : n ≤ ⌊Z⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
        exact (Nat.cast_le.2 h1).trans (Nat.floor_le (Real.exp_pos _).le)
      have hlog : Real.log n ≤ (1 / 2) / δ := by
        rw [Real.log_le_iff_le_exp (by exact_mod_cast hn0)]
        exact hnZ
      rw [le_div_iff₀ hδ0] at hlog
      linarith
  have hle := hlow.trans (hsum.sum_le_tsum _ (fun i _ => hterm0 i))
  have hl2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [hl2] at hZA
  have he0 : 0 < Real.exp (-(1 / 2)) := Real.exp_pos _
  have he1 : Real.exp (-(1 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hZA.1 he0.le,
    mul_nonneg (sub_nonneg.2 he1) (add_nonneg (mul_nonneg hE hlog2) hC0)]

/-- The proper prime-power part of `∑ k |b (p^k)|² / p^k` converges. -/
private lemma summable_tensorLog_properPrimePow (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass)
    (b : ℕ → ℂ)
    (hb : IsEulerLog a b) :
    Summable (fun n : ℕ => if ¬ n.Prime ∧ IsPrimePow n then
      (n.factorization n.minFac : ℝ) * ‖b n‖ ^ 2 / n else 0) := by
  obtain ⟨ha1, -, ⟨b₀, θ, hθ, hb₀, C₀, hC₀⟩, haO⟩ := id ha
  have haS := fun (s : ℂ) (hs : 1 < s.re) => LSeriesSummable_of_forall_norm_le_mul_rpow haO hs
  have hbb : b₀ = b := IsEulerLog.unique ha1 haS hb₀ hb
  subst hbb
  obtain ⟨c₁, hc₁⟩ := haO (1 / 8) (by norm_num)
  have hram := fun (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k) =>
    hb.norm_apply_prime_pow_le ha1 haS (fun n _ => hc₁ n) hp hk
  have hc1 : 1 ≤ c₁ := by
    have := hc₁ 1
    simpa [ha1] using this
  set f : ℕ → ℝ := fun n => if ¬ n.Prime ∧ IsPrimePow n then
      (n.factorization n.minFac : ℝ) * ‖b₀ n‖ ^ 2 / n else 0 with hf
  set ψ : {p : ℕ // p.Prime} × ℕ → ℕ := fun q => q.1.1 ^ (q.2 + 2) with hψ
  have hinj : Function.Injective ψ := by
    rintro ⟨⟨p, hp⟩, i⟩ ⟨⟨q, hq⟩, j⟩ h
    have h' : p ^ ((i + 1) + 1) = q ^ ((j + 1) + 1) := h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hp hq h'
    subst h1
    simp only [Prod.mk.injEq, true_and]
    omega
  have hzero : ∀ x ∉ Set.range ψ, f x = 0 := by
    intro n hn
    simp only [hf]
    rw [ite_eq_right]
    rintro ⟨hnp, hpp⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    exact hn ⟨(⟨p, hp⟩, k - 2), by simp only [hψ]; congr 1; omega⟩
  refine (hinj.summable_iff hzero).1 ?_
  set D : ℝ := 1 + c₁ with hD
  have hD2 : 2 ≤ D := by linarith
  set p0 : ℝ := max ((D ^ 2) ^ 8) 256 with hp0
  set ρ : ℝ := (2 : ℝ) ^ (2 * θ - 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set r : ℝ := max ρ (1 / 2) with hr
  have hr0 : 0 ≤ r := le_max_of_le_right (by norm_num)
  have hr1 : r < 1 := max_lt hρ1 (by norm_num)
  set M : ℝ := C₀ ^ 2 * p0 ^ 2 + 1 with hM
  have hP : Summable (fun p : {p : ℕ // p.Prime} => (((p : ℕ) : ℝ) ^ ((1 : ℝ) / 8))⁻¹ ^ 10) := by
    have h1 : Summable (fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))) :=
      (Real.summable_nat_rpow.2 (by norm_num)).comp_injective Subtype.val_injective
    refine h1.congr (fun p => ?_)
    rw [inv_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num
  have hK : Summable (fun j : ℕ => ((j : ℝ) + 2) * r ^ j) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h2 := summable_geometric_of_lt_one hr0 hr1
    refine (h1.add (h2.mul_left 2)).congr (fun j => ?_)
    simp only [pow_one]
    ring
  have h3 := (hP.mul_left M).mul_of_nonneg hK (fun p => by positivity) (fun j => by positivity)
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) h3
  · simp only [Function.comp, hf]
    split_ifs <;> positivity
  · obtain ⟨⟨p, hp⟩, j⟩ := q
    simp only [Function.comp, hψ, hf]
    have hk0 : j + 2 ≠ 0 := by omega
    rw [ite_eq_left ⟨Nat.Prime.not_prime_pow (by omega), hp.isPrimePow.pow hk0⟩,
      hp.pow_minFac hk0, hp.factorization_pow, Finsupp.single_eq_same]
    have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    set y : ℝ := (p : ℝ) ^ ((1 : ℝ) / 8) with hy
    have hy0 : 0 < y := by positivity
    have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by norm_num)
    have hy8 : y ^ 8 = (p : ℝ) := by
      rw [hy, ← Real.rpow_mul_natCast (by linarith)]
      norm_num
    have hQ : (0 : ℝ) < (p : ℝ) ^ (j + 2) := by positivity
    have key : ‖b₀ (p ^ (j + 2))‖ ^ 2 / (p : ℝ) ^ (j + 2) ≤ M * y⁻¹ ^ 10 * r ^ j := by
      by_cases hsmall : (p : ℝ) < p0
      · have hb1 : ‖b₀ (p ^ (j + 2))‖ ≤ C₀ * ((p : ℝ) ^ (j + 2)) ^ θ := by
          have := hC₀ (p ^ (j + 2))
          push_cast at this
          exact this
        have hsq : ‖b₀ (p ^ (j + 2))‖ ^ 2 ≤ C₀ ^ 2 * (((p : ℝ) ^ (j + 2)) ^ θ) ^ 2 := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) hb1 2
        have hrw : (((p : ℝ) ^ (j + 2)) ^ θ) ^ 2 / (p : ℝ) ^ (j + 2) =
            ((p : ℝ) ^ (j + 2)) ^ (θ * 2 - 1) := by
          rw [← Real.rpow_mul_natCast hQ.le, Real.rpow_sub_one hQ.ne']
          norm_num
        have hcmp : ((p : ℝ) ^ (j + 2)) ^ (θ * 2 - 1) ≤ r ^ j := by
          calc ((p : ℝ) ^ (j + 2)) ^ (θ * 2 - 1) ≤ ((2 : ℝ) ^ (j + 2)) ^ (θ * 2 - 1) :=
                Real.rpow_le_rpow_of_nonpos (by positivity)
                  (pow_le_pow_left₀ (by norm_num) hP2 _) (by linarith)
            _ = ρ ^ (j + 2) := by
                rw [← Real.rpow_pow_comm (by norm_num), hρ]
                ring_nf
            _ ≤ ρ ^ j := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
            _ ≤ r ^ j := pow_le_pow_left₀ hρ0 (le_max_left _ _) _
        have hC : C₀ ^ 2 ≤ M * y⁻¹ ^ 10 := by
          have hy10 : y ^ 10 ≤ (p : ℝ) ^ 2 := by
            calc y ^ 10 ≤ y ^ 16 := pow_le_pow_right₀ hy1 (by norm_num)
              _ = (y ^ 8) ^ 2 := by ring
              _ = (p : ℝ) ^ 2 := by rw [hy8]
          have hp02 : (p : ℝ) ^ 2 ≤ p0 ^ 2 := pow_le_pow_left₀ (by linarith) hsmall.le 2
          rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          have : 0 ≤ C₀ ^ 2 := sq_nonneg _
          nlinarith
        calc ‖b₀ (p ^ (j + 2))‖ ^ 2 / (p : ℝ) ^ (j + 2)
            ≤ C₀ ^ 2 * (((p : ℝ) ^ (j + 2)) ^ θ) ^ 2 / (p : ℝ) ^ (j + 2) :=
              div_le_div_of_nonneg_right hsq hQ.le
          _ = C₀ ^ 2 * ((p : ℝ) ^ (j + 2)) ^ (θ * 2 - 1) := by rw [mul_div_assoc, hrw]
          _ ≤ (M * y⁻¹ ^ 10) * r ^ j :=
              mul_le_mul hC hcmp (Real.rpow_nonneg hQ.le _) (by positivity)
      · push Not at hsmall
        have hDy : D ^ 2 ≤ y := by
          refine (pow_le_pow_iff_left₀ (by positivity) hy0.le (by norm_num : (8 : ℕ) ≠ 0)).1 ?_
          rw [hy8]
          exact (le_max_left _ _).trans hsmall
        have hy2 : 2 ≤ y := by
          refine (pow_le_pow_iff_left₀ (by norm_num) hy0.le (by norm_num : (8 : ℕ) ≠ 0)).1 ?_
          rw [hy8]
          have : (256 : ℝ) ≤ p0 := le_max_right _ _
          linarith [show (2 : ℝ) ^ 8 = 256 by norm_num]
        have hb1 := hram p hp (j + 2) (by omega)
        rw [show ((j + 2 : ℕ) : ℝ) * (1 / 8) = (1 / 8) * ((j + 2 : ℕ) : ℝ) from mul_comm _ _,
          Real.rpow_mul_natCast (by linarith), ← hy] at hb1
        have hb2 : ‖b₀ (p ^ (j + 2))‖ ≤ D ^ (j + 2) * y ^ (j + 2) := by
          refine hb1.trans ?_
          have hD1 : 1 ≤ D ^ (j + 2) := one_le_pow₀ (by linarith)
          have hk1 : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
            have : 1 ≤ j + 2 := by omega
            exact_mod_cast this
          calc ((1 + c₁) ^ (j + 2) - 1) * y ^ (j + 2) / ((j + 2 : ℕ) : ℝ)
              ≤ ((1 + c₁) ^ (j + 2) - 1) * y ^ (j + 2) :=
                div_le_self (mul_nonneg (by linarith) (by positivity)) hk1
            _ ≤ D ^ (j + 2) * y ^ (j + 2) := by
                gcongr
                linarith
        have hsq : ‖b₀ (p ^ (j + 2))‖ ^ 2 ≤ (y ^ 3) ^ (j + 2) := by
          calc ‖b₀ (p ^ (j + 2))‖ ^ 2 ≤ (D ^ (j + 2) * y ^ (j + 2)) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) hb2 2
            _ = (D ^ 2 * y ^ 2) ^ (j + 2) := by ring_nf
            _ ≤ (y * y ^ 2) ^ (j + 2) := by gcongr
            _ = (y ^ 3) ^ (j + 2) := by ring
        have hPk : (p : ℝ) ^ (j + 2) = (y ^ 8) ^ (j + 2) := by rw [hy8]
        have hinv5 : y⁻¹ ^ 5 ≤ 1 / 2 := by
          rw [inv_pow, inv_le_comm₀ (by positivity) (by norm_num)]
          have : (2 : ℝ) ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ (by norm_num) hy2 5
          norm_num at this ⊢
          linarith
        have hM1 : 1 ≤ M := by
          have : 0 ≤ C₀ ^ 2 * p0 ^ 2 := by positivity
          linarith
        calc ‖b₀ (p ^ (j + 2))‖ ^ 2 / (p : ℝ) ^ (j + 2)
            ≤ (y ^ 3) ^ (j + 2) / (y ^ 8) ^ (j + 2) := by
              rw [hPk]
              exact div_le_div_of_nonneg_right hsq (by positivity)
          _ = y⁻¹ ^ 10 * (y⁻¹ ^ 5) ^ j := by
              rw [div_eq_iff (by positivity)]
              have e : y⁻¹ ^ 10 * (y⁻¹ ^ 5) ^ j * (y ^ 8) ^ (j + 2) =
                  (y⁻¹ * y) ^ (5 * j + 10) * (y ^ 3) ^ (j + 2) := by ring
              rw [e, inv_mul_cancel₀ hy0.ne', one_pow, one_mul]
          _ ≤ y⁻¹ ^ 10 * (1 / 2) ^ j := by gcongr
          _ ≤ M * y⁻¹ ^ 10 * r ^ j := by
              have h1 : (1 / 2 : ℝ) ^ j ≤ r ^ j :=
                pow_le_pow_left₀ (by norm_num) (le_max_right _ _) _
              have h2 : 0 ≤ y⁻¹ ^ 10 := by positivity
              calc y⁻¹ ^ 10 * (1 / 2) ^ j ≤ 1 * y⁻¹ ^ 10 * r ^ j := by
                    rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 h2
                _ ≤ M * y⁻¹ ^ 10 * r ^ j := by gcongr
    push_cast
    rw [mul_div_assoc]
    calc ((j : ℝ) + 2) * (‖b₀ (p ^ (j + 2))‖ ^ 2 / (p : ℝ) ^ (j + 2))
        ≤ ((j : ℝ) + 2) * (M * y⁻¹ ^ 10 * r ^ j) := by gcongr
      _ = M * y⁻¹ ^ 10 * (((j : ℝ) + 2) * r ^ j) := by ring


/-- On `σ = 1 + δ`, `log |F ⊗ F̄|` is the prime sum `∑ |a p|² p^{-1-δ}` plus a bounded,
nonnegative prime-power part. -/
private lemma exists_log_norm_tensor_eq_tsum_add (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass)
    (b : ℕ → ℂ)
    (hb : IsEulerLog a b) {c : ArithmeticFunction ℂ}
    (hcL : IsEulerLog c (tensorLog b (fun n => starRingEnd ℂ (b n)))) :
    ∃ K : ℝ, ∀ δ : ℝ, 0 < δ → ∃ P : ℝ,
      Real.log ‖tensor b (fun n => starRingEnd ℂ (b n)) (1 + (δ : ℂ))‖ =
        ∑' n : ℕ, (if n.Prime then ‖a n‖ ^ 2 / n else 0) * (n : ℝ) ^ (-δ) + P ∧
      0 ≤ P ∧ P ≤ K := by
  obtain ⟨ha1, -, -, haO⟩ := id ha
  have haS := fun (s : ℂ) (hs : 1 < s.re) => LSeriesSummable_of_forall_norm_le_mul_rpow haO hs
  set bb : ℕ → ℂ := fun n => starRingEnd ℂ (b n) with hbb
  set τ : ℕ → ℝ := fun n =>
    if IsPrimePow n then (n.factorization n.minFac : ℝ) * ‖b n‖ ^ 2 else 0 with hτ
  have hτc : tensorLog b bb = fun n => ((τ n : ℝ) : ℂ) := by
    funext n
    simp only [tensorLog, hτ, hbb]
    split_ifs
    · rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · simp
  have hτ0 : ∀ n, 0 ≤ τ n := fun n => by
    simp only [hτ]
    split_ifs <;> positivity
  set cpr : ℕ → ℝ := fun n => if n.Prime then ‖a n‖ ^ 2 / n else 0 with hcpr
  set Pt : ℝ → ℕ → ℝ := fun δ n =>
    if ¬ n.Prime ∧ IsPrimePow n then τ n / (n : ℝ) ^ (1 + δ) else 0 with hPt
  set Kt : ℕ → ℝ := fun n => if ¬ n.Prime ∧ IsPrimePow n then
    (n.factorization n.minFac : ℝ) * ‖b n‖ ^ 2 / n else 0 with hKt
  have hKs : Summable Kt := summable_tensorLog_properPrimePow a ha b hb
  refine ⟨∑' n, Kt n, fun δ hδ => ⟨∑' n, Pt δ n, ?_⟩⟩
  have hs : 1 < ((1 : ℂ) + (δ : ℂ)).re := by simp; linarith
  have hsum := (hcL.2 _ hs).1
  have hterm : ∀ n : ℕ, LSeries.term (fun n => ((τ n : ℝ) : ℂ)) ((1 : ℂ) + (δ : ℂ)) n =
      ((τ n / (n : ℝ) ^ (1 + δ) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hτ]
    · rw [LSeries.term_of_ne_zero hn.ne',
        show (1 : ℂ) + (δ : ℂ) = ((1 + δ : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      ring
  have hreal : Summable (fun n : ℕ => τ n / (n : ℝ) ^ (1 + δ)) := by
    have h := hsum
    rw [hτc] at h
    unfold LSeriesSummable at h
    rw [show LSeries.term (fun n => ((τ n : ℝ) : ℂ)) ((1 : ℂ) + (δ : ℂ)) =
      fun n => ((τ n / (n : ℝ) ^ (1 + δ) : ℝ) : ℂ) from funext hterm] at h
    exact Complex.summable_ofReal.1 h
  have hL : LSeries (tensorLog b bb) ((1 : ℂ) + (δ : ℂ)) =
      ((∑' n : ℕ, τ n / (n : ℝ) ^ (1 + δ) : ℝ) : ℂ) := by
    rw [hτc, LSeries]
    simp_rw [hterm]
    rw [Complex.ofReal_tsum]
  have hnorm : Real.log ‖tensor b bb (1 + (δ : ℂ))‖ =
      ∑' n : ℕ, τ n / (n : ℝ) ^ (1 + δ) := by
    rw [tensor, hL, Complex.norm_exp_ofReal, Real.log_exp]
  have hsplit : ∀ n, τ n / (n : ℝ) ^ (1 + δ) = cpr n * (n : ℝ) ^ (-δ) + Pt δ n := by
    intro n
    simp only [hcpr, hPt]
    by_cases hp : n.Prime
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hτp : τ n = ‖a n‖ ^ 2 := by
        simp only [hτ]
        rw [ite_eq_left hp.isPrimePow, hp.minFac_eq, hp.factorization_self,
          hb.apply_prime ha1 haS hp]
        simp
      rw [ite_eq_left hp, ite_eq_right (fun h => h.1 hp), add_zero, hτp, Real.rpow_add hn0,
        Real.rpow_one,
        Real.rpow_neg hn0.le]
      field_simp
    · rw [ite_eq_right hp, zero_mul, zero_add]
      by_cases hpp : IsPrimePow n
      · rw [ite_eq_left ⟨hp, hpp⟩]
      · rw [ite_eq_right (fun h => hpp h.2)]
        simp [hτ, hpp]
  have hS0 : ∀ n, 0 ≤ cpr n * (n : ℝ) ^ (-δ) := fun n =>
    mul_nonneg (by simp only [hcpr]; split_ifs <;> positivity)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hP0 : ∀ n, 0 ≤ Pt δ n := fun n => by
    simp only [hPt]
    split_ifs
    · exact div_nonneg (hτ0 n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact le_rfl
  have hSs : Summable (fun n => cpr n * (n : ℝ) ^ (-δ)) :=
    Summable.of_nonneg_of_le hS0 (fun n => by rw [hsplit n]; linarith [hP0 n]) hreal
  have hPs : Summable (Pt δ) :=
    Summable.of_nonneg_of_le hP0 (fun n => by rw [hsplit n]; linarith [hS0 n]) hreal
  refine ⟨?_, tsum_nonneg hP0, ?_⟩
  · rw [hnorm, ← Summable.tsum_add hSs hPs]
    exact tsum_congr hsplit
  · refine Summable.tsum_le_tsum (fun n => ?_) hPs hKs
    simp only [hPt, hKt]
    split_ifs with h
    · have hτn : τ n = (n.factorization n.minFac : ℝ) * ‖b n‖ ^ 2 := by
        simp only [hτ]
        rw [ite_eq_left h.2]
      rw [hτn]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.2.one_lt.le
      refine div_le_div_of_nonneg_left (by positivity) (by linarith) ?_
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · exact le_rfl

/-- **`⊗`-simple functions are the primitive ones.** Assuming Selberg's conjectures (a) and
(b), if `F ∈ 𝒮` and `F ⊗ F̄ ∈ 𝒮`, then `F` is `⊗`-simple if and only if `F` is primitive. -/
theorem isTensorSimple_iff_isSelbergPrimitive (hA : ConjectureA) (hB : ConjectureB)
    (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (b : ℕ → ℂ) (hb : IsEulerLog a b)
    (hab : ∃ c ∈ selbergClass, IsEulerLog c (tensorLog b (fun n => starRingEnd ℂ (b n)))) :
    IsTensorSimple a ↔ IsSelbergPrimitive a := by
  classical
  obtain ⟨ha1, -, -, haO⟩ := id ha
  have haS := fun (s : ℂ) (hs : 1 < s.re) => LSeriesSummable_of_forall_norm_le_mul_rpow haO hs
  obtain ⟨c, hcS, hcL⟩ := hab
  obtain ⟨K, key⟩ := exists_log_norm_tensor_eq_tsum_add a ha b hb hcL
  set bb : ℕ → ℂ := fun n => starRingEnd ℂ (b n) with hbb
  set cpr : ℕ → ℝ := fun n => if n.Prime then ‖a n‖ ^ 2 / n else 0 with hcpr
  have hAbelOf : ∀ E : ℝ, 0 ≤ E →
      (fun x : ℝ => (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊x⌋₊), ‖a p‖ ^ 2 / (p : ℝ))
        - E * Real.log (Real.log x)) =O[Filter.atTop] (fun _ => (1 : ℝ)) →
      ∃ C₁ C₂ : ℝ, ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        Summable (fun n : ℕ => cpr n * (n : ℝ) ^ (-δ)) ∧
        ∑' n : ℕ, cpr n * (n : ℝ) ^ (-δ) ≤ E * (-Real.log δ) + C₁ ∧
        Real.exp (-(1 / 2)) * E * (-Real.log δ) - C₂ ≤ ∑' n : ℕ, cpr n * (n : ℝ) ^ (-δ) := by
    intro E hE hO
    refine exists_tsum_rpow_bounds_of_isBigO_log_log cpr
      (fun n => by simp only [hcpr]; split_ifs <;> positivity)
      (by simp [hcpr, Nat.not_prime_zero]) E hE (hO.congr_left (fun x => ?_))
    simp only [hcpr, Finset.sum_filter]
  have hlarge : ∀ M : ℝ, ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), M < -Real.log δ :=
    fun M => (Real.tendsto_log_nhdsGT_zero.eventually (Filter.eventually_lt_atBot (-M))).mono
      (fun δ h => by linarith)
  have combine : ∀ (H : ℂ → ℂ) (m E C₁ C₂ C₃ : ℝ),
      (∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        H (1 + (δ : ℂ)) = tensor b bb (1 + (δ : ℂ))) →
      (∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |Real.log ‖H (1 + (δ : ℂ))‖ - m * (-Real.log δ)| ≤ C₃) →
      (∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        Summable (fun n : ℕ => cpr n * (n : ℝ) ^ (-δ)) ∧
        ∑' n : ℕ, cpr n * (n : ℝ) ^ (-δ) ≤ E * (-Real.log δ) + C₁ ∧
        Real.exp (-(1 / 2)) * E * (-Real.log δ) - C₂ ≤ ∑' n : ℕ, cpr n * (n : ℝ) ^ (-δ)) →
      m ≤ E ∧ Real.exp (-(1 / 2)) * E ≤ m := by
    intro H m E C₁ C₂ C₃ hHe hG hS
    have hall := hHe.and (hG.and (hS.and eventually_mem_nhdsWithin))
    constructor
    · refine le_of_forall_exists_gt_mul_le m E (C₁ + K + C₃) (fun M => ?_)
      obtain ⟨δ, ⟨hH, hg, ⟨-, hup, -⟩, hδ⟩, hM⟩ := (hall.and (hlarge M)).exists
      obtain ⟨P, k1, k2, k3⟩ := key δ hδ
      refine ⟨-Real.log δ, hM, ?_⟩
      rw [hH, k1, abs_le] at hg
      linarith [hg.1]
    · refine le_of_forall_exists_gt_mul_le (Real.exp (-(1 / 2)) * E) m (C₂ + C₃) (fun M => ?_)
      obtain ⟨δ, ⟨hH, hg, ⟨-, -, hlo⟩, hδ⟩, hM⟩ := (hall.and (hlarge M)).exists
      obtain ⟨P, k1, k2, k3⟩ := key δ hδ
      refine ⟨-Real.log δ, hM, ?_⟩
      rw [hH, k1, abs_le] at hg
      linarith [hg.2]
  constructor
  · -- `⊗`-simple implies primitive
    rintro ⟨-, b', hb', H, hH, -, hHord⟩
    have hbb' : b' = b := IsEulerLog.unique ha1 haS hb' hb
    rw [hbb'] at hH
    have hHm : MeromorphicAt H 1 := by
      by_contra hc
      rw [meromorphicOrderAt, dite_eq_right hc] at hHord
      exact absurd hHord (by decide)
    obtain ⟨C₃, hC₃⟩ :=
      exists_abs_log_norm_sub_le_of_meromorphicOrderAt H hHm (-1) (by rw [hHord]; rfl)
    have hHe : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        H (1 + (δ : ℂ)) = tensor b bb (1 + (δ : ℂ)) := by
      filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      exact hH _ (by simpa using (show (0 : ℝ) < δ from hδ))
    obtain ⟨l, hl, hlprod⟩ : ∃ l : Multiset (ArithmeticFunction ℂ),
        (∀ g ∈ l, IsSelbergPrimitive g) ∧ l.prod = a := by
      by_cases h1 : a = 1
      · exact ⟨0, by simp, by simp [h1]⟩
      · exact exists_multiset_prod_eq ha h1
    have hfac : a = ∏ g ∈ l.toFinset, g ^ (l.count g) := by
      rw [← hlprod, Finset.prod_multiset_count]
    have hO := sum_prime_norm_sq_div_sub_isBigO_of_eq_prod_pow hA hB (s := l.toFinset)
      (e := fun g => l.count g) (fun g hg => hl g (Multiset.mem_toFinset.1 hg)) hfac
    set N : ℕ := ∑ g ∈ l.toFinset, l.count g ^ 2 with hN
    have hEN : (∑ g ∈ l.toFinset, ((l.count g : ℕ) : ℝ) ^ 2) = (N : ℝ) := by
      rw [hN]
      push_cast
      rfl
    beta_reduce at hO
    rw [hEN] at hO
    obtain ⟨C₁, C₂, hab'⟩ := hAbelOf N (Nat.cast_nonneg _) hO
    have hG : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |Real.log ‖H (1 + (δ : ℂ))‖ - (1 : ℝ) * (-Real.log δ)| ≤ C₃ :=
      hC₃.mono fun δ h => by
        convert h using 3
        push_cast
        ring
    obtain ⟨h1, h2⟩ := combine H 1 N C₁ C₂ C₃ hHe hG hab'
    have hN1 : N = 1 := by
      have i1 : 1 ≤ N := by exact_mod_cast h1
      have he : 1 / 2 < Real.exp (-(1 / 2)) := by
        have := Real.add_one_lt_exp (show (-(1 / 2) : ℝ) ≠ 0 by norm_num)
        linarith
      have i2 : N < 2 := by
        by_contra hc
        push Not at hc
        have : (2 : ℝ) ≤ N := by exact_mod_cast hc
        nlinarith
      omega
    have hcard : Multiset.card l = 1 := by
      have hle : Multiset.card l ≤ N := by
        rw [← Multiset.toFinset_sum_count_eq, hN]
        exact Finset.sum_le_sum (fun g _ => Nat.le_self_pow (by norm_num) _)
      have hne : l ≠ 0 := by
        rintro rfl
        simp at hN
        omega
      have := Multiset.card_pos.2 hne
      omega
    obtain ⟨g, rfl⟩ := Multiset.card_eq_one.1 hcard
    rw [← hlprod, Multiset.prod_singleton]
    exact hl g (Multiset.mem_singleton_self g)
  · -- primitive implies `⊗`-simple
    intro hprim
    obtain ⟨-, ⟨Fc, hFc, -, -⟩, -⟩ := id hcS
    have hFm := SelbergClass.meromorphicAt_one hcS hFc
    have hFeq : ∀ s : ℂ, 1 < s.re → Fc s = tensor b bb s := fun s hs => by
      rw [hFc.1 s hs, (hcL.2 s hs).2]
      rfl
    have hFe : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        Fc (1 + (δ : ℂ)) = tensor b bb (1 + (δ : ℂ)) := by
      filter_upwards [eventually_mem_nhdsWithin] with δ hδ
      exact hFeq _ (by simpa using (show (0 : ℝ) < δ from hδ))
    have hne : meromorphicOrderAt Fc 1 ≠ ⊤ := by
      intro htop
      rw [meromorphicOrderAt_eq_top_iff] at htop
      obtain ⟨δ, h1, h2⟩ := ((tendsto_one_add_ofReal_nhdsGT.eventually htop).and hFe).exists
      rw [h2, tensor] at h1
      exact Complex.exp_ne_zero _ h1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    obtain ⟨C₃, hC₃⟩ := exists_abs_log_norm_sub_le_of_meromorphicOrderAt Fc hFm n hn.symm
    obtain ⟨C₁, C₂, hab'⟩ := hAbelOf 1 zero_le_one
      ((hA a hprim).congr_left (fun x => by ring))
    have hG : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |Real.log ‖Fc (1 + (δ : ℂ))‖ - ((-n : ℤ) : ℝ) * (-Real.log δ)| ≤ C₃ :=
      hC₃.mono fun δ h => by
        convert h using 3
        push_cast
        ring
    obtain ⟨h1, h2⟩ := combine Fc _ 1 C₁ C₂ C₃ hFe hG hab'
    have hn1 : n = -1 := by
      have he : 0 < Real.exp (-(1 / 2)) * 1 := by positivity
      have i1 : -n ≤ 1 := by exact_mod_cast h1
      have i2 : 0 < -n := by exact_mod_cast he.trans_le h2
      omega
    refine ⟨ha, b, hb, Fc, hFeq, ?_, ?_⟩
    · exact (hFc.2.analyticOnNhd isOpen_compl_singleton).mono (fun s hs => hs.2)
    · rw [← hn, hn1]
      rfl

end SelbergClass
