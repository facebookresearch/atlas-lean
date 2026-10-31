/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Floor

/-!
# Upper bounds for the divisor function and the number of distinct prime factors

This file proves the classical upper bounds on the number of divisors `σ 0 n` and on the number
of distinct prime factors `ω n` of a natural number `n`.

## Main statements

* `ArithmeticFunction.sigma_zero_le_pow_ceil_mul_rpow`: the factorwise estimate behind both
  divisor bounds: if every prime `p ∣ n` below a threshold `y` contributes a factor at most `B`,
  and `2 ≤ y ^ ε`, then `σ 0 n ≤ B ^ ⌈y⌉₊ * n ^ ε`.
* `ArithmeticFunction.exists_sigma_zero_le_mul_rpow`: for every `ε > 0` there is `C > 0` with
  `σ 0 n ≤ C * n ^ ε` for all `n`.
* `ArithmeticFunction.sigma_zero_isBigO_rpow`, `ArithmeticFunction.sigma_zero_isLittleO_rpow`:
  the same bound as `σ 0 n = O(n ^ ε)` and `σ 0 n = o(n ^ ε)` for every `ε > 0`.
* `ArithmeticFunction.eventually_sigma_zero_lt_two_rpow`: Wigert's bound: for every `η > 0`,
  `σ 0 n < 2 ^ ((1 + η) * log n / log (log n))` for all sufficiently large `n`.
* `ArithmeticFunction.cardDistinctFactors_isBigO_log_div_log_log`:
  `ω n = O(log n / log (log n))`.
-/

@[expose] public section

open Filter Asymptotics
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega

namespace ArithmeticFunction

/-- The factorwise estimate for the divisor function. Let `ε ≥ 0` and `y ≥ 0` with `2 ≤ y ^ ε`.
If every prime `p ∣ n` with `p < y` satisfies `α + 1 ≤ B * (p ^ α) ^ ε`, where `α` is the
exponent of `p` in `n` and `1 ≤ B`, then `σ 0 n ≤ B ^ ⌈y⌉₊ * n ^ ε`. The primes `p ≥ y` need no
hypothesis, since for them `α + 1 ≤ 2 ^ α ≤ (p ^ α) ^ ε`. -/
theorem sigma_zero_le_pow_ceil_mul_rpow {n : ℕ} (hn : n ≠ 0) {ε y B : ℝ} (hε : 0 ≤ ε)
    (hy : 0 ≤ y) (hyε : 2 ≤ y ^ ε) (hB : 1 ≤ B)
    (hsmall : ∀ p ∈ n.primeFactors, (p : ℝ) < y →
      (n.factorization p : ℝ) + 1 ≤ B * ((p : ℝ) ^ n.factorization p) ^ ε) :
    (σ 0 n : ℝ) ≤ B ^ ⌈y⌉₊ * (n : ℝ) ^ ε := by
  classical
  set g : ℕ → ℝ := fun p => if (p : ℝ) < y then B else 1 with hg
  have hterm : ∀ p ∈ n.primeFactors,
      (n.factorization p : ℝ) + 1 ≤ g p * ((p : ℝ) ^ n.factorization p) ^ ε := by
    intro p hp
    by_cases hpy : (p : ℝ) < y
    · simpa [hg, hpy] using hsmall p hp hpy
    · simp only [hg, hpy, ite_false, one_mul]
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      set α := n.factorization p
      have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε :=
        hyε.trans (Real.rpow_le_rpow hy (not_lt.mp hpy) hε)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0,
        Real.rpow_natCast]
      calc (α : ℝ) + 1 ≤ 2 ^ α := by exact_mod_cast Nat.lt_two_pow_self
        _ ≤ ((p : ℝ) ^ ε) ^ α := pow_le_pow_left₀ (by norm_num) h2 α
  have hgprod : ∏ p ∈ n.primeFactors, g p ≤ B ^ ⌈y⌉₊ := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hB ((Finset.card_le_card fun p hp => ?_).trans
      (Finset.card_range _).le)
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_range]
    exact_mod_cast hp.2.trans_le (Nat.le_ceil y)
  have hcard : (σ 0 n : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [sigma_zero_apply, Nat.card_divisors hn]
    push_cast
    rfl
  have hnprod : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  rw [hcard, ← hnprod]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, g p * ((p : ℝ) ^ n.factorization p) ^ ε :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hterm
    _ = (∏ p ∈ n.primeFactors, g p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        Finset.prod_mul_distrib
    _ ≤ B ^ ⌈y⌉₊ * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε :=
        mul_le_mul_of_nonneg_right hgprod (Finset.prod_nonneg fun p _ => by positivity)

/-- The divisor bound: for every `ε > 0` there is a constant `C > 0` with `σ 0 n ≤ C * n ^ ε`
for all `n`. One may take `C = (1 + 1 / (ε * log 2)) ^ ⌈2 ^ (1 / ε)⌉₊`. -/
theorem exists_sigma_zero_le_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (σ 0 n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  have hεl : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos one_lt_two)
  set B : ℝ := 1 + 1 / (ε * Real.log 2) with hBdef
  have hB : 1 ≤ B := by rw [hBdef]; linarith [one_div_pos.mpr hεl]
  refine ⟨B ^ ⌈(2 : ℝ) ^ (1 / ε)⌉₊, by positivity, fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  refine sigma_zero_le_pow_ceil_mul_rpow hn hε.le (by positivity) ?_ hB fun p hp _ => ?_
  · rw [← Real.rpow_mul zero_le_two, one_div_mul_cancel hε.ne', Real.rpow_one]
  -- `(p ^ α) ^ ε ≥ 2 ^ (α * ε) ≥ 1 + α * ε * log 2`, which gives the claim.
  set α := n.factorization p
  set X := ((p : ℝ) ^ α) ^ ε
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hX : Real.log 2 * (ε * α) + 1 ≤ X := by
    calc Real.log 2 * (ε * α) + 1 ≤ Real.exp (Real.log 2 * (ε * α)) := Real.add_one_le_exp _
      _ = ((2 : ℝ) ^ α) ^ ε := by
          rw [Real.exp_mul, Real.exp_log two_pos, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
            mul_comm]
      _ ≤ ((p : ℝ) ^ α) ^ ε := by gcongr
  have hα : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hdiv : (α : ℝ) ≤ X / (ε * Real.log 2) := by
    rw [le_div_iff₀ hεl]; nlinarith
  have hsplit : B * X = X + X / (ε * Real.log 2) := by rw [hBdef]; ring
  rw [hsplit]
  nlinarith [mul_nonneg (Real.log_nonneg one_le_two) (mul_nonneg hε.le hα)]

/-- The divisor bound in asymptotic form: `σ 0 n = O(n ^ ε)` for every `ε > 0`. -/
theorem sigma_zero_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => (σ 0 n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ ε := by
  obtain ⟨C, -, hC⟩ := exists_sigma_zero_le_mul_rpow hε
  refine IsBigO.of_bound C (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  exact hC n

/-- The divisor bound in little-o form: `σ 0 n = o(n ^ ε)` for every `ε > 0`. -/
theorem sigma_zero_isLittleO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun n : ℕ => (σ 0 n : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ ε := by
  refine (sigma_zero_isBigO_rpow (half_pos hε)).trans_isLittleO ?_
  have h1 : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) ^ (ε / 2) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_norm_atTop_atTop.comp
      ((tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop)
  have h2 := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (ε / 2)) atTop).mul_isLittleO h1
  refine (h2.congr_left fun n => mul_one _).congr_right fun n => ?_
  rw [← Real.rpow_add' (Nat.cast_nonneg n) (by linarith), add_halves]

/-- **Wigert's divisor bound**: for every `η > 0`, the number of divisors satisfies
`σ 0 n < 2 ^ ((1 + η) * log n / log (log n))` for all sufficiently large `n`. -/
theorem eventually_sigma_zero_lt_two_rpow {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (σ 0 n : ℝ) < (2 : ℝ) ^ ((1 + η) * Real.log n / Real.log (Real.log n)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- Parameters. We use the exponent `ε = d * log 2 / log log n`, splitting the primes dividing
  -- `n` at `y = exp (log log n / d)`.
  set d : ℝ := 1 + η / 2 with hddef
  have hd0 : (0 : ℝ) < d := by rw [hddef]; linarith
  have hd1 : (1 : ℝ) < d := by rw [hddef]; linarith
  set δ : ℝ := 1 - 1 / d with hδdef
  have hδ0 : (0 : ℝ) < δ := by
    have h : 1 / d < 1 := by rw [div_lt_one hd0]; exact hd1
    rw [hδdef]; linarith
  set c : ℝ := η / 2 * Real.log 2 with hcdef
  have hc0 : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hcδ : (0 : ℝ) < c * δ ^ 3 := mul_pos hc0 (pow_pos hδ0 3)
  set U : ℝ := 3 + 108 / (c * δ ^ 3) with hUdef
  have hU3 : (3 : ℝ) ≤ U := by rw [hUdef]; linarith [div_pos (by norm_num : (0 : ℝ) < 108) hcδ]
  clear_value U c δ d
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp (Real.exp U))]
    with n hn
  -- Basic facts about `n`, `L = log n` and `u = log log n`.
  have hn0R : (0 : ℝ) < n := (Real.exp_pos _).trans_le hn
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn0R
  set L : ℝ := Real.log n with hLdef
  have hLge : Real.exp U ≤ L := by
    simpa using Real.log_le_log (Real.exp_pos _) hn
  have hL0 : (0 : ℝ) < L := (Real.exp_pos _).trans_le hLge
  set u : ℝ := Real.log L with hudef
  have huU : U ≤ u := by simpa using Real.log_le_log (Real.exp_pos U) hLge
  have hu0 : (0 : ℝ) < u := by linarith
  have hLexp : Real.exp u = L := Real.exp_log hL0
  clear_value u L
  set y : ℝ := Real.exp (u / d) with hydef
  have hy0 : (0 : ℝ) < y := Real.exp_pos _
  set ε : ℝ := d * Real.log 2 / u with hεdef
  have hε0 : (0 : ℝ) < ε := by positivity
  set M : ℝ := 1 + L / Real.log 2 with hMdef
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith [div_pos hL0 hlog2]
  have hM0 : (0 : ℝ) < M := by linarith
  -- The factorwise bound gives `σ 0 n ≤ M ^ ⌈y⌉₊ * n ^ ε`.
  have hyε : y ^ ε = 2 := by
    rw [hydef, ← Real.exp_mul, hεdef]
    convert Real.exp_log two_pos using 2
    field_simp
  have hmain : (σ 0 n : ℝ) ≤ M ^ ⌈y⌉₊ * (n : ℝ) ^ ε := by
    refine sigma_zero_le_pow_ceil_mul_rpow hn0 hε0.le hy0.le hyε.ge hM1 fun p hp _ => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    set a := n.factorization p
    have hpow1 : (1 : ℝ) ≤ (p : ℝ) ^ a := one_le_pow₀ (by linarith)
    have hple : (p : ℝ) ^ a ≤ n := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.ordProj_dvd n p)
    have hlogpa : (a : ℝ) * Real.log p ≤ L := by
      rw [hLdef]; simpa [Real.log_pow] using Real.log_le_log (by positivity) hple
    have hlogp2 : Real.log 2 ≤ Real.log p := Real.log_le_log two_pos hp2
    have ha : (a : ℝ) + 1 ≤ M := by
      have h : (a : ℝ) ≤ L / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (sub_nonneg.2 hlogp2)]
      rw [hMdef]; linarith
    have h1 : (1 : ℝ) ≤ ((p : ℝ) ^ a) ^ ε := Real.one_le_rpow hpow1 hε0.le
    nlinarith
  -- The analytic estimate `⌈y⌉₊ * log M < c * L / u`, where `c = (η / 2) * log 2`.
  have hKle : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
    have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
    have h2 : (1 : ℝ) ≤ y := Real.one_le_exp (div_pos hu0 hd0).le
    linarith
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1
  have hlogM : Real.log M ≤ 2 * u := by
    have hL4 : (4 : ℝ) ≤ L := by
      have h1 : Real.exp 3 ≤ Real.exp u := Real.exp_le_exp.2 (by linarith)
      have h2 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      linarith
    have hML : M ≤ L ^ 2 := by
      have h1 : L / Real.log 2 ≤ 2 * L := by
        rw [div_le_iff₀ hlog2]
        nlinarith
      rw [hMdef]
      nlinarith
    have h2 := Real.log_le_log hM0 hML
    rw [Real.log_pow, ← hLexp, Real.log_exp] at h2
    push_cast at h2
    linarith
  have hKM : (⌈y⌉₊ : ℝ) * Real.log M ≤ 4 * (u * y) := by
    calc (⌈y⌉₊ : ℝ) * Real.log M ≤ (2 * y) * (2 * u) :=
          mul_le_mul hKle hlogM hlogM0 (by linarith)
      _ = 4 * (u * y) := by ring
  have hLy : L = y * Real.exp (δ * u) := by
    rw [hydef, ← Real.exp_add, ← hLexp, hδdef]
    congr 1
    field_simp
    ring
  have hexp3 : (δ * u) ^ 3 / 27 ≤ Real.exp (δ * u) := by
    have h1 : (0 : ℝ) ≤ δ * u / 3 := by positivity
    have h2 : δ * u / 3 ≤ Real.exp (δ * u / 3) := by
      linarith [Real.add_one_le_exp (δ * u / 3)]
    calc (δ * u) ^ 3 / 27 = (δ * u / 3) ^ 3 := by ring
      _ ≤ Real.exp (δ * u / 3) ^ 3 := pow_le_pow_left₀ h1 h2 3
      _ = Real.exp (δ * u) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcu : (108 : ℝ) < c * δ ^ 3 * u := by
    have h1 : 108 / (c * δ ^ 3) < u := by rw [hUdef] at huU; linarith
    rwa [div_lt_iff₀ hcδ, mul_comm] at h1
  have hfinal : 4 * (u * y) < c * L / u := by
    rw [lt_div_iff₀ hu0, hLy]
    have hkey : 4 * u ^ 2 < c * Real.exp (δ * u) := by
      have h5 : c * ((δ * u) ^ 3 / 27) ≤ c * Real.exp (δ * u) :=
        mul_le_mul_of_nonneg_left hexp3 hc0.le
      have h6 : 4 * u ^ 2 < c * ((δ * u) ^ 3 / 27) := by
        have hrw : c * ((δ * u) ^ 3 / 27) = (c * δ ^ 3 * u) * u ^ 2 / 27 := by ring
        rw [hrw]
        nlinarith [mul_pos (sub_pos.mpr hcu) (mul_pos hu0 hu0)]
      linarith
    linarith [mul_lt_mul_of_pos_right hkey hy0]
  have hsplit : Real.log 2 * ((1 + η) * L / u) = L * ε + c * L / u := by
    rw [hεdef, hcdef, hddef]
    field_simp
    ring
  -- Put the pieces together.
  calc (σ 0 n : ℝ) ≤ M ^ ⌈y⌉₊ * (n : ℝ) ^ ε := hmain
    _ = Real.exp ((⌈y⌉₊ : ℝ) * Real.log M + L * ε) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hM0, Real.rpow_def_of_pos hn0R, hLdef]
    _ < Real.exp (Real.log 2 * ((1 + η) * L / u)) := by
        rw [Real.exp_lt_exp, hsplit]
        linarith
    _ = (2 : ℝ) ^ ((1 + η) * L / u) := (Real.rpow_def_of_pos two_pos _).symm

/-- The number of distinct prime factors satisfies `ω n = O(log n / log (log n))`. In fact
`ω n ≤ 4 * log n / log (log n)` for all `n ≥ 5`. -/
theorem cardDistinctFactors_isBigO_log_div_log_log :
    (fun n : ℕ => (ω n : ℝ)) =O[atTop] fun n : ℕ => Real.log n / Real.log (Real.log n) := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 5] with n hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  set y := Real.log n with hy
  have hy1 : 1 < y := by
    rw [hy, Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  -- Split the prime factors at `L = √(log n)`.
  set L := Real.sqrt y with hL
  have hL0 : 0 < L := Real.sqrt_pos.mpr hy0
  have hLsq : L * L = y := Real.mul_self_sqrt hy0.le
  have hlogL : Real.log L = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlogy_le : Real.log y ≤ 2 * L := by
    have h1 := Real.log_le_sub_one_of_pos hL0
    linarith
  have hω : ω n = n.primeFactors.card := by
    rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  set S := n.primeFactors with hS
  have hsplit : S.card = (S.filter (fun p : ℕ => (p : ℝ) ≤ L)).card +
      (S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  -- There are at most `L` small prime factors.
  have hsmall : ((S.filter (fun p : ℕ => (p : ℝ) ≤ L)).card : ℝ) ≤ L := by
    have hsub : S.filter (fun p : ℕ => (p : ℝ) ≤ L) ⊆ Finset.Icc 1 ⌊L⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_Icc.2 ⟨(Nat.prime_of_mem_primeFactors hp.1).one_lt.le, Nat.le_floor hp.2⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hL0.le)
  -- Their product being at most `n`, there are at most `2 * log n / log log n` large ones.
  set T := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L) with hT
  have hlarge : (T.card : ℝ) * (Real.log y / 2) ≤ y := by
    have hprod : L ^ T.card ≤ ∏ p ∈ T, (p : ℝ) := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => hL0.le) fun p hp => ?_
      rw [hT, Finset.mem_filter] at hp
      exact (not_le.mp hp.2).le
    have hTS : ∏ p ∈ T, p ≤ n :=
      calc ∏ p ∈ T, p ≤ ∏ p ∈ S, p :=
            Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
              (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
        _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
    have hTSR : ∏ p ∈ T, (p : ℝ) ≤ n := by rw [← Nat.cast_prod]; exact_mod_cast hTS
    have := Real.log_le_log (pow_pos hL0 _) (hprod.trans hTSR)
    rwa [Real.log_pow, hlogL] at this
  have hTle : (T.card : ℝ) ≤ 2 * y / Real.log y := by
    rw [le_div_iff₀ hly]; linarith
  have hLle : L ≤ 2 * y / Real.log y := by
    rw [le_div_iff₀ hly]
    nlinarith
  have hω' : (ω n : ℝ) ≤ 4 * (y / Real.log y) := by
    rw [hω, hsplit]
    push_cast
    have : 4 * (y / Real.log y) = 2 * y / Real.log y + 2 * y / Real.log y := by ring
    rw [this]
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (div_nonneg hy0.le hly.le)]
  exact hω'

end ArithmeticFunction
