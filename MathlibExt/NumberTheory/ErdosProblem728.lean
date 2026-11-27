/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/728.lean` (Formal Conjectures), for the definition
of `conjecture` and the statement of `conjecture_holds`.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 728

`conjecture_holds` gives factorial divisibility with the excess in any prescribed
logarithmic window. Following the construction in Sothanaphan's writeup (arXiv:2601.07421),
we take `n = 2m`, `b = m`, and `a = m + k`. To prove the binomial divisibility, we compare
the carries when adding `m + k` with those when doubling `m`. A count of digit blocks
supplies positions where only doubling carries, simultaneously for all small primes.
-/

@[expose] public section

open Finset Filter
open scoped Nat Topology

namespace MathlibExt.NumberTheory.ErdosProblem728Wanted

/-- **Erdős Problem 728.** The proposition that there is a real number $\delta > 0$ such that for
every real number $\varepsilon$ with $0 < \varepsilon < \delta$ and all real numbers $C > 0$ and
$C' > C$, there are natural numbers $a$, $b$ and $n \ge 1$ with $a > \varepsilon n$,
$b > \varepsilon n$, $a! \, b! \mid n! \, (a + b - n)!$ and $n + C \log n < a + b < n + C' \log n$.
-/
def conjecture : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
    ∃ a b n : ℕ,
      0 < n ∧
      ε * n < a ∧
      ε * n < b ∧
      a ! * b ! ∣ n ! * (a + b - n)! ∧
      a + b > n + C * Real.log n ∧
      a + b < n + C' * Real.log n

-- A digit in the upper half forces a carry on doubling. Excluding the final
-- digit leaves room to add k without carrying once the place value exceeds k.
private def goodDigits (b : ℕ) := Ico ((b + 1) / 2) (b - 1)

private def avoids (b l m : ℕ) : Prop :=
  ∀ i < l, m / b ^ i % b ∉ goodDigits b

private lemma split_injective (a : ℕ) :
    Function.Injective (fun n : ℕ ↦ (n / a, n % a)) :=
  fun _ _ h ↦ Nat.ext_div_mod (congrArg Prod.fst h) (congrArg Prod.snd h)

-- Among complete periods, excluding the good digits costs the same fraction at every position.
open Classical in
private lemma count_avoids (t b l : ℕ) (hb : 0 < b) :
    ((range (t * b ^ l)).filter (avoids b l)).card ≤
      t * (range b \ goodDigits b).card ^ l := by
  classical
  induction l with
  | zero => simpa using (card_filter_le (range t) (avoids b 0))
  | succ l ih =>
    let s := (range (t * b ^ l)).filter (avoids b l)
    let d := range b \ goodDigits b
    have h : ((range (t * b ^ (l + 1))).filter (avoids b (l + 1))).card ≤
        (s ×ˢ d).card := by
      apply card_le_card_of_injOn (fun n : ℕ ↦ (n / b, n % b)) _ (split_injective b).injOn
      intro n hn
      obtain ⟨hn, ha⟩ := mem_filter.mp hn
      refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · apply (Nat.div_lt_iff_lt_mul hb).mpr
        simpa [pow_succ, mul_assoc] using mem_range.mp hn
      · intro i hi
        simpa [Nat.div_div_eq_div_mul, pow_succ'] using ha (i + 1) (by omega)
      · exact mem_range.mpr (Nat.mod_lt _ hb)
      · simpa using ha 0 (by omega)
    rw [card_product] at h
    exact h.trans (by simpa [pow_succ, ← mul_assoc, d] using Nat.mul_le_mul_right d.card ih)

private noncomputable def badBlock (M b s l : ℕ) : Finset ℕ := by
  classical exact (range (2 * M)).filter (fun m ↦ avoids b l (m / b ^ s))

-- Round the search interval up to complete periods. Each group of twelve missed digits
-- contributes a factor of at most 1/8, since at least a quarter of the digits are good.
private lemma count_badBlock {M b s r : ℕ} (hb : 8 ≤ b) (hQ : b ^ (s + 12 * r) ≤ M) :
    (badBlock M b s (12 * r)).card * 8 ^ r ≤ 3 * M := by
  classical
  let A := b ^ s
  let l := 12 * r
  let Q := b ^ (s + l)
  let t := 2 * M / Q + 1
  let d := (range b \ goodDigits b).card
  have hb₀ : 0 < b := by omega
  have hA : 0 < A := pow_pos hb₀ _
  have hQ₀ : 0 < Q := pow_pos hb₀ _
  have hQA : Q = b ^ l * A := by simp [Q, A, pow_add, mul_comm]
  have ht : 2 * M < t * Q := by
    have := Nat.mod_lt (2 * M) hQ₀
    have := Nat.div_add_mod (2 * M) Q
    dsimp [t]
    nlinarith
  have ht' : t * Q ≤ 3 * M := by
    have := Nat.div_mul_le_self (2 * M) Q
    change Q ≤ M at hQ
    dsimp [t]
    nlinarith
  have hcount : (badBlock M b s l).card ≤
      (((range (t * b ^ l)).filter (avoids b l)) ×ˢ range A).card := by
    apply card_le_card_of_injOn (fun n : ℕ ↦ (n / A, n % A)) _ (split_injective A).injOn
    intro n hn
    obtain ⟨hn, ha⟩ := mem_filter.mp (show n ∈ (range (2 * M)).filter _ from hn)
    refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ?_, ha⟩, mem_range.mpr (Nat.mod_lt _ hA)⟩
    apply (Nat.div_lt_iff_lt_mul hA).mpr
    simpa [hQA, mul_assoc] using (mem_range.mp hn).trans ht
  rw [card_product, card_range] at hcount
  have hg : goodDigits b ⊆ range b := fun n hn ↦
    mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp hn).2 (Nat.sub_le _ _))
  have hd : 4 * d ≤ 3 * b := by
    simp only [d, card_sdiff_of_subset hg, card_range, goodDigits, Nat.card_Ico]
    omega
  have hpow : d ^ l * 8 ^ r ≤ b ^ l := by
    have h₁ := Nat.pow_le_pow_left hd 12
    have h₂ : d ^ 12 * 8 ≤ b ^ 12 := by
      simp only [mul_pow] at h₁
      norm_num1 at h₁
      omega
    simpa [l, pow_mul, mul_pow] using Nat.pow_le_pow_left h₂ r
  calc
    _ ≤ (t * d ^ l * A) * 8 ^ r :=
      Nat.mul_le_mul_right _ (hcount.trans (Nat.mul_le_mul_right _ (count_avoids t b l hb₀)))
    _ = t * (d ^ l * 8 ^ r) * A := by ring
    _ ≤ t * (b ^ l) * A := by gcongr
    _ = t * Q := by rw [hQA, mul_assoc]
    _ ≤ _ := ht'

private def start (r j : ℕ) := r + 12 * r * j

private def scale (r : ℕ) := 2 ^ (48 * r ^ 3)

-- Skip the first r digits, then test r disjoint blocks of length 12r in base p³.
-- The scale fits every period, and the sum of the failure counts is less than the interval size.
private lemma exists_digits {r : ℕ} (hr : 2 ≤ r) :
    ∃ m ∈ Ico (scale r) (2 * scale r), ∀ p, 2 ≤ p → p ≤ 2 ^ r →
      ∀ j < r, ∃ i < 12 * r,
        m / (p ^ 3) ^ (start r j + i) % (p ^ 3) ∈ goodDigits (p ^ 3) := by
  classical
  let M := scale r
  let pairs := Icc 2 (2 ^ r) ×ˢ range r
  let bad := fun u : ℕ × ℕ ↦ badBlock M (u.1 ^ 3) (start r u.2) (12 * r)
  have hcount (u) (hu : u ∈ pairs) : (bad u).card * 8 ^ r ≤ 3 * M := by
    obtain ⟨hp, hp'⟩ := mem_Icc.mp (mem_product.mp hu).1
    have hj := mem_range.mp (mem_product.mp hu).2
    apply count_badBlock (by simpa using Nat.pow_le_pow_left hp 3)
    change (u.1 ^ 3) ^ (start r u.2 + 12 * r) ≤ 2 ^ (48 * r ^ 3)
    calc
      _ ≤ ((2 ^ r) ^ 3) ^ (start r u.2 + 12 * r) := by gcongr
      _ ≤ _ := by
        rw [← pow_mul, ← pow_mul]
        apply Nat.pow_le_pow_right (by decide)
        have h := Nat.mul_le_mul_left (12 * r) (show u.2 + 1 ≤ r from hj)
        dsimp [start]
        nlinarith [Nat.mul_le_mul_left (3 * r) h, Nat.mul_le_mul_left (r * r) hr]
  have hsum : (pairs.biUnion bad).card * 8 ^ r ≤ pairs.card * (3 * M) := by
    calc
      _ ≤ (∑ u ∈ pairs, (bad u).card) * 8 ^ r := by gcongr; exact card_biUnion_le
      _ = ∑ u ∈ pairs, (bad u).card * 8 ^ r := sum_mul ..
      _ ≤ ∑ _u ∈ pairs, 3 * M := sum_le_sum hcount
      _ = _ := by simp
  have hpair : pairs.card ≤ 2 ^ r * r := by
    simpa [pairs, Nat.card_Icc] using Nat.mul_le_mul_right r (Nat.sub_le (2 ^ r) 1)
  have hsmall : 2 ^ r * r * 3 < 8 ^ r := by
    have h₂ : 3 < 2 ^ r :=
      lt_of_lt_of_le (by decide : 3 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hr)
    calc
      _ < 2 ^ r * 2 ^ r * 2 ^ r := by
        gcongr
        exact Nat.lt_pow_self (by decide)
      _ = _ := by rw [← mul_pow, ← mul_pow]; norm_num
  have hM : 0 < M := pow_pos (by decide : 0 < 2) _
  have hcard : (pairs.biUnion bad).card < M := by
    have := calc
      (pairs.biUnion bad).card * 8 ^ r ≤ pairs.card * (3 * M) := hsum
      _ ≤ (2 ^ r * r * 3) * M := by rw [mul_assoc (2 ^ r * r)]; gcongr
      _ < 8 ^ r * M := Nat.mul_lt_mul_of_pos_right hsmall hM
    exact (Nat.mul_lt_mul_right (by positivity : 0 < 8 ^ r)).mp (by simpa [mul_comm M] using this)
  obtain ⟨m, hm, hm'⟩ := not_subset.mp (show ¬ Ico M (2 * M) ⊆ pairs.biUnion bad by
    intro hs
    have := card_le_card hs
    rw [Nat.card_Ico] at this
    omega)
  refine ⟨m, hm, fun p hp hp' j hj ↦ ?_⟩
  by_contra! h
  apply hm'
  apply mem_biUnion.mpr
  refine ⟨(p, j), mem_product.mpr ⟨mem_Icc.mpr ⟨hp, hp'⟩, mem_range.mpr hj⟩, ?_⟩
  change m ∈ (range (2 * M)).filter _
  refine mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hm).2, ?_⟩
  intro i hi
  simpa [pow_add, Nat.div_div_eq_div_mul] using h i hi

-- At the end of a good digit, only doubling produces a carry.
private lemma extra_carry {m b i k : ℕ} (hb : 0 < b) (hk : k ≤ b ^ i)
    (hd : m / b ^ i % b ∈ goodDigits b) :
    b ^ (i + 1) ≤ m % b ^ (i + 1) + m % b ^ (i + 1) ∧
      k % b ^ (i + 1) + m % b ^ (i + 1) < b ^ (i + 1) := by
  let a := b ^ i
  let d := m / a % b
  have ha : 0 < a := pow_pos hb _
  have hlow : (b + 1) / 2 ≤ d := (mem_Ico.mp hd).1
  have hhigh : d < b - 1 := (mem_Ico.mp hd).2
  have h₁ := Nat.mul_le_mul_left a (show b ≤ d + d by omega)
  have h₂ := Nat.mul_le_mul_left a (show d + 2 ≤ b by omega)
  have h₃ := Nat.mod_lt m ha
  have h₄ := Nat.mod_le k (a * b)
  rw [pow_succ, Nat.mod_mul (x := m)]
  change a * b ≤ m % a + a * d + (m % a + a * d) ∧
    k % (a * b) + (m % a + a * d) < a * b
  change k ≤ a at hk
  simp only [Nat.mul_add, Nat.mul_two] at h₁ h₂
  omega

private lemma choose_dvd_of_digits {m k r : ℕ} (hk : 2 * k ≤ 2 ^ r)
    (hd : ∀ p, 2 ≤ p → p ≤ 2 ^ r → ∀ j < r, ∃ i < 12 * r,
      m / (p ^ 3) ^ (start r j + i) % (p ^ 3) ∈ goodDigits (p ^ 3)) :
    (m + k).choose k ∣ (m + m).choose m := by
  classical
  apply (Nat.factorization_le_iff_dvd (Nat.choose_pos (by omega)).ne'
    (Nat.choose_pos (by omega)).ne').mp
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  let B := (m + k) + (m + m) + 2
  have hlog (n : ℕ) : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
  rw [Nat.factorization_choose' hp (b := B) (by dsimp [B]; have := hlog (m + k); omega),
    Nat.factorization_choose' hp (b := B) (by dsimp [B]; have := hlog (m + m); omega)]
  let s := (Ico 1 B).filter (fun e ↦ p ^ e ≤ k % p ^ e + m % p ^ e)
  let t := (Ico 1 B).filter (fun e ↦ p ^ e ≤ m % p ^ e + m % p ^ e)
  change s.card ≤ t.card
  -- A carry missing from the doubling count must come from a prime power at most 2k.
  have hunmatched (e : ℕ) (he : e ∈ s \ t) : 1 ≤ e ∧ p ^ e ≤ 2 * k := by
    obtain ⟨hs, ht⟩ := mem_sdiff.mp he
    obtain ⟨hI, hc⟩ := mem_filter.mp hs
    have hnc : ¬ p ^ e ≤ m % p ^ e + m % p ^ e :=
      fun h ↦ ht (mem_filter.mpr ⟨hI, h⟩)
    have := Nat.mod_le k (p ^ e)
    exact ⟨(mem_Ico.mp hI).1, by omega⟩
  by_cases hp' : 2 ^ r < p
  · apply card_le_card
    intro e he
    by_contra hn
    obtain ⟨he₀, he₁⟩ := hunmatched e (mem_sdiff.mpr ⟨he, hn⟩)
    have := Nat.le_self_pow (by omega : e ≠ 0) p
    omega
  have hs : (s \ t).card ≤ r := by
    have sub : s \ t ⊆ Icc 1 r := by
      intro e he
      obtain ⟨he₀, he₁⟩ := hunmatched e he
      exact mem_Icc.mpr ⟨he₀, (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        ((Nat.pow_le_pow_left hp.two_le _).trans (he₁.trans hk))⟩
    simpa using card_le_card sub
  -- Each good block supplies a different carry in the opposite set difference.
  choose! f hf hg using hd p hp.two_le (by omega)
  let pos := fun j ↦ start r j + f j
  let exp := fun j ↦ 3 * (pos j + 1)
  have ht : r ≤ (t \ s).card := by
    rw [← card_range r]
    apply card_le_card_of_injOn exp
    · intro j hj
      have hj' := mem_range.mp hj
      have hb : 2 ≤ p ^ 3 := hp.two_le.trans (Nat.le_self_pow (by decide) p)
      have hk' : k ≤ (p ^ 3) ^ pos j := calc
        k ≤ 2 ^ r := by omega
        _ ≤ (p ^ 3) ^ r := Nat.pow_le_pow_left hb _
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by dsimp [pos, start]; omega)
      have ⟨h₁, h₂⟩ := extra_carry (by omega : 0 < p ^ 3) hk' (hg j hj')
      rw [← pow_mul] at h₁ h₂
      have he : exp j < p ^ exp j := Nat.lt_pow_self hp.one_lt
      have := Nat.mod_le m (p ^ exp j)
      change p ^ exp j ≤ m % p ^ exp j + m % p ^ exp j at h₁
      have hI : exp j ∈ Ico 1 B := mem_Ico.mpr ⟨by dsimp [exp]; omega, by dsimp [B]; omega⟩
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hI, h₁⟩, fun h ↦ h₂.not_ge (mem_filter.mp h).2⟩
    · intro a ha b hb hab
      have hmono (x y : ℕ) (hx : x < r) (hxy : x < y) : exp x < exp y := by
        have := Nat.mul_le_mul_left (12 * r) (show x + 1 ≤ y from hxy)
        have := hf x hx
        dsimp [exp, pos, start]
        nlinarith
      rcases lt_trichotomy a b with h | h | h
      · exact ((hmono a b (mem_range.mp ha) h).ne hab).elim
      · exact h
      · exact ((hmono b a (mem_range.mp hb) h).ne hab.symm).elim
  have h₁ := card_sdiff_add_card_inter s t
  have h₂ := card_sdiff_add_card_inter t s
  rw [inter_comm t s] at h₂
  omega

private lemma factorial_dvd_of_choose_dvd {m k : ℕ}
    (h : (m + k).choose k ∣ (m + m).choose m) :
    (m + k)! * m ! ∣ (m + m)! * k ! := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  rw [← Nat.add_choose_mul_factorial_mul_factorial m m, hq,
    ← Nat.add_choose_mul_factorial_mul_factorial m k]
  ring

-- Choose k as the floor of c log M. Since M ≤ m < 2M, replacing M by 2m changes
-- the logarithm by at most log 4, which the strict window eventually absorbs.
private lemma exists_window {C C' : ℝ} (hC : 0 < C) (hCC : C < C') :
    ∃ m k : ℕ, 0 < m ∧ (m + k)! * m ! ∣ (m + m)! * k ! ∧
      C * Real.log (m + m : ℝ) < k ∧ (k : ℝ) < C' * Real.log (m + m : ℝ) := by
  obtain ⟨c, h₁, h₂⟩ := exists_between hCC
  let d := 48 * Real.log 2
  have hd : 0 < d := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hc : 0 < c := hC.trans h₁
  have hpoly : Tendsto (fun r : ℕ ↦ (r : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by decide : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hgap := (hpoly.const_mul_atTop (mul_pos (sub_pos.mpr h₁) hd)).eventually
    (eventually_gt_atTop (C * Real.log 4 + 1))
  have hbound := (tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1 : ℝ) < 2)
    |>.const_mul (2 * c * d)).eventually (eventually_lt_nhds
      (by simp : (2 * c * d) * 0 < 1))
  obtain ⟨r, hr, hgap, hbound⟩ := ((eventually_ge_atTop 2).and (hgap.and hbound)).exists
  change C * Real.log 4 + 1 < (c - C) * d * (r : ℝ) ^ 3 at hgap
  change 2 * c * d * ((r : ℝ) ^ 3 / 2 ^ r) < 1 at hbound
  let M := scale r
  have hM : 0 < M := pow_pos (by decide : 0 < 2) _
  have hlog : Real.log M = d * (r : ℝ) ^ 3 := by
    simp [M, scale, Real.log_pow, d, mul_right_comm]
  let k := ⌊c * Real.log M⌋₊
  have hlog₀ : 0 < Real.log M := by rw [hlog]; positivity
  have hk₁ : (k : ℝ) ≤ c * Real.log M := Nat.floor_le (mul_pos hc hlog₀).le
  have hk₂ : c * Real.log M < k + 1 := Nat.lt_floor_add_one _
  have hk : 2 * k ≤ 2 ^ r := by
    rw [← mul_div_assoc, div_lt_one (by positivity)] at hbound
    rw [hlog] at hk₁
    exact_mod_cast (show 2 * (k : ℝ) ≤ (2 : ℝ) ^ r by linarith)
  obtain ⟨m, hm, hdigits⟩ := exists_digits hr
  obtain ⟨hl, hu⟩ := mem_Ico.mp hm
  change M ≤ m at hl
  change m < 2 * M at hu
  have hm₀ := hM.trans_le hl
  refine ⟨m, k, hm₀, factorial_dvd_of_choose_dvd (choose_dvd_of_digits hk hdigits), ?_, ?_⟩
  · have hmn : (m : ℝ) + m ≤ 4 * M := by exact_mod_cast (by omega : m + m ≤ 4 * M)
    have ht := Real.log_le_log (by positivity) hmn
    rw [Real.log_mul (by norm_num) (by positivity)] at ht
    rw [hlog] at hk₂ ht
    nlinarith [mul_le_mul_of_nonneg_left ht hC.le]
  · have hmn : (M : ℝ) ≤ m + m := by exact_mod_cast (by omega : M ≤ m + m)
    exact hk₁.trans_lt ((mul_lt_mul_of_pos_right h₂ hlog₀).trans_le
      (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hmn) (hC.trans hCC).le))

/--
**Erdős Problem 728 holds.** There is a real number $\delta > 0$ such that for every real number
$\varepsilon$ with $0 < \varepsilon < \delta$ and all real numbers $C > 0$ and $C' > C$, there are
natural numbers $a$, $b$ and $n \ge 1$ with $a > \varepsilon n$, $b > \varepsilon n$,
$a! \, b! \mid n! \, (a + b - n)!$ and $n + C \log n < a + b < n + C' \log n$.

The statement was resolved in the affirmative by Barreto and ChatGPT-5.2.

Source: N.
Sothanaphan, Resolution of Erdős Problem #728: a writeup of Aristotle's Lean proof,
arXiv:2601.07421 (2026), https://arxiv.org/abs/2601.07421. Moved from
`OpenConjectures/NumberTheory/ErdosProblem728`.
-/
theorem conjecture_holds : conjecture := by
  unfold conjecture
  filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
    nhdsWithin_le_nhds] with ε hε
  intro C hC C' hCC
  obtain ⟨m, k, hm, hdiv, hl, hu⟩ := exists_window hC hCC
  have hhalf := mul_lt_mul_of_pos_right hε (Nat.cast_pos.mpr hm : (0 : ℝ) < m)
  refine ⟨m + k, m, m + m, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  · push_cast
    linarith
  · simpa only [show m + k + m - (m + m) = k by omega] using hdiv
  · push_cast
    linarith
  · push_cast
    linarith

end MathlibExt.NumberTheory.ErdosProblem728Wanted
