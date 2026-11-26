/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Complementary sequences

A positive integer strictly between two successive pyramidal numbers has a known number of
pyramidal predecessors. Integer cube root bounds locate the two possible gaps containing the
requested term of the complementary sequence. More generally, an interleaving function
locates the gap containing the requested term for any sequence with sufficiently large gaps.
Rounding $\sqrt{2n}$ to the nearest integer locates the gap of the triangular numbers containing
the $n$-th non-triangular number.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The $n$-th non-value of a sequence.** For $f : \mathbb{N} \to \mathbb{N}$ and $n \ge 1$, the
$n$-th non-value of $f$ is the $n$-th smallest positive integer that is not of the form $f(m)$
with $m \ge 1$, or $0$ if fewer than $n$ such integers exist. At $n = 0$ it takes the same value
as at $n = 1$.

In the paper's notation, where $f = f_{\neg P}$ lists the positive integers without a property
$P$, the $n$-th non-value of $f$ is $f_P(n)$, the $n$-th term of the complementary sequence.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (definition of `f_P`). -/
public noncomputable def nthNonValue (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun x => 0 < x ∧ ∀ m, 1 ≤ m → f m ≠ x) (n - 1)

/-- **The first non-square.** The smallest positive integer that is not the square of a positive
integer is $2$; that is, the first non-value of $m \mapsto m^2$ is $2$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (the non-squares). -/
public theorem nthNonValue_sq_one : nthNonValue (fun m => m ^ 2) 1 = 2 := by
  classical
  have h2 : 0 < 2 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 2 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have hc : Nat.count (fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) 2 = 0 := by
    have h0 : ¬ (0 < 0 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 0) := fun h => lt_irrefl 0 h.1
    have h1 : ¬ (0 < 1 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 1) := fun h => h.2 1 le_rfl rfl
    simp only [Nat.count_succ, Nat.count_zero, h0, h1, ite_false]
  have := Nat.nth_count (p := fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) h2
  rw [hc] at this
  simpa [nthNonValue] using this

/-- **The second non-square.** The second smallest positive integer that is not the square of a
positive integer is $3$; that is, the second non-value of $m \mapsto m^2$ is $3$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Section 1 (the non-squares). -/
public theorem nthNonValue_sq_two : nthNonValue (fun m => m ^ 2) 2 = 3 := by
  classical
  have h2 : 0 < 2 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 2 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have h3 : 0 < 3 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 3 := by
    refine ⟨by norm_num, fun m hm h => ?_⟩
    have : m ≤ 1 := by nlinarith
    interval_cases m
    simp at h
  have hc : Nat.count (fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) 3 = 1 := by
    have h0 : ¬ (0 < 0 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 0) := fun h => lt_irrefl 0 h.1
    have h1 : ¬ (0 < 1 ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ 1) := fun h => h.2 1 le_rfl rfl
    simp only [Nat.count_succ, Nat.count_zero, h0, h1, ite_false,
      eq_true h2, ite_true]
  have := Nat.nth_count (p := fun x => 0 < x ∧ ∀ m, 1 ≤ m → m ^ 2 ≠ x) h3
  rw [hc] at this
  simpa [nthNonValue] using this

namespace nthNonValue_pyramidal_two_case_le_eight

open Finset

/-- Between two successive values of `f`, the number of skipped positive integers is known. -/
private theorem nthNonValue_of_gap {f : ℕ → ℕ} (hf : StrictMono f) (h0 : f 0 = 0)
    {n t : ℕ} (hlo : f t < n + t) (hhi : n + t < f (t + 1)) :
    nthNonValue f n = n + t := by
  classical
  let p := fun x => 0 < x ∧ ∀ m, 1 ≤ m → f m ≠ x
  have hmem : p (n + t) := by
    refine ⟨Nat.zero_lt_of_lt hlo, fun m _ => ?_⟩
    rcases le_or_gt m t with hm | hm
    · exact ((hf.monotone hm).trans_lt hlo).ne
    · exact (hhi.trans_le (hf.monotone hm)).ne'
  let vals := (range (t + 1)).image f
  have hsub : vals ⊆ range (n + t) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr ((hf.monotone (Nat.le_of_lt_succ (mem_range.mp hm))).trans_lt hlo)
  have hfilter : (range (n + t)).filter p = range (n + t) \ vals := by
    ext x
    simp only [mem_filter, mem_sdiff, mem_range, vals, mem_image]
    refine and_congr_right fun hx => ⟨fun hp ⟨m, _, he⟩ => ?_, fun hv => ?_⟩
    · cases m with
      | zero => exact hp.1.ne' (h0 ▸ he).symm
      | succ m => exact hp.2 _ (by omega) he
    · refine ⟨Nat.pos_of_ne_zero (fun he => hv ⟨0, by omega, h0.trans he.symm⟩), ?_⟩
      intro m _ he
      apply hv
      exact ⟨m, hf.lt_iff_lt.mp (he ▸ hx.trans hhi), he⟩
  have hcount : Nat.count p (n + t) = n - 1 := by
    rw [Nat.count_eq_card_filter_range, hfilter, card_sdiff_of_subset hsub, card_range]
    simp only [vals, card_image_of_injective _ hf.injective, card_range]
    omega
  change Nat.nth p (n - 1) = n + t
  rw [← hcount, Nat.nth_count hmem]

private def pyramidal (k j : ℕ) : ℕ :=
  j * (j + 1) * ((k - 2) * j + 5 - k) / 6

/-- The numerator is divisible by six. Its two summands use products of three and two
consecutive integers, respectively. -/
private theorem six_mul_pyramidal_succ (d j : ℕ) :
    6 * pyramidal (d + 2) (j + 1) = (j + 1) * (j + 2) * (d * j + 3) := by
  obtain ⟨a, ha⟩ := Nat.factorial_dvd_ascFactorial j 3
  obtain ⟨b, hb⟩ := Nat.factorial_dvd_ascFactorial (j + 1) 2
  norm_num [Nat.ascFactorial, Nat.factorial] at ha hb
  unfold pyramidal
  rw [Nat.add_sub_cancel, Nat.mul_add d j 1, Nat.mul_one,
    show d * j + d + 5 - (d + 2) = d * j + 3 by omega, Nat.mul_div_cancel']
  exact ⟨d * a + b, by linear_combination d * ha + 3 * hb⟩

private theorem pyramidal_strictMono (d : ℕ) : StrictMono (pyramidal (d + 2)) := by
  apply strictMono_nat_of_lt_succ
  intro j
  cases j with
  | zero => simp [pyramidal]
  | succ j =>
    have h₁ := six_mul_pyramidal_succ d j
    have h₂ := six_mul_pyramidal_succ d (j + 1)
    ring_nf at h₁ h₂ ⊢
    omega

end nthNonValue_pyramidal_two_case_le_eight

open nthNonValue_pyramidal_two_case_le_eight

/-- **Two-case formula for the non-pyramidal numbers when $k \le 8$.** Let $3 \le k \le 8$, and
for $j \ge 1$ let $P(k, j) = j (j + 1) ((k - 2) j - (k - 5))/6$ be the $k$-gonal pyramidal
numbers. For every integer $n \ge 1$, put $s = \lfloor \sqrt[3]{6n/(k - 2)} \rfloor$. Then the
$n$-th positive integer that is not of the form $P(k, j)$ with $j \ge 1$ equals $n + s - 1$ if
$6n \le s (s - 1) (s (k - 2) + k + 1)$, and $n + s$ otherwise.

This extends Equation (7) of Corollary 4 from $k \le 5$ to $k \le 8$; the paper reports it after
checking small values of $n$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, remark after Corollary 4. -/
public theorem nthNonValue_pyramidal_two_case_le_eight (k : ℕ) (hk : 3 ≤ k)
    (hk' : k ≤ 8) (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.nthRoot 3 (6 * n / (k - 2))
    nthNonValue (fun j => j * (j + 1) * ((k - 2) * j + 5 - k) / 6) n =
      if 6 * n ≤ s * (s - 1) * (s * (k - 2) + k + 1) then n + s - 1 else n + s := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : 0 < d := by omega
  let s := Nat.nthRoot 3 (6 * n / d)
  have hlo : s ^ 3 * d ≤ 6 * n :=
    (Nat.le_div_iff_mul_le hd).mp (Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide)))
  have hhi : 6 * n < (s + 1) ^ 3 * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_pow_nthRoot_add_one (by decide) _)
  have hs : 1 ≤ s := by
    apply (Nat.le_nthRoot_iff (by decide)).mpr
    apply (Nat.le_div_iff_mul_le hd).mpr
    simpa using (show d ≤ 6 * n by omega)
  change nthNonValue (pyramidal (d + 2)) n = _
  simp only [Nat.add_sub_cancel]
  change _ = if 6 * n ≤ s * (s - 1) * (s * d + (d + 2) + 1) then n + s - 1 else n + s
  obtain ⟨r, hr⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
  rw [hr] at hlo hhi ⊢
  simp only [Nat.add_sub_cancel]
  -- The threshold compares n with the number of missing positive integers up to P(k, s).
  have hcut : 6 * pyramidal (d + 2) (r + 1) =
      6 * (r + 1) + (r + 1) * r * ((r + 1) * d + (d + 2) + 1) := by
    rw [six_mul_pyramidal_succ]
    ring
  have hmono := pyramidal_strictMono d
  have hzero : pyramidal (d + 2) 0 = 0 := by simp [pyramidal]
  split_ifs with h
  · rw [show n + (r + 1) - 1 = n + r by omega]
    apply nthNonValue_of_gap hmono hzero _ (by omega)
    cases r with
    | zero => simpa [pyramidal] using (show 0 < n by omega)
    | succ r =>
      have he := six_mul_pyramidal_succ d r
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      ring_nf at he hlo ⊢
      omega
  · apply nthNonValue_of_gap hmono hzero (by omega)
    have he := six_mul_pyramidal_succ d (r + 1)
    cases r with
    | zero =>
      -- For s = 1 the upper cube bound gives 6n < 8d, so n ≤ d + 1 since d ≤ 6.
      norm_num at he hhi ⊢
      omega
    | succ r =>
      have hcoef : d + 3 ≤ 3 * (r + 3) := by omega
      nlinarith only [he, hhi, Nat.mul_le_mul_left (r + 3) hcoef]

private theorem nthNonValue_eq_one_step.exists_strictMono_extension (f : ℕ → ℕ)
    (hf1 : 1 ≤ f 1) (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) :
    ∃ g : ℕ → ℕ, g 0 = 0 ∧ (∀ m, 1 ≤ m → g m = f m) ∧ StrictMono g := by
  -- The gap-counting lemma uses zero as the left endpoint before the first positive value.
  let g := Function.update f 0 0
  have gzero : g 0 = 0 := Function.update_self ..
  have gpos (m : ℕ) (hm : 1 ≤ m) : g m = f m := Function.update_of_ne (by omega) 0 f
  have hg : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro m
    cases m with
    | zero =>
      rw [gzero, gpos 1 le_rfl]
      omega
    | succ m =>
      rw [gpos _ (by omega), gpos _ (by omega)]
      have := hgap (m + 1) (by omega)
      omega
  exact ⟨g, gzero, gpos, hg⟩

/-- **Complementary sequences from one evaluation of the counting function.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all
$m \ge 1$, let $C(x)$ be the number of $m$ with $1 \le m \le x$ and $f(m) \le x$, and for
$n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with $m \ge 1$.
Then for every $n \ge 1$, $f_P(n) = n + C(n) + 1$ if $f(C(n) + 1) \le n + C(n)$, and
$f_P(n) = n + C(n)$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 2. -/
public theorem nthNonValue_eq_one_step (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (n : ℕ) (hn : 1 ≤ n) :
    let C : ℕ → ℕ := fun x => ((Finset.Icc 1 x).filter (fun m => f m ≤ x)).card
    nthNonValue f n = if f (C n + 1) ≤ n + C n then n + C n + 1 else n + C n := by
  intro C
  obtain ⟨g, gzero, gpos, hg⟩ := nthNonValue_eq_one_step.exists_strictMono_extension f hf1 hgap
  -- The indices counted at n form the initial interval from 1 to k.
  obtain ⟨k, hk, hnext⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (p := fun m => n < g m) (by simp [gzero]) ⟨n + 1, (Nat.lt_succ_self n).trans_le hg.le_apply⟩
  have hlast : g k ≤ n := le_of_not_gt hk
  have hindex (m : ℕ) : g m ≤ n ↔ m ≤ k :=
    ⟨fun h => Nat.lt_succ_iff.mp (hg.lt_iff_lt.mp (h.trans_lt hnext)),
      fun h => (hg.monotone h).trans hlast⟩
  have hC : C n = k := by
    have hset : ((Finset.Icc 1 n).filter fun m => f m ≤ n) = Finset.Icc 1 k := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, and_assoc]
      refine and_congr_right fun hm => ?_
      rw [← gpos m hm, hindex]
      exact and_iff_right_of_imp fun h => h.trans (hg.le_apply.trans hlast)
    change ((Finset.Icc 1 n).filter _).card = k
    simp [hset]
  have heq : nthNonValue f n = nthNonValue g n := by
    simp +contextual only [nthNonValue, gpos]
  rw [heq, hC, ← gpos (k + 1) (by omega)]
  split_ifs with h
  · -- The next value is skipped, and the gap after it contains n + k + 1.
    rw [Nat.add_assoc]
    apply nthNonValue_of_gap hg gzero (by omega)
    have hstep := hgap (k + 1) (by omega)
    rw [← gpos _ (by omega), ← gpos _ (by omega)] at hstep
    omega
  · apply nthNonValue_of_gap hg gzero _ (by omega)
    cases k with
    | zero => simpa [gzero] using (show 0 < n by omega)
    | succ k => omega

/-- **Complementary sequences from an interleaving function.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Then for every $n \ge 1$, $f_P(n) = n + h(n) + 1$ if $f(h(n) + 1) \le n + h(n)$; otherwise
$f_P(n) = n + h(n) - 1$ if $n + h(n) \le f(h(n))$, and $f_P(n) = n + h(n)$ if not.

For increasing $\alpha$ with $\alpha(1) = 1$, the paper's choice of $h(n)$ as the largest
$m \ge 1$ with $\alpha(m) \le n$ satisfies the hypothesis on $h$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 3. -/
public theorem nthNonValue_eq_interleave (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1)) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n =
      if f (h n + 1) ≤ n + h n then n + h n + 1
      else if n + h n ≤ f (h n) then n + h n - 1
      else n + h n := by
  obtain ⟨g, gzero, gpos, hg⟩ := nthNonValue_eq_one_step.exists_strictMono_extension f hf1 hgap
  have heq : nthNonValue f n = nthNonValue g n := by
    simp +contextual only [nthNonValue, gpos]
  rw [heq]
  obtain ⟨hhpos, hleft, hright⟩ := hh n hn
  obtain ⟨k, hk⟩ : ∃ k, h n = k + 1 := ⟨h n - 1, by omega⟩
  rw [hk] at hleft hright ⊢
  have hnext : n < f (k + 2) := by
    exact_mod_cast hright.trans_le (hα (k + 2) (by omega)).2
  have hprev : g k < n + k := by
    cases k with
    | zero =>
      rw [gzero, Nat.add_zero]
      omega
    | succ k =>
      have hle : f (k + 1) ≤ n := by
        exact_mod_cast ((hα (k + 2) (by omega)).1.trans hleft)
      rw [gpos _ (by omega)]
      omega
  split_ifs with hhi hlo
  · rw [Nat.add_assoc]
    apply nthNonValue_of_gap hg gzero
    · rw [gpos _ (by omega)]
      omega
    · rw [gpos _ (by omega)]
      exact (Nat.add_lt_add_right hnext (k + 2)).trans_le (hgap (k + 2) (by omega))
  · rw [show n + (k + 1) - 1 = n + k by omega]
    apply nthNonValue_of_gap hg gzero hprev
    rw [gpos _ (by omega)]
    omega
  · apply nthNonValue_of_gap hg gzero <;> rw [gpos _ (by omega)] <;> omega

/-- **Formula for the $n$-th non-triangular number.** For every integer $n \ge 1$, the $n$-th
smallest positive integer that is not a triangular number $j(j+1)/2$ with $j \ge 1$ is
$n + \lfloor \sqrt{2n} + 1/2 \rfloor$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 3. -/
public theorem nthNonValue_triangular_eq_round (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => j * (j + 1) / 2) n = n + ⌊Real.sqrt (2 * n) + 1 / 2⌋₊ := by
  set s := ⌊Real.sqrt (2 * n) + 1 / 2⌋₊
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : 1 ≤ Real.sqrt (2 * n) := (Real.le_sqrt' one_pos).mpr (by linarith)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast Nat.le_floor (by push_cast; linarith)
  have hfl : (s : ℝ) ≤ Real.sqrt (2 * n) + 1 / 2 := Nat.floor_le (by linarith)
  have hfu : Real.sqrt (2 * n) + 1 / 2 < s + 1 := Nat.lt_floor_add_one _
  -- Rounding gives (s - 1/2)² ≤ 2n < (s + 1/2)², so s(s - 1) < 2n ≤ s(s + 1).
  have hlo : ((s : ℝ) - 1 / 2) ^ 2 ≤ 2 * n :=
    (Real.le_sqrt (by linarith) (by linarith)).mp (by linarith)
  have hhi : (2 * n : ℝ) < ((s : ℝ) + 1 / 2) ^ 2 := (Real.sqrt_lt' (by linarith)).mp (by linarith)
  have hlo' : s * s < 2 * n + s := by
    have : ((s * s : ℕ) : ℝ) < 2 * n + s := by push_cast; nlinarith
    exact_mod_cast this
  have hhi' : 2 * n < s * s + s + 1 := by
    have : ((2 * n : ℕ) : ℝ) < s * s + s + 1 := by push_cast; nlinarith
    exact_mod_cast this
  -- Hence n + s lies strictly between the s-th and (s + 1)-st triangular numbers.
  have hmono : StrictMono (fun j : ℕ => j * (j + 1) / 2) := by
    apply strictMono_nat_of_lt_succ
    intro j
    ring_nf
    omega
  clear_value s
  apply nthNonValue_of_gap hmono (by simp)
  · rw [Nat.mul_add_one]
    omega
  · rw [show (s + 1) * (s + 1 + 1) = s * s + 3 * s + 2 by ring]
    omega

/-- **Formula for the non-square numbers.** For every integer $n \ge 1$, the $n$-th positive
integer that is not a perfect square is $n + \lfloor \sqrt{n} + 1/2 \rfloor$.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 3. -/
public theorem nthNonValue_sq_eq_round (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue (fun j => j ^ 2) n = n + ⌊Real.sqrt n + 1 / 2⌋₊ := by
  let j := ⌊Real.sqrt n + 1 / 2⌋₊
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt n := (Real.le_sqrt' one_pos).mpr (by simpa using hnReal)
  have hj : 1 ≤ j := Nat.le_floor (by push_cast; linarith)
  have hjReal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hfloor : (j : ℝ) ≤ Real.sqrt n + 1 / 2 := Nat.floor_le (by positivity)
  have hfloorSucc : Real.sqrt n + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : ((j : ℝ) - 1 / 2) ^ 2 ≤ (n : ℝ) :=
    (Real.le_sqrt (by linarith) (by positivity)).mp (by linarith)
  have hhi : (n : ℝ) < ((j : ℝ) + 1 / 2) ^ 2 :=
    (Real.sqrt_lt' (by positivity)).mp (by linarith)
  -- The quarter terms give strict bounds between integers, hence j² - j < n ≤ j² + j.
  have hleft : j ^ 2 < n + j := by
    exact_mod_cast (show (j : ℝ) ^ 2 < (n : ℝ) + j by nlinarith only [hlo])
  have hright : n < j ^ 2 + j + 1 := by
    exact_mod_cast (show (n : ℝ) < (j : ℝ) ^ 2 + j + 1 by nlinarith only [hhi])
  have hmono : StrictMono (fun k : ℕ => k ^ 2) := by
    intro a b hab
    exact Nat.pow_lt_pow_left hab (by decide)
  refine nthNonValue_of_gap hmono (by simp) hleft ?_
  change n + j < (j + 1) ^ 2
  rw [show (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 by ring]
  omega

end

end MetaMathlibExt
