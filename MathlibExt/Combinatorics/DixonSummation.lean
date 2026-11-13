/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Extended factorial.** For an integer $n$, the extended factorial of $n$ is the rational
number $n!$ when $n \ge 0$ and $0$ when $n < 0$. -/
public def extFact (n : ℤ) : ℚ :=
  if 0 ≤ n then (n.natAbs.factorial : ℚ) else 0

/-- **The extended factorial vanishes at negative integers.** For every integer $n < 0$, the
extended factorial of $n$ is $0$. -/
@[simp] public theorem extFact_of_neg {n : ℤ} (hn : n < 0) : extFact n = 0 := by
  simp [extFact, not_le_of_gt hn]

/-- **The extended factorial of a natural number.** For every natural number $n$, the extended
factorial of $n$ equals the ordinary factorial $n!$. -/
@[simp] public theorem extFact_natCast (n : ℕ) : extFact n = n.factorial := by
  simp [extFact]

/-- **Inverse factorial on the integers.** For an integer $n$, the inverse factorial of $n$ is
the rational number $1/n!$ when $n \ge 0$ and $0$ when $n < 0$. -/
public def invFact (n : ℤ) : ℚ :=
  if 0 ≤ n then 1 / (n.natAbs.factorial : ℚ) else 0

/-- **The inverse factorial vanishes at negative integers.** For every integer $n < 0$, the
inverse factorial of $n$ is $0$. -/
@[simp] public theorem invFact_of_neg {n : ℤ} (hn : n < 0) : invFact n = 0 := by
  simp [invFact, not_le_of_gt hn]

/-- **The inverse factorial at natural numbers.** For every natural number $n$, the inverse
factorial of $n$, viewed as an integer, equals $(n!)^{-1}$ in $\mathbb{Q}$. -/
@[simp] public theorem invFact_natCast (n : ℕ) : invFact n = (n.factorial : ℚ)⁻¹ := by
  simp [invFact]

/-- **Shift identity for the inverse factorial.** For every integer $n$, the inverse
factorial of $n$ equals $n + 1$ times the inverse factorial of $n + 1$, as rational numbers.

For $n \ge 0$ this is $1/n! = (n+1)/(n+1)!$. For $n < 0$ both sides are $0$: the inverse
factorial vanishes at negative integers, and the factor $n + 1$ is $0$ at $n = -1$. -/
public theorem invFact_shift (n : ℤ) : invFact n = (n + 1) * invFact (n + 1) := by
  by_cases hn : n < 0
  · by_cases hn1 : n = -1
    · subst n
      norm_num [invFact]
    · have hn' : n + 1 < 0 := by omega
      simp [invFact, not_le_of_gt hn, not_le_of_gt hn']
  · have hn' : 0 ≤ n := by omega
    have hn1 : 0 ≤ n + 1 := by omega
    have habs : (n + 1).natAbs = n.natAbs + 1 := by omega
    have hcast : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn'
    simp [invFact, hn', hn1, habs, Nat.factorial_succ]
    field_simp
    rw [abs_of_nonneg hcast]

/-- **Integer binomial coefficient.** For an integer $m$ write $m!$ for the extended factorial
and $\frac{1}{m!}$ for the inverse factorial; both are $0$ when $m < 0$. For integers $n$ and
$k$, the integer binomial coefficient is the rational number
$\binom{n}{k} = n! \cdot \frac{1}{k!} \cdot \frac{1}{(n - k)!}$.

These are the source's zero conventions: $\binom{n}{k} = 0$ unless $0 \le k \le n$. -/
public def intBinom (n k : ℤ) : ℚ :=
  extFact n * invFact k * invFact (n - k)

/-- **Integer binomial coefficients of natural numbers.** For natural numbers $k \le n$, the
integer binomial coefficient of $n$ and $k$ equals the ordinary binomial coefficient
$\binom{n}{k}$. -/
@[simp] public theorem intBinom_natCast {n k : ℕ} (hk : k ≤ n) :
    intBinom n k = n.choose k := by
  rw [intBinom, ← Int.ofNat_sub hk]
  simp only [extFact_natCast, invFact_natCast]
  rw [Nat.cast_choose ℚ hk]
  field_simp

/-- **Integer binomial coefficients vanish at negative lower index.** For integers $n$ and
$k$ with $k < 0$, the integer binomial coefficient $\binom{n}{k}$ is $0$. -/
@[simp] public theorem intBinom_of_neg_right {n k : ℤ} (hk : k < 0) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg hk]

/-- **Integer binomial coefficients vanish when the lower index exceeds the upper.** For
integers $n < k$, the integer binomial coefficient $\binom{n}{k}$ is $0$. -/
@[simp] public theorem intBinom_of_lt {n k : ℤ} (h : n < k) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg (show n - k < 0 by omega)]

/-- **Term of Dixon's alternating sum.** Write $\binom{n}{m}$ for the integer binomial coefficient
of integers $n$ and $m$. For integers $a_1, a_2, a_3$ and $k$, the Dixon summand is the rational
number $(-1)^k \binom{2a_1}{a_1 + k} \binom{2a_2}{a_2 + k} \binom{2a_3}{a_3 + k}$. -/
public def dixonSummand (a₁ a₂ a₃ k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k.natAbs * intBinom (2 * a₁) (a₁ + k) *
    (intBinom (2 * a₂) (a₂ + k) * intBinom (2 * a₃) (a₃ + k))

/-- **Bound of the Dixon summation window.** For integers $a_1, a_2, a_3$, the Dixon bound is
$\max(|a_1|, |a_2|, |a_3|)$.

Every integer $k$ whose term in Dixon's alternating sum is nonzero satisfies $|k|$ at most this
bound, so summing over $k$ from minus the bound to the bound covers the whole sum. -/
public def dixonBound (a₁ a₂ a₃ : ℤ) : ℤ :=
  max (|a₁|) (max (|a₂|) (|a₃|))

/-- **The Dixon sum $\upsilon_3$.** For integers $a_1, a_2, a_3$, let
$B = \max(|a_1|, |a_2|, |a_3|)$. Then $\upsilon_3(a_1, a_2, a_3)$ is the rational number

$$\upsilon_3(a_1, a_2, a_3) = \sum_{k=-B}^{B} (-1)^k \prod_{i=1}^{3} \binom{2a_i}{a_i + k},$$

where for integers $n$ and $k$ the binomial coefficient $\binom{n}{k}$ is the ordinary one when
$0 \le k \le n$ and is $0$ otherwise.

Every summand with $|k| > B$ is zero, so this is the alternating sum over all integers $k$. -/
public def upsilon₃ (a₁ a₂ a₃ : ℤ) : ℚ :=
  ∑ k ∈ Finset.Icc (-(dixonBound a₁ a₂ a₃)) (dixonBound a₁ a₂ a₃),
    dixonSummand a₁ a₂ a₃ k

public example : extFact (-3 : ℤ) = 0 := by
  simp [extFact]

public example : extFact (0 : ℤ) = 1 := by
  simp [extFact]

public example : extFact (5 : ℤ) = 120 := by
  have hle : (0 : ℤ) ≤ 5 := by decide
  have habs : (5 : ℤ).natAbs = 5 := rfl
  have hfac : Nat.factorial 5 = 120 := by decide
  simp [extFact, hle, habs, hfac]

public example : invFact (-2 : ℤ) = 0 := by
  simp [invFact]

public example : invFact (0 : ℤ) = 1 := by
  simp [invFact]

public example : invFact (3 : ℤ) = 1 / 6 := by
  have hle : (0 : ℤ) ≤ 3 := by decide
  have habs : (3 : ℤ).natAbs = 3 := rfl
  have hfac : Nat.factorial 3 = 6 := by decide
  simp [invFact, hle, habs, hfac]

public example : intBinom (4 : ℤ) (2 : ℤ) = 6 := by
  have h4 : extFact (4 : ℤ) = 24 := by
    have hle : (0 : ℤ) ≤ 4 := by decide
    have habs : (4 : ℤ).natAbs = 4 := rfl
    have hfac : Nat.factorial 4 = 24 := by decide
    simp [extFact, hle, habs, hfac]
  have h2 : invFact (2 : ℤ) = 1 / 2 := by
    have hle : (0 : ℤ) ≤ 2 := by decide
    have habs : (2 : ℤ).natAbs = 2 := rfl
    have hfac : Nat.factorial 2 = 2 := by decide
    simp [invFact, hle, habs, hfac]
  simp [intBinom, h4, h2]
  norm_num

public example : upsilon₃ (0 : ℤ) 0 0 = 1 := by
  have hbound : dixonBound (0 : ℤ) 0 0 = 0 := by decide
  have h0 : extFact (0 : ℤ) = 1 := by simp [extFact]
  have hi0 : invFact (0 : ℤ) = 1 := by simp [invFact]
  simp [upsilon₃, hbound, dixonSummand, intBinom, h0, hi0]

private def dixon_kernel (a b c k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
    invFact (b + k) * invFact (b - k) * invFact (c + k) * invFact (c - k)

private def dixon_phi (a b c : ℤ) : ℚ :=
  extFact (a + b + c) * invFact (a + b) * invFact (a + c) *
    invFact (b + c) * invFact a * invFact b * invFact c

private def dixon_certificate (a b c k : ℤ) : ℚ :=
  -((-1 : ℚ) ^ k) / (2 * (a + b + c + 1)) *
    invFact (a + k - 1) * invFact (a - k) *
    invFact (b + k - 1) * invFact (b - k) *
    invFact (c + k) * invFact (c + 1 - k) / dixon_phi a b c

private lemma dixon_sign (k : ℤ) : (-1 : ℚ) ^ k.natAbs = (-1 : ℚ) ^ k := by
  rcases Int.even_or_odd k with he | ho
  · have he' : Even k.natAbs := he.natAbs
    rw [he'.neg_one_pow, he.neg_one_zpow]
  · have ho' : Odd k.natAbs := ho.natAbs
    rw [ho'.neg_one_pow, ho.neg_one_zpow]

private lemma dixon_intBinom_two (a k : ℤ) :
    intBinom (2 * a) (a + k) =
      extFact (2 * a) * invFact (a + k) * invFact (a - k) := by
  unfold intBinom
  rw [show 2 * a - (a + k) = a - k by ring]

private lemma dixon_summand_eq (a b c k : ℤ) :
    dixonSummand a b c k =
      extFact (2 * a) * extFact (2 * b) * extFact (2 * c) * dixon_kernel a b c k := by
  unfold dixonSummand
  rw [dixon_sign, dixon_intBinom_two, dixon_intBinom_two, dixon_intBinom_two]
  unfold dixon_kernel
  ring

private lemma dixon_kernel_eq_zero_of_not_mem (a b c k : ℤ)
    (hk : k ∉ Finset.Icc (-a) a) : dixon_kernel a b c k = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · rw [dixon_kernel, invFact_of_neg (show a + k < 0 by omega)]
    ring
  · rw [dixon_kernel, invFact_of_neg (show a - k < 0 by omega)]
    ring

private lemma dixon_le_bound (a b c : ℤ) : a ≤ dixonBound a b c := by
  unfold dixonBound
  exact (le_abs_self a).trans (le_max_left _ _)

private lemma dixon_sum_window (a b c : ℤ) :
    (∑ k ∈ Finset.Icc (-(dixonBound a b c)) (dixonBound a b c),
      dixon_kernel a b c k) =
      ∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k := by
  symm
  apply Finset.sum_subset
  · apply Finset.Icc_subset_Icc
    · have h := dixon_le_bound a b c
      omega
    · exact dixon_le_bound a b c
  · intro k _ hk
    exact dixon_kernel_eq_zero_of_not_mem a b c k hk

private lemma dixon_extFact_mul_invFact {n : ℤ} (hn : 0 ≤ n) :
    extFact n * invFact n = 1 := by
  simp [extFact, invFact, hn]
  field_simp

private lemma dixon_invFact_mul_neg (k : ℤ) (hk : k ≠ 0) :
    invFact k * invFact (-k) = 0 := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · rw [invFact_of_neg hk]
    ring
  · rw [invFact_of_neg (show -k < 0 by omega)]
    ring

private lemma dixon_base (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b 0 k) = dixon_phi a b 0 := by
  have hzero : (0 : ℤ) ∈ Finset.Icc (-a) a := by
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.sum_eq_single 0]
  · have hab : 0 ≤ a + b := by omega
    have hcancel := dixon_extFact_mul_invFact hab
    unfold dixon_kernel dixon_phi
    simp only [zpow_zero, one_mul, add_zero, sub_zero]
    rw [hcancel]
    have hi0 : invFact 0 = 1 := by norm_num [invFact]
    rw [hi0]
    ring
  · intro k _ hk
    unfold dixon_kernel
    rw [zero_add, zero_sub]
    have hzero' := dixon_invFact_mul_neg k hk
    calc
      (-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
          invFact (b + k) * invFact (b - k) * invFact k * invFact (-k) =
          ((-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
            invFact (b + k) * invFact (b - k)) * (invFact k * invFact (-k)) := by ring
      _ = 0 := by rw [hzero']; ring
  · simp [hzero]

private lemma dixon_invFact_pos {n : ℤ} (hn : 0 ≤ n) : 0 < invFact n := by
  unfold invFact
  split
  · positivity
  · contradiction

private lemma dixon_extFact_pos {n : ℤ} (hn : 0 ≤ n) : 0 < extFact n := by
  unfold extFact
  split
  · positivity
  · contradiction

private lemma dixon_phi_pos (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 < dixon_phi a b c := by
  have h₀ := dixon_extFact_pos (show 0 ≤ a + b + c by omega)
  have h₁ := dixon_invFact_pos (show 0 ≤ a + b by omega)
  have h₂ := dixon_invFact_pos (show 0 ≤ a + c by omega)
  have h₃ := dixon_invFact_pos (show 0 ≤ b + c by omega)
  have h₄ := dixon_invFact_pos ha
  have h₅ := dixon_invFact_pos hb
  have h₆ := dixon_invFact_pos hc
  unfold dixon_phi
  positivity

private lemma dixon_extFact_succ (n : ℤ) (hn : 0 ≤ n) :
    extFact (n + 1) = (n + 1) * extFact n := by
  have hn1 : 0 ≤ n + 1 := by omega
  have habs : (n + 1).natAbs = n.natAbs + 1 := by omega
  simp [extFact, hn, hn1, habs, Nat.factorial_succ]

private lemma dixon_phi_succ (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    dixon_phi a b (c + 1) =
      dixon_phi a b c * (a + b + c + 1) /
        ((a + c + 1) * (b + c + 1) * (c + 1)) := by
  have h₀ : ((a + c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  have h₁ : ((b + c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  have h₂ : ((c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  unfold dixon_phi
  rw [show a + b + (c + 1) = (a + b + c) + 1 by ring,
    dixon_extFact_succ _ (by omega)]
  rw [show a + (c + 1) = a + c + 1 by ring,
    show b + (c + 1) = b + c + 1 by ring]
  rw [invFact_shift (a + c), invFact_shift (b + c), invFact_shift c]
  field_simp
  push_cast
  ring

private lemma dixon_invFact_pred (n : ℤ) : invFact (n - 1) = n * invFact n := by
  have h := invFact_shift (n - 1)
  rw [show n - 1 + 1 = n by ring] at h
  rw [h]
  push_cast
  ring

private lemma dixon_sign_succ (k : ℤ) : (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k) := by
  rw [zpow_add_one₀ (by norm_num) k]
  ring

private lemma dixon_wz_pointwise (a b c k : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    dixon_kernel a b (c + 1) k / dixon_phi a b (c + 1) -
        dixon_kernel a b c k / dixon_phi a b c =
      dixon_certificate a b c (k + 1) - dixon_certificate a b c k := by
  have hphi : dixon_phi a b c ≠ 0 := (dixon_phi_pos a b c ha hb hc).ne'
  have hs : (0 : ℚ) < (a : ℚ) + b + c + 1 := by positivity
  have hac : (0 : ℚ) < (a : ℚ) + c + 1 := by positivity
  have hbc : (0 : ℚ) < (b : ℚ) + c + 1 := by positivity
  have hc1 : (0 : ℚ) < (c : ℚ) + 1 := by positivity
  rw [dixon_phi_succ a b c ha hb hc]
  unfold dixon_kernel dixon_certificate
  rw [dixon_sign_succ]
  rw [show a + (k + 1) - 1 = a + k by ring,
    show a - (k + 1) = (a - k) - 1 by ring,
    show b + (k + 1) - 1 = b + k by ring,
    show b - (k + 1) = (b - k) - 1 by ring,
    show c + (k + 1) = c + 1 + k by ring,
    show c + 1 - (k + 1) = c - k by ring]
  rw [dixon_invFact_pred (a - k), dixon_invFact_pred (b - k),
    dixon_invFact_pred (a + k), dixon_invFact_pred (b + k),
    invFact_shift (c - k), invFact_shift (c + k)]
  rw [show c - k + 1 = c + 1 - k by ring,
    show c + k + 1 = c + 1 + k by ring]
  field_simp [hphi, hs.ne', hac.ne', hbc.ne', hc1.ne']
  push_cast
  ring

private lemma dixon_sum_Icc_sub (G : ℤ → ℚ) (a b : ℤ) (hab : a ≤ b + 1) :
    ∑ k ∈ Finset.Icc a b, (G (k + 1) - G k) = G (b + 1) - G a := by
  have key : ∀ n : ℤ, a - 1 ≤ n →
      ∑ k ∈ Finset.Icc a n, (G (k + 1) - G k) = G (n + 1) - G a := by
    intro n hn
    induction n, hn using Int.leInduction with
    | base =>
      have he : Finset.Icc a (a - 1) = (∅ : Finset ℤ) := by
        apply Finset.Icc_eq_empty
        omega
      rw [he, Finset.sum_empty, sub_add_cancel, sub_self]
    | succ n _ ih =>
      have hmem : n + 1 ∉ Finset.Icc a n := by
        simp only [Finset.mem_Icc]
        omega
      have hins : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hins, Finset.sum_insert hmem, ih]
      ring
  exact key b (by omega)

private lemma dixon_certificate_top (a b c : ℤ) :
    dixon_certificate a b c (a + 1) = 0 := by
  unfold dixon_certificate
  rw [show a - (a + 1) = -1 by ring,
    invFact_of_neg (show (-1 : ℤ) < 0 by norm_num)]
  ring

private lemma dixon_certificate_bottom (a b c : ℤ) :
    dixon_certificate a b c (-a) = 0 := by
  unfold dixon_certificate
  rw [show a + -a - 1 = -1 by ring,
    invFact_of_neg (show (-1 : ℤ) < 0 by norm_num)]
  ring

private lemma dixon_normalized_sum (a b c : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k) / dixon_phi a b c = 1 := by
  induction c, hc using Int.leInduction with
  | base =>
    rw [dixon_base a b ha hb]
    exact div_self (dixon_phi_pos a b 0 ha hb (by omega)).ne'
  | succ c hc ih =>
    have hsum :
        (∑ k ∈ Finset.Icc (-a) a,
            (dixon_kernel a b (c + 1) k / dixon_phi a b (c + 1) -
              dixon_kernel a b c k / dixon_phi a b c)) = 0 := by
      calc
        _ = ∑ k ∈ Finset.Icc (-a) a,
            (dixon_certificate a b c (k + 1) - dixon_certificate a b c k) := by
              apply Finset.sum_congr rfl
              intro k _
              exact dixon_wz_pointwise a b c k ha hb hc
        _ = dixon_certificate a b c (a + 1) - dixon_certificate a b c (-a) :=
          dixon_sum_Icc_sub _ _ _ (by omega)
        _ = 0 := by rw [dixon_certificate_top, dixon_certificate_bottom, sub_self]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsum
    exact (sub_eq_zero.mp hsum).trans ih

private lemma dixon_kernel_sum (a b c : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k) = dixon_phi a b c := by
  apply (div_eq_one_iff_eq (dixon_phi_pos a b c ha hb hc).ne').mp
  exact dixon_normalized_sum a b c ha hb hc

private lemma dixon_nonneg (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    upsilon₃ a b c =
      extFact (2 * a) * extFact (2 * b) * extFact (2 * c) * dixon_phi a b c := by
  unfold upsilon₃
  simp_rw [dixon_summand_eq]
  rw [← Finset.mul_sum, dixon_sum_window, dixon_kernel_sum a b c ha hb hc]

private lemma dixon_upsilon_of_prefactor_eq_zero (a b c : ℤ)
    (h : extFact (2 * a) * extFact (2 * b) * extFact (2 * c) = 0) :
    upsilon₃ a b c = 0 := by
  unfold upsilon₃
  apply Finset.sum_eq_zero
  intro k _
  rw [dixon_summand_eq, h, zero_mul]

/-- **Dixon's summation theorem.** For an integer $m$ write $m!$ for the extended factorial
and $\frac{1}{m!}$ for the inverse factorial; both are $0$ when $m < 0$. For all integers
$a_1, a_2, a_3$, the Dixon sum $\Upsilon_3(a_1, a_2, a_3)$ equals
$$
(2a_1)!\,(2a_2)!\,(2a_3)!\,(a_1 + a_2 + a_3)! \cdot
\frac{1}{(a_1 + a_2)!} \cdot \frac{1}{(a_1 + a_3)!} \cdot \frac{1}{(a_2 + a_3)!} \cdot
\frac{1}{a_1!} \cdot \frac{1}{a_2!} \cdot \frac{1}{a_3!}.
$$

Proves `Wanted` entry `dixon_summation`.

Proof: a Wilf–Zeilberger pair. For $a = a_1 \ge 0$ and $b = a_2 \ge 0$ the normalized summand
in $c = a_3$ has the certificate ratio
$R(c, k) = -\frac{(a + k)(b + k)}{2(c - k + 1)(a + b + c + 1)}$; induction on $c$ telescopes
over the fixed window $[-a, a]$. Negative arguments make both sides zero.

Source: Abdesselam, arXiv:1903.11147v2, Proposition (Dixon), TeX lines 502-512.
-/
public theorem dixon_summation (a₁ a₂ a₃ : ℤ) :
  upsilon₃ a₁ a₂ a₃ =
    extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) *
      extFact (a₁ + a₂ + a₃) * invFact (a₁ + a₂) * invFact (a₁ + a₃) *
      invFact (a₂ + a₃) * invFact a₁ * invFact a₂ * invFact a₃ := by
  by_cases ha : a₁ < 0
  · have hzero : extFact (2 * a₁) = 0 := extFact_of_neg (by omega)
    have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
      rw [hzero]
      ring
    rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
    ring
  · by_cases hb : a₂ < 0
    · have hzero : extFact (2 * a₂) = 0 := extFact_of_neg (by omega)
      have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
        rw [hzero]
        ring
      rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
      ring
    · by_cases hc : a₃ < 0
      · have hzero : extFact (2 * a₃) = 0 := extFact_of_neg (by omega)
        have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
          rw [hzero]
          ring
        rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
        ring
      · have ha' : 0 ≤ a₁ := by omega
        have hb' : 0 ≤ a₂ := by omega
        have hc' : 0 ≤ a₃ := by omega
        rw [dixon_nonneg a₁ a₂ a₃ ha' hb' hc']
        unfold dixon_phi
        ring

end MetaMathlibExt
