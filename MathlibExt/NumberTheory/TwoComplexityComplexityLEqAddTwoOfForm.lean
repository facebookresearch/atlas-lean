/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.TwoComplexityMax
public import MathlibExt.NumberTheory.TwoComplexitySum

/-!
# Four forms of even numbers with 2-complexity `m + 2`

The theorem `complexityL_eq_add_two_of_form` gives the 2-complexity of the four exceptional forms.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive Integers",
*INTEGERS* 24 (2024), Article A109 (<https://math.colgate.edu/~integers/vol24.html>), Corollary 3.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private theorem scale_build {k n : ℕ} (h : CanBuild 2 k n) (d : ℕ) :
    CanBuild 2 (k + d) (n * 2 ^ d) := by
  induction d with
  | zero => simpa using h
  | succ d ih => simpa only [pow_succ, ← mul_assoc, Nat.add_succ] using ih.mul CanBuild.base

private theorem build_three (m a b : ℕ) (ha : a < m) (hb : b < a) (hpos : 1 ≤ b) :
    CanBuild 2 (m + 2) (2 ^ m + 2 ^ a + 2 ^ b) := by
  have h := scale_build
    ((scale_build ((canBuild_max 2 (m - a + 1) (by decide) (by omega)).1.add
      CanBuild.base) (a - b)).add CanBuild.base) (b - 1)
  change CanBuild 2 _ (((2 ^ (m - a + 1) + 2 ^ 1) * 2 ^ (a - b) + 2 ^ 1) *
    2 ^ (b - 1)) at h
  have h₁ : m - a + 1 + (a - b) + (b - 1) = m := by omega
  have h₂ : 1 + (a - b) + (b - 1) = a := by omega
  have h₃ : 1 + (b - 1) = b := by omega
  convert h using 1
  · omega
  · simp only [add_mul, ← pow_add, h₁, h₂, h₃]

private theorem build_balanced (m a b c : ℕ) (hca : c ≤ a)
    (hcb : c ≤ b) (hpos : 2 ≤ c) (heq : m + c = a + b) :
    CanBuild 2 (m + 2) (2 ^ m + 2 ^ a + 2 ^ b + 2 ^ c) := by
  have h := scale_build
    (((canBuild_max 2 (a - c + 1) (by decide) (by omega)).1.add CanBuild.base).mul
      ((canBuild_max 2 (b - c + 1) (by decide) (by omega)).1.add CanBuild.base)) (c - 2)
  change CanBuild 2 _ ((2 ^ (a - c + 1) + 2 ^ 1) * (2 ^ (b - c + 1) + 2 ^ 1) *
    2 ^ (c - 2)) at h
  have h₁ : a - c + 1 + (b - c + 1) + (c - 2) = m := by omega
  have h₂ : a - c + 1 + 1 + (c - 2) = a := by omega
  have h₃ : 1 + (b - c + 1) + (c - 2) = b := by omega
  have h₄ : 1 + 1 + (c - 2) = c := by omega
  convert h using 1
  · omega
  · simp only [add_mul, mul_add, ← pow_add]
    rw [h₁, h₂, h₃, h₄]
    ac_rfl

private theorem build_six_form (m a : ℕ) (ha : a + 3 ≤ m) (hpos : 3 ≤ a) :
    CanBuild 2 (m + 2) (2 ^ m + 2 ^ (m - 3) + 2 ^ a + 2 ^ (a - 1)) := by
  have h6 : CanBuild 2 3 6 := CanBuild.base.add (CanBuild.base.add CanBuild.base)
  have h := scale_build (h6.mul ((scale_build h6 (m - a - 2)).add CanBuild.base)) (a - 3)
  have he : 6 * (6 * 2 ^ (m - a - 2) + 2) * 2 ^ (a - 3) =
      (2 ^ 5 + 2 ^ 2) * 2 ^ (m - a - 2) * 2 ^ (a - 3) +
        (2 ^ 3 + 2 ^ 2) * 2 ^ (a - 3) := by ring
  rw [he] at h
  have h₁ : 5 + (m - a - 2) + (a - 3) = m := by omega
  have h₂ : 2 + (m - a - 2) + (a - 3) = m - 3 := by omega
  have h₃ : 3 + (a - 3) = a := by omega
  have h₄ : 2 + (a - 3) = a - 1 := by omega
  convert h using 1
  · omega
  · simp only [add_mul, ← pow_add]
    rw [h₁, h₂, h₃, h₄]
    ac_rfl

private theorem build_fixed_form (m : ℕ) (hm : 10 ≤ m) :
    CanBuild 2 (m + 2) (2 ^ m + 2 ^ (m - 5) + 2 ^ (m - 6) + 2 ^ (m - 7)) := by
  have h6 : CanBuild 2 3 6 := CanBuild.base.add (CanBuild.base.add CanBuild.base)
  have h1080 : CanBuild 2 12 1080 :=
    ((canBuild_max 2 4 (by decide) (by decide)).1.add CanBuild.base).mul
      (((canBuild_max 2 3 (by decide) (by decide)).1.add CanBuild.base).mul h6)
  have h := scale_build h1080 (m - 10)
  have he : (1080 : ℕ) = 2 ^ 10 + 2 ^ 5 + 2 ^ 4 + 2 ^ 3 := by decide
  rw [he] at h
  have h₁ : 10 + (m - 10) = m := by omega
  have h₂ : 5 + (m - 10) = m - 5 := by omega
  have h₃ : 4 + (m - 10) = m - 6 := by omega
  have h₄ : 3 + (m - 10) = m - 7 := by omega
  convert h using 1
  · omega
  · simp only [add_mul, ← pow_add, h₁, h₂, h₃, h₄]

private theorem largest_exponent (m n a b : ℕ) (hab : a ≤ b)
    (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1)) (heq : n = 2 ^ a + 2 ^ b) : b = m := by
  have hle : b ≤ m := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show m + 1 ≤ b by omega)
    have hpos := Nat.two_pow_pos a
    omega
  have hge : m ≤ b := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show b + 1 ≤ m by omega)
    have hp' := Nat.pow_le_pow_right (n := 2) (by decide) hab
    rw [pow_succ] at hp
    omega
  omega

private theorem not_two_powers (m n c : ℕ)
    (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1))
    (hc1 : 2 ^ m + 2 ^ c < n) (hc2 : n < 2 ^ m + 2 ^ (c + 1)) :
    ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b := by
  rintro ⟨a, b, hab, heq⟩
  have hb := largest_exponent m n a b hab hn1 hn2 heq
  subst b
  by_cases hac : a ≤ c
  · have hp := Nat.pow_le_pow_right (n := 2) (by decide) hac
    omega
  · have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show c + 1 ≤ a by omega)
    omega

private theorem two_small_powers (a b c : ℕ) (hb : b < a) (hc : c < b) :
    2 ^ b + 2 ^ c < 2 ^ a := by
  have hp := Nat.pow_lt_pow_right (a := 2) (by decide) hc
  have hp' := Nat.pow_le_pow_right (n := 2) (by decide) (show b + 1 ≤ a by omega)
  rw [pow_succ] at hp'
  omega

private theorem form_interval (m n : ℕ) (hform : twoComplexityAddTwoForm m n) :
    ∃ c : ℕ, 2 ^ m + 2 ^ c < n ∧ n < 2 ^ m + 2 ^ (c + 1) := by
  rcases hform with ⟨a, b, _, hb, _, rfl⟩ | ⟨a, b, c, _, hb, hc, _, _, rfl⟩ |
    ⟨a, ha, hpos, rfl⟩ | ⟨hm, rfl⟩
  · refine ⟨a, ?_, ?_⟩
    · have hp := Nat.two_pow_pos b
      omega
    · have hp := Nat.pow_lt_pow_right (a := 2) (by decide) hb
      rw [pow_succ]
      omega
  · refine ⟨a, ?_, ?_⟩
    · have hp := Nat.two_pow_pos b
      have hp' := Nat.two_pow_pos c
      omega
    · have hp := two_small_powers a b c hb hc
      rw [pow_succ]
      omega
  · by_cases heq : a = m - 3
    · refine ⟨a + 1, ?_, ?_⟩
      · rw [← heq, pow_succ]
        have hp := Nat.two_pow_pos (a - 1)
        omega
      · rw [← heq, pow_succ, pow_succ]
        have hp := Nat.pow_lt_pow_right (a := 2) (by decide) (show a - 1 < a by omega)
        omega
    · refine ⟨m - 3, ?_, ?_⟩
      · have hp := Nat.two_pow_pos a
        have hp' := Nat.two_pow_pos (a - 1)
        omega
      · have hp := two_small_powers (m - 3) a (a - 1) (by omega) (by omega)
        rw [pow_succ]
        omega
  · refine ⟨m - 5, ?_, ?_⟩
    · have hp := Nat.two_pow_pos (m - 6)
      have hp' := Nat.two_pow_pos (m - 7)
      omega
    · have hp := two_small_powers (m - 5) (m - 6) (m - 7) (by omega) (by omega)
      rw [pow_succ]
      omega

private theorem build_form (m n : ℕ) (hform : twoComplexityAddTwoForm m n) :
    CanBuild 2 (m + 2) n := by
  rcases hform with ⟨a, b, ha, hb, hpos, rfl⟩ | ⟨a, b, c, _, hb, hc, hpos, heq, rfl⟩ |
    ⟨a, ha, hpos, rfl⟩ | ⟨hm, rfl⟩
  · exact build_three m a b ha hb hpos
  · exact build_balanced m a b c (by omega) (by omega) hpos heq
  · exact build_six_form m a ha (by omega)
  · exact build_fixed_form m hm

/-- **Four forms of even numbers with 2-complexity $m + 2$.** Write $\|n\|_2$ for the
2-complexity of $n$. Let $m \ge 3$ and let $n$ be an even natural number with
$2^m < n \le 2^{m+1}$. Suppose that $n$ has one of the following forms, where all exponents
are natural numbers:
(a) $n = 2^m + 2^{m_2} + 2^{m_3}$ with $m > m_2 > m_3 \ge 1$;
(b) $n = 2^m + 2^{m_2} + 2^{m_3} + 2^{m_4}$ with $m > m_2 > m_3 > m_4 \ge 2$ and
$m + m_4 = m_2 + m_3$;
(c) $n = 2^m + 2^{m-3} + 2^{m_2} + 2^{m_2-1}$ with $m \ge m_2 + 3 \ge 6$;
(d) $n = 2^m + 2^{m-5} + 2^{m-6} + 2^{m-7}$ with $m \ge 10$.
Then $\|n\|_2 = m + 2$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 3. -/
public theorem complexityL_eq_add_two_of_form (m n : ℕ)
    (hm : 3 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1))
    (hform : twoComplexityAddTwoForm m n) :
    complexityL 2 n = m + 2 := by
  have hn : 1 ≤ n := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) hm
    norm_num at hp
    omega
  obtain ⟨c, hc1, hc2⟩ := form_interval m n hform
  have hlog := logb_two_add_one_le n h2n hn (not_two_powers m n c hn1 hn2 hc1 hc2)
  have hlt : (m : ℝ) < Real.logb 2 n := by
    have h := Real.logb_lt_logb (b := 2) (by norm_num) (pow_pos (by norm_num) m)
      (show (2 : ℝ) ^ m < n by exact_mod_cast hn1)
    simpa only [Real.logb_pow, Real.logb_self_eq_one (b := 2) (by norm_num), mul_one] using h
  have hreal : (m : ℝ) + 1 < (complexityL 2 n : ℝ) := by linarith
  have hnat : m + 1 < complexityL 2 n := by exact_mod_cast hreal
  exact Nat.le_antisymm (complexityL_min_le (build_form m n hform)) (by omega)

end MathlibExt.NumberTheory.TwoComplexityWanted
