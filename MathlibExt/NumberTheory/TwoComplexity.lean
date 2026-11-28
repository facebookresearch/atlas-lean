/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Find

/-!
# A lower bound for the 2-complexity of even integers

Following Pengcheng Zhang, *The 2-Complexity of Even Positive Integers*, we classify the values
above half the maximum for a fixed number of copies of two. Applying this classification to a
minimal expression gives the logarithmic lower bound.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- **Numbers built from copies of $l$.** For natural numbers $l$, $k$ and $n$, the number $n$
can be built from $k$ copies of $l$ when $n$ is the value of an expression that uses exactly $k$
copies of $l$, combined by addition and multiplication with arbitrary parentheses. Inductively,
$l$ is built from $1$ copy, and if $x$ is built from $a$ copies and $y$ from $b$ copies, then
$x + y$ and $x y$ are built from $a + b$ copies. -/
inductive CanBuild (l : ℕ) : ℕ → ℕ → Prop
  | base : CanBuild l 1 l
  | add {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x + y)
  | mul {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x * y)

/-- **The $l$-complexity of a natural number.** For natural numbers $l$ and $n$, the
$l$-complexity $\|n\|_l$ of $n$ is the least number $k$ such that $n$ can be built from $k$
copies of $l$ using addition and multiplication (with arbitrary parentheses), and
$\|n\|_l = 0$ if $n$ cannot be built from copies of $l$ at all. -/
noncomputable def complexityL (l n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, CanBuild l k n then Nat.find h else 0

/-- **Every build uses at least one copy.** If $n$ can be obtained from $k$ copies of $l$ using
addition and multiplication, then $k \ge 1$. -/
theorem CanBuild.one_le {l k n : ℕ} (h : CanBuild l k n) : 1 ≤ k := by
  induction h with
  | base => exact Nat.le_refl 1
  | add _ _ iha _ => exact Nat.le_add_right_of_le iha
  | mul _ _ iha _ => exact Nat.le_add_right_of_le iha

/-- **A buildable number is built from as many copies as its $l$-complexity.** For natural
numbers $l$ and $n$, if $n$ can be built from some number of copies of $l$ using addition and
multiplication, then $n$ can be built in this way from $c$ copies of $l$, where $c$ is the
$l$-complexity of $n$. -/
theorem complexityL_spec {l n : ℕ} (h : ∃ k, CanBuild l k n) :
    CanBuild l (complexityL l n) n := by
  classical
  unfold complexityL
  rw [dite_eq_left h]
  exact Nat.find_spec h

/-- **The $l$-complexity is at most the size of any build.** For natural numbers $l$, $k$ and
$n$, if $n$ can be built from $k$ copies of $l$ using addition and multiplication, then the
$l$-complexity of $n$ is at most $k$. -/
theorem complexityL_min_le {l n k : ℕ} (h : CanBuild l k n) :
    complexityL l n ≤ k := by
  classical
  unfold complexityL
  rw [dite_eq_left ⟨k, h⟩]
  exact Nat.find_min' ⟨k, h⟩ h

/-- **The $l$-complexity vanishes exactly on numbers that cannot be built.** For natural
numbers $l$ and $n$, the $l$-complexity of $n$ is $0$ if and only if there is no $k$ such that
$n$ can be built from $k$ copies of $l$ using addition and multiplication. -/
theorem complexityL_eq_zero_iff {l n : ℕ} :
    complexityL l n = 0 ↔ ¬ ∃ k, CanBuild l k n := by
  classical
  by_cases h : ∃ k, CanBuild l k n
  · constructor
    · intro h0
      have hspec := complexityL_spec h
      rw [h0] at hspec
      exact absurd hspec.one_le (by simp)
    · intro hne
      exact absurd h hne
  · simp [complexityL, h]

/-- **Zhang's four exceptional forms.** For natural numbers $m$ and $n$, $n$ has one of the four
exceptional forms for $m$ when one of the following holds:
(a) $n = 2^m + 2^{m_2} + 2^{m_3}$ for some natural numbers $m > m_2 > m_3 \ge 1$;
(b) $n = 2^m + 2^{m_2} + 2^{m_3} + 2^{m_4}$ for some natural numbers $m > m_2 > m_3 > m_4 \ge 2$
with $m + m_4 = m_2 + m_3$;
(c) $n = 2^m + 2^{m-3} + 2^{m_2} + 2^{m_2 - 1}$ for some natural number $m_2$ with
$m \ge m_2 + 3 \ge 6$;
(d) $m \ge 10$ and $n = 2^m + 2^{m-5} + 2^{m-6} + 2^{m-7}$.

These are the forms of Corollary 3 and Theorem 1(2) of Zhang's paper, which concern even $n$
with $2^m < n \le 2^{m+1}$ and 2-complexity $m + 2$. -/
def twoComplexityAddTwoForm (m n : ℕ) : Prop :=
  (∃ m2 m3 : ℕ, m2 < m ∧ m3 < m2 ∧ 1 ≤ m3 ∧
    n = 2 ^ m + 2 ^ m2 + 2 ^ m3) ∨
  (∃ m2 m3 m4 : ℕ, m2 < m ∧ m3 < m2 ∧ m4 < m3 ∧ 2 ≤ m4 ∧
    m + m4 = m2 + m3 ∧
    n = 2 ^ m + 2 ^ m2 + 2 ^ m3 + 2 ^ m4) ∨
  (∃ m2 : ℕ, m2 + 3 ≤ m ∧ 6 ≤ m2 + 3 ∧
    n = 2 ^ m + 2 ^ (m - 3) + 2 ^ m2 + 2 ^ (m2 - 1)) ∨
  (10 ≤ m ∧
    n = 2 ^ m + 2 ^ (m - 5) + 2 ^ (m - 6) + 2 ^ (m - 7))

-- Above half the maximum, the value has the form 2^i + 2^(i+d).
-- Allowing d = 0 includes the maximum itself.
private def BuildBound (k n : ℕ) : Prop :=
  2 * n ≤ 2 ^ k ∨ ∃ i d : ℕ, k = i + d + 1 ∧ n = 2 ^ i * (2 ^ d + 1)

private theorem BuildBound.le_pow {k n : ℕ} (h : BuildBound k n) : n ≤ 2 ^ k := by
  rcases h with h | ⟨i, d, rfl, rfl⟩
  · omega
  · rw [pow_succ, pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by have := Nat.two_pow_pos d; omega)

private theorem BuildBound.scale {k n : ℕ} (h : BuildBound k n) (s : ℕ) :
    BuildBound (s + k) (2 ^ s * n) := by
  rcases h with h | ⟨i, d, rfl, rfl⟩
  · left
    rw [pow_add, mul_left_comm]
    exact Nat.mul_le_mul_left _ h
  · exact Or.inr ⟨s + i, d, by omega, by rw [pow_add, mul_assoc]⟩

private theorem add_bound {a b x y : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) (he : 2 ∣ x + y) : BuildBound (a + b) (x + y) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hab : 2 ^ a + 2 ^ b ≤ 2 ^ (a + b) + 1 := by
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (Nat.one_le_two_pow (n := a))
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le (Nat.one_le_two_pow (n := b))
    rw [pow_add, hu, hv]
    nlinarith only [Nat.zero_le (u * v)]
  rw [pow_succ] at hx hy
  by_cases h : x + y ≤ 2 * 2 ^ (a + b)
  · left
    rw [show a + 1 + (b + 1) = (a + b) + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  · -- The sum is even and at most two above the halfway point.
    exact Or.inr ⟨1, a + b, by omega, by simp only [pow_one]; omega⟩

-- After removing powers of two, the only product of two odd factors greater than one
-- that stays above half the maximum is 3 * 3 = 2^3 + 1.
private theorem odd_parts_bound (d e : ℕ) :
    BuildBound (d + e + 2) ((2 ^ d + 1) * (2 ^ e + 1)) := by
  wlog hde : d ≤ e generalizing d e
  · simpa only [add_comm e d, mul_comm (2 ^ e + 1)] using this e d (by omega)
  rcases d with _ | d
  · exact Or.inr ⟨1, e, by omega, by simp⟩
  by_cases he : e = 1
  · have hd : d = 0 := by omega
    subst d e
    exact Or.inr ⟨0, 3, rfl, rfl⟩
  · left
    have hv : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    have hu : 2 ^ 1 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hu
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hv
    rw [pow_add 2 (d + 1 + e) 2, pow_add 2 (d + 1) e, hu, hv]
    norm_num
    nlinarith only [Nat.zero_le u, Nat.zero_le v, Nat.zero_le (u * v)]

private theorem BuildBound.mul {a b x y : ℕ} (hx : BuildBound a x) (hy : BuildBound b y) :
    BuildBound (a + b) (x * y) := by
  have hx' := hx.le_pow
  have hy' := hy.le_pow
  rcases hx with hx | ⟨i, d, rfl, rfl⟩
  · left
    rw [← mul_assoc, pow_add]
    exact Nat.mul_le_mul hx hy'
  rcases hy with hy | ⟨j, e, rfl, rfl⟩
  · left
    rw [mul_left_comm, pow_add]
    exact Nat.mul_le_mul hx' hy
  · convert (odd_parts_bound d e).scale (i + j) using 1
    · omega
    · rw [pow_add]
      ac_rfl

private theorem build_bound {k n : ℕ} (h : CanBuild 2 k n) : 2 ∣ n ∧ BuildBound k n := by
  induction h with
  | base => exact ⟨dvd_refl _, Or.inr ⟨0, 0, rfl, rfl⟩⟩
  | add hx hy ihx ihy =>
    have he := dvd_add ihx.1 ihy.1
    exact ⟨he, add_bound hx.one_le hy.one_le ihx.2.le_pow ihy.2.le_pow he⟩
  | mul _ _ ihx ihy => exact ⟨dvd_mul_of_dvd_left ihx.1 _, ihx.2.mul ihy.2⟩

private theorem build_even (m : ℕ) : CanBuild 2 (m + 1) (2 * (m + 1)) := by
  induction m with
  | zero => exact CanBuild.base
  | succ m ih => simpa only [Nat.mul_succ] using ih.add CanBuild.base

/-- **A lower bound for the 2-complexity outside sums of two powers of two.** Write
$\|n\|_2$ for the $2$-complexity of $n$. Let $n$ be a positive even integer that cannot be
written as $2^a + 2^b$ with natural numbers $a \le b$. Then $\log_2 n + 1 \le \|n\|_2$.

Since $n$ is even, the hypothesis says that $n$ is neither a power of $2$ nor a sum of two
distinct powers of $2$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 2. -/
theorem logb_two_add_one_le (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n)
    (hform : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b) :
    Real.logb 2 n + 1 ≤ (complexityL 2 n : ℝ) := by
  have hb : ∃ k, CanBuild 2 k n := by
    obtain ⟨m, rfl⟩ := h2n
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    exact ⟨_, build_even m⟩
  obtain h | ⟨i, d, _, h⟩ := (build_bound (complexityL_spec hb)).2
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos (by norm_num) hn')
      (show (2 : ℝ) * n ≤ 2 ^ complexityL 2 n by exact_mod_cast h)
    simpa [Real.logb_mul, hn'.ne', Real.logb_pow, Real.logb_self_eq_one, add_comm] using hl
  · exact (hform ⟨i, i + d, by omega, by rw [h, pow_add]; ring⟩).elim

end MathlibExt.NumberTheory.TwoComplexityWanted
