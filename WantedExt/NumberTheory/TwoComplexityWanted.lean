/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The 2-complexity of even positive integers

Statements from Pengcheng Zhang, "The 2-Complexity of Even
Positive Integers", *INTEGERS* 24 (2024), Article A109
(<https://math.colgate.edu/~integers/vol24.html>).

The paper's `l`-complexity `‖n‖_l` (for `l > 1` and `n` a
positive multiple of `l`) is the least number of copies of
`l` in an expression for `n` using addition, multiplication
and parentheses; here `CanBuild l k n` says `n` is obtained
from `k` copies of `l`, and `complexityL l n` is the least
such `k` (`0` when `n` is not obtainable, e.g. `l ∤ n`).
Logarithms are real (`Real.logb`). The extracted statements
flatten superscripts (`2m` for `2^m`, `lm` for `l^m`,
`6r` for `6^r`, `105` for `10^5`); the readings used here
were all verified by exhaustive BFS over expressions with
at most 14 copies of `2` (values up to `2^14`), 9 copies of
`3`, and 8 copies of `4`, which confirms every statement
below on that grid (for Theorem 2, the grid reaches
`2^m * 6^r` with `m + 3r ≤ 14` and `2^m * 10^r` with
`m + 4r ≤ 14`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- `CanBuild l k n`: the number `n` can be obtained from
`k` copies of `l` using addition and multiplication
(with arbitrary parentheses). -/
inductive CanBuild (l : ℕ) : ℕ → ℕ → Prop
  | base : CanBuild l 1 l
  | add {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x + y)
  | mul {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x * y)

/-- The paper's `l`-complexity `‖n‖_l`: the least number
of copies of `l` needed to build `n` with `+` and `*`, or
`0` if `n` cannot be built at all. -/
noncomputable def complexityL (l n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, CanBuild l k n then Nat.find h else 0

/-- Every build uses at least one copy. -/
theorem CanBuild.one_le {l k n : ℕ} (h : CanBuild l k n) : 1 ≤ k := by
  induction h with
  | base => exact Nat.le_refl 1
  | add _ _ iha _ => exact Nat.le_add_right_of_le iha
  | mul _ _ iha _ => exact Nat.le_add_right_of_le iha

/-- Specification of `complexityL`: a buildable `n` is
built using exactly `complexityL l n` copies. -/
theorem complexityL_spec {l n : ℕ} (h : ∃ k, CanBuild l k n) :
    CanBuild l (complexityL l n) n := by
  classical
  unfold complexityL
  rw [dif_pos h]
  exact Nat.find_spec h

/-- Minimality of `complexityL`: it is at most the copy
count of any build. -/
theorem complexityL_min_le {l n k : ℕ} (h : CanBuild l k n) :
    complexityL l n ≤ k := by
  classical
  unfold complexityL
  rw [dif_pos ⟨k, h⟩]
  exact Nat.find_min' ⟨k, h⟩ h

/-- `complexityL l n = 0` exactly when `n` cannot be built
from copies of `l` at all. -/
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

/-- The four forms of Corollary 3 / Theorem 1(2) for
`‖n‖₂ = m + 2` where `2^m < n ≤ 2^(m+1)`: (a) three distinct
powers of `2` with largest exponent `m` and smallest at
least `1`; (b) four distinct powers with exponents
`m > m₂ > m₃ > m₄ ≥ 2` and `m + m₄ = m₂ + m₃`; (c)
`2^m + 2^(m-3) + 2^m₂ + 2^(m₂-1)` with `m ≥ m₂ + 3 ≥ 6`;
(d) `2^m + 2^(m-5) + 2^(m-6) + 2^(m-7)` with `m ≥ 10`. -/
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

/-- **Lemma 1**: for `l > 1` and positive `m`, `l^m` is the
largest number obtainable using addition and multiplication
with `m` copies of `l`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 1. -/
theorem_wanted canBuild_max (l m : ℕ) (hl : 1 < l)
    (hm : 1 ≤ m) :
    CanBuild l m (l ^ m) ∧
      ∀ n : ℕ, CanBuild l m n → n ≤ l ^ m

/-- **Proposition 1**: for `l > 1` and `n` a positive
multiple of `l`, `log_l n ≤ ‖n‖_l ≤ l * log_l n - 1`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 1. -/
theorem_wanted logb_le_complexityL_le (l n : ℕ) (hl : 1 < l)
    (hln : l ∣ n) (hn : 1 ≤ n) :
    Real.logb l n ≤ (complexityL l n : ℝ) ∧
      (complexityL l n : ℝ) ≤ l * Real.logb l n - 1

/-- **Corollary 1**: for `l > 1` and `m ≥ m' ≥ 1`,
`‖l^m + l^{m'}‖_l = m + 1`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 1. -/
theorem_wanted complexityL_pow_add_pow (l m m' : ℕ)
    (hl : 1 < l) (h : m' ≤ m) (hm' : 1 ≤ m') :
    complexityL l (l ^ m + l ^ m') = m + 1

/-- **Lemma 3**(1): `‖2^{m₁}‖₂ = m₁`, and
`‖2^{m₁} + 2^{m₂}‖₂ = m₁ + 1` for `m₁ > m₂ ≥ 1`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted complexityL_two_pow_and_add (m1 m2 : ℕ)
    (h : m2 < m1) (hm2 : 1 ≤ m2) :
    complexityL 2 (2 ^ m1) = m1 ∧
      complexityL 2 (2 ^ m1 + 2 ^ m2) = m1 + 1

/-- **Lemma 3**(2): the 2-complexity of a sum of `k`
distinct powers of `2` with largest exponent `m₁` and all
exponents at least `1` is at most `m₁ + k - 1`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted complexityL_sum_two_pow_le (s : Finset ℕ)
    (hs : ∀ e ∈ s, 1 ≤ e) (hne : s.Nonempty) :
    complexityL 2 (∑ e ∈ s, 2 ^ e) ≤ s.max' hne + s.card - 1

/-- **Lemma 3**(3): for positive even `n`,
`log₂ n ≤ ‖n‖₂ ≤ 2 * log₂ n - 1`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted logb_two_bounds (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) :
    Real.logb 2 n ≤ (complexityL 2 n : ℝ) ∧
      (complexityL 2 n : ℝ) ≤ 2 * Real.logb 2 n - 1

/-- **Corollary 2**: if a positive even `n` is not a sum of
one or two distinct powers of `2`, then
`log₂ n + 1 ≤ ‖n‖₂`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 2. -/
theorem_wanted logb_two_add_one_le (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n)
    (hform : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b) :
    Real.logb 2 n + 1 ≤ (complexityL 2 n : ℝ)

/-- **Proposition 2**: for `l > 1`, writing a positive
multiple `n` of `l` uniquely as `n = b + a * l` with `b` a
positive multiple of `l^2` and `0 ≤ a ≤ l - 1`, one has
`‖n‖_l = ‖b‖_l + a`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 2. -/
theorem_wanted complexityL_decomp (l n b a : ℕ) (hl : 1 < l)
    (hn : n = b + a * l) (hb : l ^ 2 ∣ b) (hb0 : 1 ≤ b)
    (ha : a ≤ l - 1) :
    complexityL l n = complexityL l b + a

/-- **Proposition 3** (= **Theorem 1**(1)): for `m ≥ 1` and
positive even `n` with `2^m < n ≤ 2^(m+1)`, `‖n‖₂ = m + 1`
if and only if `n = 2^m + 2^t` for some `1 ≤ t ≤ m`
(the case `t = m` gives `n = 2^(m+1)`).

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 3 and Theorem 1. -/
theorem_wanted complexityL_eq_add_one_iff (m n : ℕ)
    (hm : 1 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1)) :
    complexityL 2 n = m + 1 ↔
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ n = 2 ^ m + 2 ^ t

/-- **Corollary 3**: for `m ≥ 3` and positive even `n` with
`2^m < n ≤ 2^(m+1)`, if `n` is of one of the four forms in
`twoComplexityAddTwoForm`, then `‖n‖₂ = m + 2`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 3. -/
theorem_wanted complexityL_eq_add_two_of_form (m n : ℕ)
    (hm : 3 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1))
    (hform : twoComplexityAddTwoForm m n) :
    complexityL 2 n = m + 2

/-- **Proposition 4** (= **Theorem 1**(2)): for `m ≥ 3` and
positive even `n` with `2^m < n ≤ 2^(m+1)`, `‖n‖₂ = m + 2`
if and only if `n` is of one of the four forms in
`twoComplexityAddTwoForm`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 4 and Theorem 1. -/
theorem_wanted complexityL_eq_add_two_iff (m n : ℕ)
    (hm : 3 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1)) :
    complexityL 2 n = m + 2 ↔ twoComplexityAddTwoForm m n

/-- **Corollary 4**: if a positive even `n`, with
`2^m < n ≤ 2^(m+1)`, is neither a sum of one or two
distinct powers of `2` nor of one of the four forms in
`twoComplexityAddTwoForm`, then `log₂ n + 2 ≤ ‖n‖₂`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 4. -/
theorem_wanted logb_two_add_two_le (m n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1))
    (hpow : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b)
    (hform : ¬ twoComplexityAddTwoForm m n) :
    Real.logb 2 n + 2 ≤ (complexityL 2 n : ℝ)

/-- **Corollary 4**, particular case: if a positive even
`n` is a sum of at least five distinct powers of `2`, then
`log₂ n + 2 ≤ ‖n‖₂`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 4. -/
theorem_wanted logb_two_add_two_le_of_five_powers (n : ℕ)
    (s : Finset ℕ) (h2n : 2 ∣ n) (hn : 1 ≤ n)
    (hs : n = ∑ e ∈ s, 2 ^ e) (hcard : 5 ≤ s.card) :
    Real.logb 2 n + 2 ≤ (complexityL 2 n : ℝ)

/-- **Proposition 5** (= **Theorem 2**(1)), equality range:
`‖2^m * 6^r‖₂ = m + 3r` for `1 ≤ r ≤ 7` and all `m ≥ 0`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 5 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_six_pow_eq (m r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 7) :
    complexityL 2 (2 ^ m * 6 ^ r) = m + 3 * r

/-- **Proposition 5** (= **Theorem 2**(1)), remaining range:
`m + 3r - 1 ≤ ‖2^m * 6^r‖₂ ≤ m + 3r` for `8 ≤ r ≤ 9`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 5 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_six_pow_bounds
    (m r : ℕ) (hr1 : 8 ≤ r) (hr2 : r ≤ 9) :
    m + 3 * r - 1 ≤ complexityL 2 (2 ^ m * 6 ^ r) ∧
      complexityL 2 (2 ^ m * 6 ^ r) ≤ m + 3 * r

/-- **Proposition 6** (= **Theorem 2**(2)), equality range:
`‖2^m * 10^r‖₂ = m + 4r` for `1 ≤ r ≤ 4` and all `m ≥ 0`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 6 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_ten_pow_eq (m r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 4) :
    complexityL 2 (2 ^ m * 10 ^ r) = m + 4 * r

/-- **Proposition 6** (= **Theorem 2**(2)), the case
`r = 5`: `m + 19 ≤ ‖2^m * 10^5‖₂ ≤ m + 20`.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 6 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_ten_pow_five_bounds
    (m : ℕ) :
    m + 19 ≤ complexityL 2 (2 ^ m * 10 ^ 5) ∧
      complexityL 2 (2 ^ m * 10 ^ 5) ≤ m + 20

end MathlibExt.NumberTheory.TwoComplexityWanted
