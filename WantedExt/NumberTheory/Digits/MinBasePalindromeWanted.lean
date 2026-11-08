/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Minimum-base palindromic representations of powers of 2

Statements from D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69
(arXiv:2401.07351).

The base-`b` representation `(c_k, …, c_0)_b` of `N` (leading digit nonzero) is
Mathlib's little-endian `Nat.digits b N = [c_0, …, c_k]`; `N` is a palindrome in
base `b` when this list is a `List.Palindrome`. A `(k+1)`-digit representation
has `(Nat.digits b N).length = k + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `b(N)`: the smallest base `b > 1` in which `N` is a palindrome (it exists:
`N = (N)_{N+1}` is a one-digit palindrome).

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1. -/
public noncomputable def minPalindromicBase (N : ℕ) : ℕ :=
  sInf {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}

/-- `N` has a base-`b` representation in binomial form with at least two digits:
`N = (α C(k,k), α C(k,k-1), …, α C(k,0))_b` for some `α ≥ 1` and `k ≥ 1` (the
one-digit case `k = 0` is excluded as degenerate).

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1
(definition of binomial form). -/
public def HasBinomialForm (b N : ℕ) : Prop :=
  ∃ α k : ℕ, 1 ≤ α ∧ 1 ≤ k ∧ Nat.digits b N = (List.range (k + 1)).map fun i => α * k.choose i

/-- Characteristic value `b(2) = 3`: `2 = (1,0)_2` is not a palindrome, `2 = (2)_3` is.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Table 1. -/
public theorem minPalindromicBase_two : minPalindromicBase 2 = 3 := by
  have h3 : (3 : ℕ) ∈ {b | 2 ≤ b ∧ (Nat.digits b 2).Palindrome} := by
    refine ⟨by norm_num, ?_⟩
    rw [show Nat.digits 3 2 = [2] by norm_num]
    exact List.Palindrome.singleton 2
  unfold minPalindromicBase
  apply le_antisymm (Nat.sInf_le h3)
  apply le_csInf ⟨3, h3⟩
  rintro b ⟨hb, hp⟩
  by_contra h
  have hb2 : b = 2 := by omega
  subst hb2
  rw [show Nat.digits 2 2 = [0, 1] by norm_num] at hp
  have := hp.reverse_eq
  simp at this

/-- Characteristic example: `2023 = (7, 14, 7)_16 = 7 · (1, 2, 1)_16` is in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1. -/
public theorem hasBinomialForm_16_2023 : HasBinomialForm 16 2023 :=
  ⟨7, 2, by norm_num, by norm_num, by norm_num [List.range_succ]⟩

/-- Brown: if `b(N) = N - 1` (`N ≥ 1`), then `N ∈ {3, 4, 6}` or `N > 6` is prime.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 1
(`integers-2024-A69-thm-1`), credited to K. Brown. -/
public theorem_wanted minPalindromicBase_eq_pred (N : ℕ) (hN : 1 ≤ N)
    (h : minPalindromicBase N = N - 1) : N = 3 ∨ N = 4 ∨ N = 6 ∨ (6 < N ∧ N.Prime)

/-- If `α ≥ 1`, `α C(k, ⌈k/2⌉) < b` and `N = α (1 + b)^k`, then `N` has the binomial
form `α (C(k,k), C(k,k-1), …, C(k,0))_b`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 1
(`integers-2024-A69-lem-1`). -/
public theorem_wanted digits_mul_one_add_pow (α k b : ℕ) (hα : 1 ≤ α)
    (h : α * k.choose ((k + 1) / 2) < b) :
    Nat.digits b (α * (1 + b) ^ k) = (List.range (k + 1)).map fun i => α * k.choose i

/-- If `n = xk + r` with `k ≥ 1`, `r ≥ 0` and `2^r C(k, ⌈k/2⌉) < 2^x - 1`, then `2^n`
has a representation in base `2^x - 1` in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 1
(`integers-2024-A69-cor-1`). -/
public theorem_wanted hasBinomialForm_two_pow (n x k r : ℕ) (hk : 1 ≤ k) (hn : n = x * k + r)
    (h : 2 ^ r * k.choose ((k + 1) / 2) < 2 ^ x - 1) : HasBinomialForm (2 ^ x - 1) (2 ^ n)

/-- If the base-`b` representation of `2^n` is a multiple `α` of a binomial
representation with at least two digits (`k ≥ 1`), then `b = 2^x - 1` for some
`x ≤ n` and `α` is a power of `2`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 2
(`integers-2024-A69-lem-2`). -/
public theorem_wanted binomialForm_two_pow_base (n b α k : ℕ) (hb : 2 ≤ b) (hα : 1 ≤ α)
    (hk : 1 ≤ k) (h : Nat.digits b (2 ^ n) = (List.range (k + 1)).map fun i => α * k.choose i) :
    (∃ x ≤ n, b = 2 ^ x - 1) ∧ ∃ i, α = 2 ^ i

/-- A palindromic representation with an even number of digits
`(c_{2k+1}, …, c_0)_b` of `N` forces `b + 1 ∣ N`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 3
(`integers-2024-A69-lem-3`). -/
public theorem_wanted succ_dvd_of_palindrome_even_length (N b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b N).Palindrome) (he : Even (Nat.digits b N).length) : b + 1 ∣ N

/-- If `2^n` has a palindromic representation in base `b` with an even number of
digits, then `b = 2^x - 1` for some `x`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 2
(`integers-2024-A69-cor-2`). -/
public theorem_wanted base_eq_two_pow_sub_one_of_palindrome (n b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b (2 ^ n)).Palindrome) (he : Even (Nat.digits b (2 ^ n)).length) :
    ∃ x, b = 2 ^ x - 1

/-- `2^n` has a 3-digit palindromic representation in base `b` if and only if
`b² + 1 ≤ 2^n ≤ b³ - 1` and `(1/b)⌊2^n/b⌋ - (b-1)/b ≤ c ≤ (1/b)⌊2^n/b⌋`, where
`c = 2^n mod b ≠ 0`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 2
(`integers-2024-A69-thm-2`). -/
public theorem_wanted three_digit_palindrome_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    ((Nat.digits b (2 ^ n)).Palindrome ∧ (Nat.digits b (2 ^ n)).length = 3) ↔
      b ^ 2 + 1 ≤ 2 ^ n ∧ 2 ^ n ≤ b ^ 3 - 1 ∧ 2 ^ n % b ≠ 0 ∧
        ((2 ^ n / b : ℕ) : ℚ) / b - ((b : ℚ) - 1) / b ≤ ((2 ^ n % b : ℕ) : ℚ) ∧
        ((2 ^ n % b : ℕ) : ℚ) ≤ ((2 ^ n / b : ℕ) : ℚ) / b

/-- The only 3-digit binomial form representations of `2^n` are
`2^i (1, 2, 1)_{2^{(n-i)/2} - 1}` with `0 ≤ 3i < n - 2` and `n ≡ i (mod 2)`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 3
(`integers-2024-A69-thm-3`). -/
public theorem_wanted three_digit_binomialForm_two_pow_iff (n b α : ℕ) (hb : 2 ≤ b)
    (hα : 1 ≤ α) :
    Nat.digits b (2 ^ n) = [α, 2 * α, α] ↔
      ∃ i : ℕ, 3 * i + 2 < n ∧ n % 2 = i % 2 ∧ α = 2 ^ i ∧ b = 2 ^ ((n - i) / 2) - 1

/-- There is a representation `2^n = (1, c, 1)_b` that is not of binomial form
(`c ≠ 2`) if and only if (i) `2^n - 1 = kb` with `b ≤ k ≤ 2b - 1`, and (ii) it is
not the case that `n` is even and `b = 2^{n/2} - 1`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 4
(`integers-2024-A69-thm-4`). -/
public theorem_wanted one_c_one_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    (∃ c, c ≠ 2 ∧ Nat.digits b (2 ^ n) = [1, c, 1]) ↔
      (∃ k, 2 ^ n - 1 = k * b ∧ b ≤ k ∧ k ≤ 2 * b - 1) ∧ ¬ (Even n ∧ b = 2 ^ (n / 2) - 1)

/-- Let `b = 2^x - 1` (`x ≥ 2`), `n ≥ 1`, and let `2^n = (c_k, …, c_0)_b` be a
palindromic representation (so `k + 1` digits). Then (1) `n > k(x - 1)`; and (2) if
`r = n - kx ≥ 0` and either `k ≤ x - r`, or `3 ≤ k ≤ x - r + 1` and `x ≥ 3`, then
the representation is the binomial form `2^r (C(k,k), …, C(k,0))_b`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 4
(`integers-2024-A69-lem-4`). -/
public theorem_wanted palindrome_two_pow_base_two_pow_sub_one (x n k : ℕ) (hx : 2 ≤ x)
    (hn : 1 ≤ n) (hp : (Nat.digits (2 ^ x - 1) (2 ^ n)).Palindrome)
    (hk : (Nat.digits (2 ^ x - 1) (2 ^ n)).length = k + 1) :
    k * (x - 1) < n ∧
      ∀ r : ℕ, n = k * x + r →
        ((k : ℤ) ≤ (x : ℤ) - r ∨ (3 ≤ k ∧ (k : ℤ) ≤ (x : ℤ) - r + 1 ∧ 3 ≤ x)) →
        Nat.digits (2 ^ x - 1) (2 ^ n) = (List.range (k + 1)).map fun i => 2 ^ r * k.choose i

/-- For every `n ≥ 2`, `2^n` has a base-`b` binomial form representation for some
`b ≤ 2^y - 1` with `y ≤ ⌈√(2n)⌉ + 1`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 5
(`integers-2024-A69-thm-5`). -/
public theorem_wanted exists_small_base_binomialForm_two_pow (n : ℕ) (hn : 2 ≤ n) :
    ∃ y b : ℕ, y ≤ ⌈Real.sqrt (2 * n)⌉₊ + 1 ∧ 2 ≤ b ∧ b ≤ 2 ^ y - 1 ∧ HasBinomialForm b (2 ^ n)

/-- If `p` is prime and `N = p^n` has a palindromic representation
`(c_k, …, c_0)_b` with `k` odd (an even number of digits), then `b = p^x - 1` for
some `x`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 6
(`integers-2024-A69-thm-6`). -/
public theorem_wanted base_eq_prime_pow_sub_one_of_palindrome (p n b : ℕ) (hp : p.Prime)
    (hb : 2 ≤ b) (hpal : (Nat.digits b (p ^ n)).Palindrome)
    (he : Even (Nat.digits b (p ^ n)).length) : ∃ x, b = p ^ x - 1

/-- For every base `z ≥ 2`: (I) `z^n = (1, 0, …, 0)_z` with `n + 1` digits; (II)
for `n ≥ 1`, `z^n + 1 = (1, 0, …, 0, 1)_z` with `n + 1` digits. Part (III) is
omitted: as printed (`z^n - 1 = (1, 1, …, 1)_z`) it is false for `z ≥ 3`, e.g.
`3^2 - 1 = 8 = (2, 2)_3`.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 7
(`integers-2024-A69-thm-7`), parts (I) and (II). -/
public theorem_wanted digits_pow_and_pow_add_one (z n : ℕ) (hz : 2 ≤ z) :
    Nat.digits z (z ^ n) = List.replicate n 0 ++ [1] ∧
      (1 ≤ n → Nat.digits z (z ^ n + 1) = [1] ++ List.replicate (n - 1) 0 ++ [1])

/-- Bugeaud–Mihăilescu: apart from `11² = (1,1,1,1,1)_3`, `20² = (1,1,1,1)_7` and
`7³ = (1,1,1)_18`, the Nagell–Ljunggren equation `(xⁿ - 1)/(x - 1) = y^q` has no
solution with `x, y ≥ 2`, `n ≥ 3`, `q ≥ 2` if `q = 2`, or `3 ∣ n`, or `4 ∣ n`, or
`q = 3` and `n ≢ 5 (mod 6)`. The ranges `x, y ≥ 2`, `n ≥ 3`, `q ≥ 2` are the
standard ones for this equation (not displayed in the paper).

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 8
(`integers-2024-A69-thm-8`), quoting Bugeaud and Mihăilescu. -/
public theorem_wanted nagell_ljunggren_solutions (x y n q : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hn : 3 ≤ n) (hq : 2 ≤ q) (h : (x ^ n - 1) / (x - 1) = y ^ q)
    (hc : q = 2 ∨ 3 ∣ n ∨ 4 ∣ n ∨ (q = 3 ∧ n % 6 ≠ 5)) :
    (x, y, n, q) = (3, 11, 5, 2) ∨ (x, y, n, q) = (7, 20, 4, 2) ∨ (x, y, n, q) = (18, 7, 3, 3)

end

end MetaMathlibExt
