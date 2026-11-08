/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PadovanSequence

/-!
# Sums of products of binomial coefficients mod 2 as run length transforms

Statements from Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2
and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73 (arXiv:2309.04012).

The paper studies `T(n) = ∑_{k=0}^{n} [binom(a₁n + a₂k, a₃n + a₄k) binom(n, k) mod 2]`. Each summand
is written `(binom(·, ·) * binom(n, k)) % 2` in `ℕ`. The run length transform of `S` sends `n` to
the product of `S(ℓ)` over the lengths `ℓ` of the maximal runs of `1`s in the binary expansion of
`n` (the paper's example `T(11) = S(1) S(2)`; its display writes a sum by mistake).
-/

namespace MetaMathlibExt

@[expose] public section

open Matrix

/-- The lengths of the maximal runs of `1`s in a list of binary digits, where `c` is the length of
the run of `1`s read just before the list (a digit other than `1` ends a run).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def bitRunLengths : List ℕ → ℕ → List ℕ
  | [], c => if c = 0 then [] else [c]
  | b :: bs, c =>
    if b = 1 then bitRunLengths bs (c + 1)
    else if c = 0 then bitRunLengths bs 0 else c :: bitRunLengths bs 0

/-- The lengths of the maximal runs of `1`s in the binary expansion of `n`, read from the least
significant bit (the paper's list `𝓛(n)`, whose order does not matter).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def binaryRunLengths (n : ℕ) : List ℕ :=
  bitRunLengths (Nat.digits 2 n) 0

/-- The run length transform of `S`: `T(n) = ∏_{ℓ ∈ 𝓛(n)} S(ℓ)`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public def runLengthTransform (S : ℕ → ℤ) (n : ℕ) : ℤ :=
  ((binaryRunLengths n).map S).prod

/-- `0` has no runs of `1`s, so every run length transform takes the value `1` at `0`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Definition 1. -/
public theorem runLengthTransform_zero (S : ℕ → ℤ) : runLengthTransform S 0 = 1 := by
  simp [runLengthTransform, binaryRunLengths, bitRunLengths]

/-- The paper's example: `[11]₂ = 1011`, so `T(11) = S(1) S(2)`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, example after Definition 1. -/
public theorem runLengthTransform_eleven (S : ℕ → ℤ) : runLengthTransform S 11 = S 1 * S 2 := by
  have hd : Nat.digits 2 11 = [1, 1, 0, 1] := by norm_num
  have h : binaryRunLengths 11 = [2, 1] := by
    rw [binaryRunLengths, hd]
    decide
  rw [runLengthTransform, h]
  simp [mul_comm]

/-- **Lemma 1.** Let `S(n + 1) = d₀ S(n) + ⋯ + d_r S(n - r)` for `n ≥ r` with `S(0) = 1` (the
initial values `c_i = S(i)` are free). With `v = (1, 0, …, 0)`, `w = (S(0), …, S(r))ᵀ`, and the
companion matrix `γ(1)` (ones on the superdiagonal, last row `d_r, …, d₀`), `S(n) = v γ(1)ⁿ w`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 1. -/
public theorem_wanted linearRecurrence_eq_companion_pow (r : ℕ) (d : Fin (r + 1) → ℤ)
    (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    S n = Pi.single 0 1 ⬝ᵥ
      ((Matrix.of fun i j : Fin (r + 1) =>
          if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)) ^ n *ᵥ
        fun i => S i)

/-- **Theorem 1.** For `S` as in Lemma 1, the run length transform `T` of `S` is `2`-regular with
the linear representation `(v, γ(0), γ(1), w)`: `T(n) = v γ([n]₂) w`, where `γ(0)` has first
column `(S(0), …, S(r))ᵀ` and zeros elsewhere, `γ(1)` is the companion matrix of Lemma 1, and
`γ([n]₂)` multiplies `γ(b)` over the binary digits `b` of `n` from the most significant one.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 1. -/
public theorem_wanted runLengthTransform_linearRecurrence_eq_linearRep (r : ℕ)
    (d : Fin (r + 1) → ℤ) (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    runLengthTransform S n = Pi.single 0 1 ⬝ᵥ
      ((((Nat.digits 2 n).reverse.map fun b =>
          if b = 0 then Matrix.of fun i j : Fin (r + 1) => if j = 0 then S i else 0
          else Matrix.of fun i j : Fin (r + 1) =>
            if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)).prod) *ᵥ
        fun i => S i)

/-- **Theorem 2.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n - k, 2k)` binom(n, k) mod 2]` is the run length transform
of the Fibonacci sequence `1, 1, 2, 3, 5, 8, …` (`Nat.fib (i + 1)`).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 2. -/
public theorem_wanted runLengthTransform_choose_sub_two_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 1) : ℤ)) n

/-- **Theorem 3.** The sum `T(n) = ∑_{k=0}^{n} [`binom(3k, k)` binom(n, k) mod 2]` is the run length transform
of the truncated Fibonacci sequence `1, 2, 3, 5, 8, …` (`Nat.fib (i + 2)`).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 3. -/
public theorem_wanted runLengthTransform_choose_three_mul_fib (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((3 * k).choose k * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (Nat.fib (i + 2) : ℤ)) n

/-- **Theorem 4.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n, 2k)` binom(n, k) mod 2]` is the run length transform
of `1, 1, 2, 4, 8, …`, i.e. `1` followed by the positive powers of `2`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 4. -/
public theorem_wanted runLengthTransform_choose_two_mul_pow_two (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), (n.choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i = 0 then 1 else 2 ^ (i - 1)) n

/-- **Theorem 5.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 2k, 2k)` binom(n, k) mod 2]` is the run length transform
of `1, 2, 2, 2, …`, the sequence of `2`s prepended with a `1`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 5. -/
public theorem_wanted runLengthTransform_choose_add_two_mul_one_two (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 2 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i = 0 then 1 else 2) n

/-- **Theorem 6.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + k, n - k)` binom(n, k) mod 2]` is the run length transform
of the positive integers `1, 2, 3, …`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 6. -/
public theorem_wanted runLengthTransform_choose_add_sub_succ (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i + 1 : ℤ)) n

/-- **Theorem 7.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n - k, 6k)` binom(n, k) mod 2]` is the run length transform
of Narayana's cows sequence `1, 1, 1, 2, 3, 4, 6, 9, …` (`narayanaCowsSequence (i + 1)`).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 7. -/
public theorem_wanted runLengthTransform_choose_sub_six_mul_narayanaCows (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n - k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (narayanaCowsSequence (i + 1) : ℤ)) n

/-- **Theorem 8.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 3k, 6k)` binom(n, k) mod 2]` is the run length transform
of the doubled positive integers `1, 1, 2, 2, 3, 3, …`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 8. -/
public theorem_wanted runLengthTransform_choose_add_three_mul_six_mul_doubled (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 3 * k).choose (6 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i / 2 + 1 : ℤ)) n

/-- **Theorem 9.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 2k, 2n - k)` binom(n, k) mod 2]` is the run length transform
of the Lucas numbers prepended with `1, 1`, i.e. `1, 1, 2, 1, 3, 4, 7, 11, …`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 9. -/
public theorem_wanted runLengthTransform_choose_add_two_mul_two_mul_sub_lucas (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 2 * k).choose (2 * n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i < 2 then 1 else (lucasNumber (i - 2) : ℤ)) n

/-- **Theorem 12.** The sum `T(n) = ∑_{k=0}^{n} [`binom(-n + 7k, n + k)` binom(n, k) mod 2]` is the run length transform
of the Padovan numbers (OEIS A000931) from offset `5`, i.e. `1, 1, 1, 2, 2, 3, 4, 5, …` (`shiftedPadovanSequence (i + 2)`). The top entry is negative for small `k`; there the paper's convention `binom(a, b) = 0` for `a < b` agrees with truncated subtraction, since the bottom entry `n + k` is positive whenever the top entry is truncated.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 12. -/
public theorem_wanted runLengthTransform_choose_seven_mul_sub_padovan_five (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((7 * k - n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence (i + 2) : ℤ)) n

/-- **Theorem 13.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 7k, 3n + k)` binom(n, k) mod 2]` is the run length transform
of the Padovan numbers (OEIS A000931) from offset `3`, i.e. `1, 0, 1, 1, 1, 2, 2, 3, …` (`shiftedPadovanSequence i`).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 13. -/
public theorem_wanted runLengthTransform_choose_add_seven_mul_padovan_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 7 * k).choose (3 * n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (shiftedPadovanSequence i : ℤ)) n

/-- **Theorem 14.** The sum `T(n) = ∑_{k=0}^{n} [`binom(6k, n + 3k)` binom(n, k) mod 2]` is the run length transform
of the sequence alternating between `1` and the positive integers, `1, 1, 1, 2, 1, 3, 1, 4, …`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 14. -/
public theorem_wanted runLengthTransform_choose_six_mul_alternating (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((6 * k).choose (n + 3 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if Even i then 1 else (i / 2 + 1 : ℤ)) n

/-- **Theorem 15.** The sum `T(n) = ∑_{k=0}^{n} [`binom(-2n + 8k, n + k)` binom(n, k) mod 2]` is the run length transform
of the periodic sequence `1, 1, 0, 1, 1, 0, …`. The top entry is negative for small `k`; there the paper's convention `binom(a, b) = 0` for `a < b` agrees with truncated subtraction, since the bottom entry `n + k` is positive whenever the top entry is truncated.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 15. -/
public theorem_wanted runLengthTransform_choose_eight_mul_sub_period_three (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((8 * k - 2 * n).choose (n + k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => if i % 3 = 2 then 0 else 1) n

/-- **Theorem 10.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 5k, 2n + 2k)` binom(n, k) mod 2]` is the run length transform
of the sequence `S(n) = S(n - 1) + S(n - 2) - S(n - 3) + S(n - 4)` for `n ≥ 4` with `S(0) = S(1) = S(2) = S(3) = 1`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 10. -/
public theorem_wanted runLengthTransform_choose_add_five_mul_two_mul_add_two_mul (S : ℕ → ℤ)
    (h0 : S 0 = 1) (h1 : S 1 = 1) (h2 : S 2 = 1)
    (h3 : S 3 = 1) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * n + 2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n

/-- **Theorem 11.** The sum `T(n) = ∑_{k=0}^{n} [`binom(n + 5k, 2k)` binom(n, k) mod 2]` is the run length transform
of the sequence `S(n) = S(n - 1) + S(n - 2) - S(n - 3) + S(n - 4)` for `n ≥ 4` with `S(0) = 1`, `S(1) = S(2) = 2`, `S(3) = 3`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 11. -/
public theorem_wanted runLengthTransform_choose_add_five_mul_two_mul (S : ℕ → ℤ) (h0 : S 0 = 1)
    (h1 : S 1 = 2) (h2 : S 2 = 2)
    (h3 : S 3 = 3) (hrec : ∀ m, 4 ≤ m → S m = S (m - 1) + S (m - 2) - S (m - 3) + S (m - 4))
        (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + 5 * k).choose (2 * k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform S n

/-- **Lemma 2.** For `T_m(n) = ∑_{k=0}^{n} [binom(2^m k, n + k) binom(n, k) mod 2]` and
`n = 2^ℓ - 1`, `T_m(n) = 1` if `ℓ ≡ 0 (mod m)` and `0` otherwise. The paper takes `m ≥ 2`; the
statement holds for every `m` (with `ℓ ≡ 0 (mod 0)` meaning `ℓ = 0`).

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 2. -/
public theorem_wanted sum_choose_two_pow_mul_mod_two_two_pow_sub_one (m ℓ : ℕ) :
    ∑ k ∈ Finset.range (2 ^ ℓ - 1 + 1), ((2 ^ m * k).choose (2 ^ ℓ - 1 + k) * (2 ^ ℓ -
        1).choose k) % 2 =
      if m ∣ ℓ then 1 else 0

/-- **Theorem 16.** For `T_m(n) = ∑_{k=0}^{n} [binom(2^m k, n + k) binom(n, k) mod 2]`,
`T_m(n) = 1` if every maximal run of `1`s in `[n]₂` has length divisible by `m`, and `0`
otherwise. The paper takes `m ≥ 2`; the statement holds for every `m`.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 16. -/
public theorem_wanted sum_choose_two_pow_mul_mod_two_eq (m n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((2 ^ m * k).choose (n + k) * n.choose k) % 2 =
      if ∀ ℓ ∈ binaryRunLengths n, m ∣ ℓ then 1 else 0

end

end MetaMathlibExt
