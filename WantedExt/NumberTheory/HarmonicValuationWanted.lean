/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.HarmonicValuation

namespace MetaMathlibExt

@[expose] public section

/-- `E_k(n, N)`: the `k`-th elementary symmetric function of
`1/(n - N + 1), 1/(n - N + 2), …, 1/n` (the paper's `E_k(n, am)` with
`N = am`).

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Section 4, equation (4.1). -/
public def harmonicElemSymm (n N k : ℕ) : ℚ :=
  ∑ s ∈ (Finset.Ioc (n - N) n).powersetCard k, ∏ i ∈ s, (1 / i : ℚ)

/-- `E_1(2, 2) = H_2 = 3/2` and `E_2(2, 2) = 1/2`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Section 4 (`E_1(n, am) = H_n - H_{n-am}`). -/
public theorem harmonicElemSymm_two_two :
    harmonicElemSymm 2 2 1 = 3 / 2 ∧ harmonicElemSymm 2 2 2 = 1 / 2 := by
  constructor <;> decide +kernel

/-- For `1 ≤ k ≤ n`: `E_k(n, n) = |s(n + 1, k + 1)| / n!` (unsigned Stirling
numbers of the first kind) and the trivial bound
`ν₂(E_k(n, n)) ≥ -k ⌊log₂ n⌋` (4.2).

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Section 4 preamble to Lemma 2 (the corpus record
labelled Theorem 7). -/
public theorem_wanted harmonicElemSymm_self_eq_and_padicValRat_ge (n k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    harmonicElemSymm n n k = (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) / (n.factorial : ℚ) ∧
      -((k : ℤ) * Nat.log 2 n) ≤ padicValRat 2 (harmonicElemSymm n n k)

/-- **Lemma 2**: for `1 ≤ k ≤ n`,
`ν₂(E_k(n, n)) ≥ ∑_{i=1}^k (-⌊log₂ n⌋ + ⌊log₂ i⌋)
= -k⌊log₂ n⌋ + (k + 1)⌊log₂ k⌋ - 2(2^{⌊log₂ k⌋} - 1)`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Lemma 2. -/
public theorem_wanted padicValRat_two_harmonicElemSymm_self_ge (n k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc 1 k, (-(Nat.log 2 n : ℤ) + Nat.log 2 i) ≤
        padicValRat 2 (harmonicElemSymm n n k) ∧
      ∑ i ∈ Finset.Icc 1 k, (-(Nat.log 2 n : ℤ) + Nat.log 2 i) =
        -(k * Nat.log 2 n : ℤ) + ((k + 1) * Nat.log 2 k - 2 * (2 ^ Nat.log 2 k - 1))

/-- **Corollary 3**: for every `k ≥ 1` there is `n ≥ k` with
`ν₂(E_k(n, n)) = ∑_{i=1}^k (-⌊log₂ n⌋ + ⌊log₂ i⌋)` (equality in Lemma 2).

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 3. -/
public theorem_wanted exists_padicValRat_two_harmonicElemSymm_self_eq (k : ℕ) (hk : 1 ≤ k) :
    ∃ n, k ≤ n ∧ padicValRat 2 (harmonicElemSymm n n k) =
      ∑ i ∈ Finset.Icc 1 k, (-(Nat.log 2 n : ℤ) + Nat.log 2 i)

/-- **Theorem 7**: for positive integers `a ≤ n`, `b`, and `N` with
`ν₂(N) ≥ ⌊log₂ n⌋`,
`ν₂(∑_{m=1}^{⌊n/a⌋} (C(n + N, am) - C(n, am)) 2^{bm}) ≥ ν₂(N) - ⌊log₂ n⌋ + b`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Theorem 7, equation (5.1). -/
public theorem_wanted padicValInt_two_lacunary_binomial_sum_ge (a b n N : ℕ) (ha : 0 < a)
    (hb : 0 < b) (han : a ≤ n) (hN : 0 < N) (hv : Nat.log 2 n ≤ padicValNat 2 N) :
    (padicValNat 2 N : ℤ) - Nat.log 2 n + b ≤
      padicValInt 2 (∑ m ∈ Finset.Icc 1 (n / a),
        (((n + N).choose (a * m) : ℤ) - (n.choose (a * m) : ℤ)) * 2 ^ (b * m))

end

end MetaMathlibExt
