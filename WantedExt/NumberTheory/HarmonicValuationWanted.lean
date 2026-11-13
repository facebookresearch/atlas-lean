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
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- The weighted binary digit sum `a(n) = ∑ aᵢ * 2^{aᵢ}`, summed over the
exponents `aᵢ` of the powers of `2` in the binary expansion of `n` (that is,
over the indices of the `1` bits of `n`).

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic
Numbers*, INTEGERS 24 (2024), Article A27, Corollary 2 and Theorem 4; the
first values `0, 0, 2, 2, 8, 8, 10, 10, 24, ...` are displayed there. -/
public def weightedBinaryDigitSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log 2 n + 1), if Nat.testBit n i then i * 2 ^ i else 0

/-- Characteristic value `a(2) = 2`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24
(2024), Article A27, Theorem 4 (displayed values). -/
public theorem weightedBinaryDigitSum_two : weightedBinaryDigitSum 2 = 2 := by
  decide

/-- Characteristic value `a(4) = 8`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24
(2024), Article A27, Theorem 4 (displayed values). -/
public theorem weightedBinaryDigitSum_four : weightedBinaryDigitSum 4 = 8 := by
  decide

/-- Kürschák's strengthening of Theisinger's theorem:

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Theorem 2 (`integers-2024-A27-thm-2`). for `0 ≤ m ≤ n - 2` the difference `H_n - H_m`
does not lie
in the ring of `2`-adic integers.

For a rational number this is the statement that its `2`-adic valuation
`padicValRat 2` is negative; in particular `H_n - H_m ∉ ℤ`. -/
public theorem_wanted padicValRat_two_harmonic_sub_neg (m n : ℕ)
    (h : m + 2 ≤ n) :
    padicValRat 2 (harmonic n - harmonic m) < 0

/-- Fiber counts of the values `ν₂(H_n - H_m)`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Theorem 3 (`integers-2024-A27-thm-3`):
writing `n = ∑_{i=1}^{t} 2^{aᵢ}` in binary, among the values
`ν₂(H_n - H_m)` for `m = 0, 1, …, n - 1` exactly `2^{aᵢ}` are equal to
`-aᵢ`, for each exponent `aᵢ` occurring in the expansion.

The extracted statement truncates the refinement locating these values in
the intervals determined by the partial sums `Mⱼ`; only the fiber counts
stated in the first part are formalized here. Verified computationally with
exact rational arithmetic for `n < 40`. -/
public theorem_wanted card_filter_padicValRat_two_harmonic_sub (n a : ℕ)
    (ha : Nat.testBit n a = true) :
    ((Finset.range n).filter
      (fun m => padicValRat 2 (harmonic n - harmonic m) = -(a : ℤ))).card
      = 2 ^ a

/-- Valuation of the difference `H_{2n} - H_n`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Lemma 1 (`integers-2024-A27-lem-1`): for `n ≥ 1`,
`ν₂(H_{2n} - H_n) = -⌊log₂(2n)⌋`. -/
public theorem_wanted padicValRat_two_harmonic_two_mul_sub (n : ℕ)
    (hn : 1 ≤ n) :
    padicValRat 2 (harmonic (2 * n) - harmonic n) = -(Nat.log 2 (2 * n) : ℤ)

/-- Valuation at powers of two.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Corollary 1 (`integers-2024-A27-cor-1`): if `n = 2^a` is a
power of `2` then `ν₂(H_n - H_{n-m}) = -a` for every `1 ≤ m ≤ n`. -/
public theorem_wanted padicValRat_two_harmonic_pow_sub (a m : ℕ)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ a) :
    padicValRat 2 (harmonic (2 ^ a) - harmonic (2 ^ a - m)) = -(a : ℤ)

/-- Sum of valuations over all `m < n`.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Corollary 2 (`integers-2024-A27-cor-2`):
`∑_{m=0}^{n-1} ν₂(H_n - H_m) = -a(n)`, where `a(n) = weightedBinaryDigitSum n`.

The extracted statement flattens the displayed aggregation over `m`; the sum
reading used here (rather than a product of valuations) was verified
computationally with exact rational arithmetic for `n ≤ 16`. -/
public theorem_wanted sum_padicValRat_two_harmonic_sub (n : ℕ) :
    ∑ m ∈ Finset.range n, padicValRat 2 (harmonic n - harmonic m)
      = -(weightedBinaryDigitSum n : ℤ)

/-- Recurrence for the weighted binary digit sum.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Theorem 4 (`integers-2024-A27-thm-4`): the
weighted binary digit sum satisfies `a(2n) = 2a(n) + 2n` and
`a(2n + 1) = a(2n)`, with `a(0) = a(1) = 0`.

The two-variable generating-function claim in the same theorem is garbled in
the extraction and is not formalized. -/
public theorem_wanted weightedBinaryDigitSum_recurrence (n : ℕ) :
    weightedBinaryDigitSum (2 * n) = 2 * weightedBinaryDigitSum n + 2 * n ∧
    weightedBinaryDigitSum (2 * n + 1) = weightedBinaryDigitSum (2 * n)

/-- Valuation for shifts by powers of two.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Theorem 5 (`integers-2024-A27-thm-5`): for `m = 2^r` with
`1 ≤ m ≤ n`, `ν₂(H_n - H_{n-m}) = -r - ν₂(⌊n / m⌋)`. -/
public theorem_wanted padicValRat_two_harmonic_sub_pow (r n : ℕ)
    (h : 2 ^ r ≤ n) :
    padicValRat 2 (harmonic n - harmonic (n - 2 ^ r))
      = -(r : ℤ) - ((n / 2 ^ r).factorization 2 : ℤ)

/-- Piecewise valuation formula.

Source: Lengyel, *On the 2-Adic Valuation of Differences of Harmonic Numbers*, INTEGERS 24 (2024),
Article A27, Theorem 6, formula (3.1) (`integers-2024-A27-thm-6`): let
`M = ⌈log₂(m + 1)⌉` and `j = ⌊(n - m) / 2^M⌋`, where `1 ≤ m ≤ n`. Then
`ν₂(H_n - H_{n-m}) = -M + 1` when `2^M * j + m ≤ n ≤ 2^M * (j + 1) - 1`, and
`ν₂(H_n - H_{n-m}) = -M - ν₂(j + 1)` when
`2^M * (j + 1) ≤ n ≤ 2^M * (j + 1) + m - 1`.

The accompanying lower bound (3.2) is garbled in the extraction and is not
formalized. Both branches were verified computationally with exact rational
arithmetic for `m < 20`, `n < 45`. -/
public theorem_wanted padicValRat_two_harmonic_sub_piecewise (m n : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1))) + m ≤ n ∧
        n + 1 ≤ 2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ) + 1) ∧
    (2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) ≤ n ∧
        n + 1 ≤ 2 ^ (Nat.clog 2 (m + 1)) * ((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1) + m →
      padicValRat 2 (harmonic n - harmonic (n - m))
        = -(Nat.clog 2 (m + 1) : ℤ)
          - (((n - m) / 2 ^ (Nat.clog 2 (m + 1)) + 1).factorization 2 : ℤ))

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
