/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Intersections in pairs of words

Statements from Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*,
INTEGERS 24 (2024), Article A107.

A word of length `n` over the alphabet `[k]` is a map `Fin n → Fin k`; a pair `(u, v)` is
non-intersecting when no letter occurs in both, and the overlap statistic (tracked by `q`) is the
number of positions of `v` whose letter occurs in `u`. Weakly decreasing words are `Antitone`
maps. The paper's generating functions run over pairs of non-empty words (`x^n y^r`, `n, r ≥ 1`).
A two-variable generating function that factors as `A(x) B(y)` is stated coefficientwise:
`[x^n y^r] A(x)B(y) = [x^n]A · [y^r]B`, with `A`, `B` in `ℚ⟦X⟧`; `q` is a rational parameter
(an identity of polynomials in `q` holds iff it holds for every `q : ℚ`); Corollary 4 is stated in
`MvPowerSeries (Fin 2) ℚ` with `x = X 0`, `y = X 1`. `S_{n,j}` is `Nat.stirlingSecond n j`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1: for `n, r ≥ 1`, the number of non-intersecting pairs of words of lengths `n` and `r`
over `[k]` is `[x^n y^r] f_k(x, y)` for both closed forms
`f_k = ∑_{j=1}^{k-1} C(k, j) j! x^j / ∏_{i=1}^{j} (1 - i x) · (k-j)y / (1 - (k-j)y)
= ∑_{n ≥ 1} ∑_{j=1}^{k-1} C(k, j) j! S_{n,j} x^n (k-j)y / (1 - (k-j)y)`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 1 (`integers-2024-A107-thm-1`). -/
public theorem_wanted nonIntersectingWordPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) *
          coeff n ((j.factorial : ℚ⟦X⟧) * X ^ j * (∏ i ∈ Finset.Icc 1 j, (1 - (i : ℚ⟦X⟧) * X))⁻¹) *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹) ∧
      (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
        ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j *
          coeff r (((k - j : ℕ) : ℚ⟦X⟧) * X * (1 - ((k - j : ℕ) : ℚ⟦X⟧) * X)⁻¹)

/-- Corollary 1: the generating function of non-intersecting pairs of words of the same length
`n ≥ 1` over `[k]` is `g_k(x) = ∑_{n ≥ 1} ∑_{j=1}^{k-1} C(k, j) j! S_{n,j} (k-j)^n x^n` (the
`n = 0` coefficient is `0` on both sides: the empty pair is not counted).

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 1 (`integers-2024-A107-cor-1`). -/
public theorem_wanted nonIntersectingWordPairs_sameLength_generatingFunction (k : ℕ) :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else
        (((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ)) =
      PowerSeries.mk fun n => ∑ j ∈ Finset.Icc 1 (k - 1),
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((k - j : ℕ) : ℚ) ^ n

/-- Corollary 2: for `n ≥ 1`, the number of non-intersecting pairs of words of length `n` over
`[k]` is `h_k(n) = ∑_{j=1}^{k-1} C(k, j) j! S_{n,j} (k-j)^n`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 2 (`integers-2024-A107-cor-2`). -/
public theorem_wanted nonIntersectingWordPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n →
        Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * j.factorial * Nat.stirlingSecond n j * (k - j) ^ n

/-- Theorem 2: for `n, r ≥ 1` and every `q`, the sum of `q^{overlap}` over all pairs of words of
lengths `n` and `r` over `[k]` is `[x^n y^r] P(x, y, q; k)` with
`P = ∑_{j=1}^{k} C(k, j) (qj + k - j)y / (1 - (qj + k - j)y) ∑_{n ≥ 1} j! S_{n,j} x^n`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 2 (`integers-2024-A107-thm-2`). -/
public theorem_wanted wordPairs_overlap_sum_eq_coeff (k n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℚ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))),
        q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
      ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) *
        coeff r (PowerSeries.C (q * j + (k - j : ℕ)) * X *
          (1 - PowerSeries.C (q * j + (k - j : ℕ)) * X)⁻¹) *
        (j.factorial * Nat.stirlingSecond n j)

/-- Corollary 3: for `n ≥ 1` and every `q`, the sum of `q^{overlap}` over pairs of words of equal
length `n` over `[k]` (the coefficient of `x^{2n}` in `P(x, q; k)`) is
`∑_{j=1}^{k} C(k, j) j! S_{n,j} (qj + k - j)^n`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 3 (`integers-2024-A107-cor-3`). -/
public theorem_wanted wordPairs_sameLength_overlap_sum (k n : ℕ) (hn : 1 ≤ n) (q : ℚ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))),
        q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
      ∑ j ∈ Finset.Icc 1 k,
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * (q * j + (k - j : ℕ)) ^ n

/-- Theorem 3: for `n, r ≥ 1`, the number of non-intersecting pairs of weakly decreasing words of
lengths `n` and `r` over `[k]` is `[x^n y^r] f_{w,k}(x, y)` with
`f_{w,k} = ∑_{j=1}^{k-1} C(k, j) x^j (1-x)^{-j} ((1-y)^{-(k-j)} - 1)`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 3 (`integers-2024-A107-thm-3`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
      ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
        coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 : ℚ⟦X⟧))

/-- Corollary 4: the generating function of non-intersecting pairs of non-empty weakly decreasing
words over `[k]` (`x`, `y` marking the two lengths) is
`f_{w,k}(x, y) = (x/(1-x) + 1/(1-y))^k - (1/(1-x))^k - (1/(1-y))^k + 1`.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 4 (`integers-2024-A107-cor-4`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_generatingFunction (k n r : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 r)
        ((MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹ + (1 - MvPowerSeries.X 1)⁻¹) ^ k -
          ((1 - MvPowerSeries.X 0)⁻¹) ^ k - ((1 - MvPowerSeries.X 1)⁻¹) ^ k + 1 :
          MvPowerSeries (Fin 2) ℚ) =
      if 1 ≤ n ∧ 1 ≤ r then (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r →
          Fin k))).filter fun p => Antitone p.1 ∧ Antitone p.2 ∧
          Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) else 0

/-- Corollary 5: for `n ≥ 1`, the number of non-intersecting pairs of weakly decreasing words of
length `n` over `[k]` is `∑_{j=1}^{k-1} C(k, j) C(n-1, j-1) C(n+k-j-1, n)` (the `z^n` coefficient
of the paper's generating function).

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 5 (`integers-2024-A107-cor-5`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_sameLength_card (k n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
      ∑ j ∈ Finset.Icc 1 (k - 1), k.choose j * (n - 1).choose (j - 1) * (n + k - j - 1).choose n

/-- Theorem 4, with the sum over `j` running to `k`: for `n, r ≥ 1` and every `q`, the sum of
`q^{overlap}` over pairs of weakly decreasing words of lengths `n` and `r` over `[k]` is
`[x^n y^r] g_{w,k}(x, y, q)` for both forms
`g_{w,k} = ∑_{j=1}^{k} C(k, j) x^j (1-x)^{-j} ((1-y)^{-(k-j)} - 1 + (1-y)^{-(k-j)} ∑_{r ≥ 1} C(r+j-1, r) q^r y^r)
= ∑_{j=1}^{k} C(k, j) x^j (1-x)^{-j} (-1 + (1-y)^{-(k-j)} (1-qy)^{-j})`. The printed upper limit
`k - 1` omits the pairs whose first word uses all `k` letters (`j = k`, which Theorem 2 includes):
for `k = 1`, `n = r = 1` the only pair `(1, 1)` contributes `q`, while the printed sum is empty.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 4 (`integers-2024-A107-thm-4`). -/
public theorem_wanted weaklyDecreasingPairs_overlap_sum_eq_coeff (k n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (q : ℚ) :
    ∑ p ∈ ((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2), q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
        ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
          coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 + ((1 - X) ^ (k - j))⁻¹ *
            PowerSeries.mk fun m => if m = 0 then 0 else ((m + j - 1).choose m : ℚ) *
                q ^ m : ℚ⟦X⟧)) ∧
      ∑ p ∈ ((Finset.univ : Finset ((Fin n → Fin k) × (Fin r →
          Fin k))).filter fun p => Antitone p.1 ∧
          Antitone p.2), q ^ (Finset.univ.filter fun i => p.2 i ∈ Finset.univ.image p.1).card =
        ∑ j ∈ Finset.Icc 1 k, (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
          coeff r ((-1 + ((1 - X) ^ (k - j))⁻¹ * ((1 - PowerSeries.C q * X) ^ j)⁻¹ : ℚ⟦X⟧))

end

end MetaMathlibExt
