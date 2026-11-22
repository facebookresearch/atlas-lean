/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

/-!
# Congruences for `ℓ`-regular tripartitions, `ℓ ∈ {2, 3}` — wishlist

Statements from Mohammed L. Nadji and Moussa Ahmia, *Congruences for `l`-Regular
Tripartitions for `l` in `{2,3}`*, INTEGERS 24 (2024), Article A86.

`T_ℓ(n)` counts triples of `ℓ`-regular partitions (no part divisible by `ℓ`) of total
size `n`, i.e. `∑ T_ℓ(n) qⁿ = f_ℓ³ / f_1³` (paper, Section 1, eq. (1)), where
`f_k = (q^k; q^k)_∞` is `qEulerProduct k`, written `𝔣 k` below. Eta-quotient identities are
stated with denominators cleared (every `f_k` with `k ≥ 1` has constant coefficient `1`, so
it is a unit of `ℤ⟦X⟧`). The Cui–Gu `p`-dissections (Lemmas 4 and 5) involve Ramanujan's
`f(a, b)` with negated arguments and are stated for complex `q` with `‖q‖ < 1`, through
`ramanujanThetaRaw` and `qPochhammerInfRaw`.

Already stated elsewhere in this library: Lemma 2, eq. (4), is
`qPochhammer_three_dissection_product_one_two`; Lemma 3, eq. (5), is
`f1_cube_three_dissection`; Lemma 6, eq. (9), is the case `k = 1` of
`qEulerProduct_pow_prime_pow_congruence`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- The number `T_ℓ(n)` of `ℓ`-regular tripartitions of `n`: triples `(λ₁, λ₂, λ₃)` of
partitions with `|λ₁| + |λ₂| + |λ₃| = n` in which no part of any `λᵢ` is divisible by `ℓ`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Section 1, definition of `T_ℓ(n)` (with
generating function `f_ℓ³ / f_1³`, Section 1, eq. (1)). -/
public def regularTripartitionCount (l n : ℕ) : ℕ :=
  ∑ x ∈ Finset.antidiagonal n, ∑ y ∈ Finset.antidiagonal x.2,
    (Nat.Partition.restricted x.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.2 (¬ l ∣ ·)).card

private theorem card_restricted_zero (p : ℕ → Prop) [DecidablePred p] :
    (Nat.Partition.restricted 0 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default]

private theorem card_restricted_one (p : ℕ → Prop) [DecidablePred p] (h : p 1) :
    (Nat.Partition.restricted 1 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default, h]

/-- `T_ℓ(0) = 1`: the only tripartition of `0` is the triple of empty partitions.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_zero (l : ℕ) : regularTripartitionCount l 0 = 1 := by
  simp [regularTripartitionCount, card_restricted_zero]

/-- `T_ℓ(1) = 3` for `ℓ ≠ 1`: the single part `1` sits in one of the three components.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_one (l : ℕ) (hl : l ≠ 1) :
    regularTripartitionCount l 1 = 3 := by
  have h1 : ¬ l ∣ 1 := by simpa using hl
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, card_restricted_zero,
    card_restricted_one (fun x => ¬ l ∣ x) h1]

/-- `T_2(3n + 1) ≡ 0 (mod 3)` and `T_2(3n + 2) ≡ 0 (mod 6)` for all `n ≥ 0`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 1. -/
public theorem_wanted regularTripartitionCount_two_mod_three_six (n : ℕ) :
    3 ∣ regularTripartitionCount 2 (3 * n + 1) ∧ 6 ∣ regularTripartitionCount 2 (3 * n + 2)

/-- `T_3(3n + 1) ≡ 0 (mod 3)` and `T_3(3n + 2) ≡ 0 (mod 9)` for all `n ≥ 0`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 2 (congruences (53), (54)). -/
public theorem_wanted regularTripartitionCount_three_mod_three_nine (n : ℕ) :
    3 ∣ regularTripartitionCount 3 (3 * n + 1) ∧ 9 ∣ regularTripartitionCount 3 (3 * n + 2)

/-- `T_3(6n + 4) ≡ 0 (mod 6)` for all `n ≥ 0`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 3 (congruence (64)). -/
public theorem_wanted regularTripartitionCount_three_six_mul_add_four (n : ℕ) :
    6 ∣ regularTripartitionCount 3 (6 * n + 4)

/-- For a prime `p ≥ 5`, `α, n ≥ 0` and `1 ≤ i ≤ p - 1`,
`T_2(3 p^{2α+1} (p n + i) + (p^{2α+2} - 1)/8) ≡ 0 (mod 2)` (the division is exact).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 1 (congruence (13)). -/
public theorem_wanted regularTripartitionCount_two_prime_ge_five_even
    (p α n i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hi : 1 ≤ i) (hip : i < p) :
    2 ∣ regularTripartitionCount 2
      (3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 8)

/-- For an odd prime `p`, `α, n ≥ 0` and `1 ≤ i ≤ p - 1`,
`T_2(9 p^{2α+1} (p n + i) + (9 p^{2α+2} - 1)/8) ≡ 0 (mod 2)` (the division is exact).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 2 (congruence (21)). -/
public theorem_wanted regularTripartitionCount_two_odd_prime_even
    (p α n i : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hi : 1 ≤ i) (hip : i < p) :
    2 ∣ regularTripartitionCount 2
      (9 * p ^ (2 * α + 1) * (p * n + i) + (9 * p ^ (2 * α + 2) - 1) / 8)

/-- For a prime `p ≡ 3 (mod 4)`, `α, n ≥ 0` and `1 ≤ i ≤ p - 1`,
`T_3(3 p^{2α+1} (p n + i) + (p^{2α+2} - 1)/4) ≡ 0 (mod 3)` (the division is exact).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 5 (congruence (55)). -/
public theorem_wanted regularTripartitionCount_three_prime_three_mod_four
    (p α n i : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hi : 1 ≤ i) (hip : i < p) :
    3 ∣ regularTripartitionCount 3
      (3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 4)

local notation "𝔣" => qEulerProduct

/-- Toh's 3-dissection
`f_2³ / f_1³ = f_6 / f_3 + 3q f_6⁴ f_9⁵ / (f_3⁸ f_18) + 6q² f_6³ f_9² f_18² / f_3⁷
+ 12q³ f_6² f_18⁵ / (f_3⁶ f_9)`, stated with denominators cleared (both sides multiplied by
`f_1³ f_3⁸ f_9 f_18`).

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 1, eq. (3) (`integers-2024-A86-lem-1`). -/
public theorem_wanted f2_cube_div_f1_cube_three_dissection :
    𝔣 2 ^ 3 * 𝔣 3 ^ 8 * 𝔣 9 * 𝔣 18 =
      𝔣 1 ^ 3 * (𝔣 3 ^ 7 * 𝔣 6 * 𝔣 9 * 𝔣 18 + 3 * X * 𝔣 6 ^ 4 * 𝔣 9 ^ 6 +
        6 * X ^ 2 * 𝔣 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 3 * 𝔣 18 ^ 3 +
        12 * X ^ 3 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2 * 𝔣 18 ^ 6)

/-- The 3-dissection of `1 / f_1³`:
`1 / f_1³ = (f_9³ / f_3¹²) (f_1⁶ + 9q f_1³ f_9³ + 27q² f_9⁶)` and
`1 / f_1³ = f_6² f_9¹⁵ / (f_3¹⁴ f_18⁶) + 3q f_6 f_9¹² / (f_3¹³ f_18³) + 9q² f_9⁹ / f_3¹²
+ 8q³ f_9⁶ f_18³ / (f_3¹¹ f_6) + 12q⁴ f_9³ f_18⁶ / (f_3¹⁰ f_6²)
+ 16q⁶ f_18¹² / (f_3⁸ f_6⁴ f_9³)`, both stated with denominators cleared (multiplied by
`f_1³ f_3¹²`, resp. `f_1³ f_3¹⁴ f_6⁴ f_9³ f_18⁶`). The lemma's first identity (5) is
`f1_cube_three_dissection`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 3, eq. (6) (`integers-2024-A86-lem-3`). -/
public theorem_wanted one_div_f1_cube_three_dissection :
    𝔣 3 ^ 12 = 𝔣 1 ^ 3 * 𝔣 9 ^ 3 *
        (𝔣 1 ^ 6 + 9 * X * 𝔣 1 ^ 3 * 𝔣 9 ^ 3 + 27 * X ^ 2 * 𝔣 9 ^ 6) ∧
      𝔣 3 ^ 14 * 𝔣 6 ^ 4 * 𝔣 9 ^ 3 * 𝔣 18 ^ 6 =
        𝔣 1 ^ 3 * (𝔣 6 ^ 6 * 𝔣 9 ^ 18 + 3 * X * 𝔣 3 * 𝔣 6 ^ 5 * 𝔣 9 ^ 15 * 𝔣 18 ^ 3 +
          9 * X ^ 2 * 𝔣 3 ^ 2 * 𝔣 6 ^ 4 * 𝔣 9 ^ 12 * 𝔣 18 ^ 6 +
          8 * X ^ 3 * 𝔣 3 ^ 3 * 𝔣 6 ^ 3 * 𝔣 9 ^ 9 * 𝔣 18 ^ 9 +
          12 * X ^ 4 * 𝔣 3 ^ 4 * 𝔣 6 ^ 2 * 𝔣 9 ^ 6 * 𝔣 18 ^ 12 +
          16 * X ^ 6 * 𝔣 3 ^ 6 * 𝔣 18 ^ 18)

/-- Cui and Gu's `p`-dissection of `ψ(q) = f(q, q³)` for an odd prime `p`:
`ψ(q) = ∑_{k=0}^{(p-3)/2} q^{k(k+1)/2} f(q^{(p²+(2k+1)p)/2}, q^{(p²-(2k+1)p)/2})
+ q^{(p²-1)/8} ψ(q^{p²})`, for complex `q` with `‖q‖ < 1`; and
`(m² + m)/2 ≢ (p² - 1)/8 (mod p)` for `0 ≤ m ≤ (p - 3)/2`. Ramanujan's `f(a, b)` is
`ramanujanThetaRaw a b` (summable here since `‖q‖ < 1` and both exponents are positive);
`ψ(q^{p²})` is written `f(q^{p²}, q^{3p²})`. All divisions are exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 4, eq. (7) (`integers-2024-A86-lem-4`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.1. -/
public theorem_wanted ramanujanPsi_prime_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
        ∑ k ∈ Finset.range ((p - 1) / 2), q ^ (k * (k + 1) / 2) *
            ramanujanThetaRaw (q ^ ((p ^ 2 + (2 * k + 1) * p) / 2))
              (q ^ ((p ^ 2 - (2 * k + 1) * p) / 2)) +
          q ^ ((p ^ 2 - 1) / 8) * ramanujanThetaRaw (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) ∧
      ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p]

/-- Cui and Gu's `p`-dissection of `f_1 = (q; q)_∞` for a prime `p ≥ 5`: with
`s = (±p - 1)/6`, i.e. `s = (p - 1)/6` if `p ≡ 1 (mod 6)` and `s = (-p - 1)/6` if
`p ≡ -1 (mod 6)`,
`f_1 = ∑_{k = (1-p)/2, k ≠ s}^{(p-1)/2} (-1)^k q^{k(3k+1)/2}
f(-q^{(3p²+(6k+1)p)/2}, -q^{(3p²-(6k+1)p)/2}) + (-1)^s q^{(p²-1)/24} f_{p²}`,
for complex `q` with `‖q‖ < 1`. Ramanujan's `f(a, b)` is `ramanujanThetaRaw a b`, and
`f_k = (q^k; q^k)_∞` is `qPochhammerInfRaw (q ^ k) (q ^ k)`. The exponents `k(3k+1)/2` and
`(3p² ± (6k+1)p)/2` are nonnegative integers, passed to `ℕ` powers with `Int.toNat`. All
divisions are exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 5, eq. (8) (`integers-2024-A86-lem-5`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.2. The same identity is Nayaka, Dharmendra and Mahesh Kumar,
*Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80,
Lemma 4, eq. (43) (`integers-2024-A80-lem-4`). -/
public theorem_wanted qPochhammer_prime_dissection (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInfRaw q q =
      ∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
          (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat *
            ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
              (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) +
        (-1 : ℂ) ^ s * q ^ ((p ^ 2 - 1) / 24) *
          QPochhammer.qPochhammerInfRaw (q ^ (p ^ 2)) (q ^ (p ^ 2))

/-- The 3-dissection of the generating function of `T_2`:
`∑ T_2(3n) qⁿ = f_2 / f_1 + 12q f_2² f_6⁵ / (f_1⁶ f_3)`,
`∑ T_2(3n + 1) qⁿ = 3 f_2⁴ f_3⁵ / (f_1⁸ f_6)` and
`∑ T_2(3n + 2) qⁿ = 6 f_2³ f_3² f_6² / f_1⁷`, each stated with its denominator cleared.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 7, eqs. (10)–(12)
(`integers-2024-A86-lem-7`). -/
public theorem_wanted regularTripartitionCount_two_three_dissection :
    𝔣 1 ^ 6 * 𝔣 3 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n) : ℤ)) =
        𝔣 1 ^ 5 * 𝔣 2 * 𝔣 3 + 12 * X * 𝔣 2 ^ 2 * 𝔣 6 ^ 5 ∧
      𝔣 1 ^ 8 * 𝔣 6 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n + 1) : ℤ)) =
        3 * 𝔣 2 ^ 4 * 𝔣 3 ^ 5 ∧
      𝔣 1 ^ 7 * PowerSeries.mk (fun n => (regularTripartitionCount 2 (3 * n + 2) : ℤ)) =
        6 * 𝔣 2 ^ 3 * 𝔣 3 ^ 2 * 𝔣 6 ^ 2

/-- For all `α, n ≥ 0`, with `A_α = ∑_{i=0}^{2α+1} 3^{2i}` and `B_α = ∑_{i=0}^{2α} 3^{2i}`:
`T_2(3^{4α+4} n + A_α + 3^{4α+3}) ≡ T_2(3^{4α+4} n + A_α + 2·3^{4α+3}) ≡ 0 (mod 12)` and
`T_2(3^{4α+2} n + B_α + 3^{4α+1}) ≡ T_2(3^{4α+2} n + B_α + 2·3^{4α+1}) ≡ 0 (mod 12)`.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 3, eqs. (31)–(34)
(`integers-2024-A86-thm-3`). -/
public theorem_wanted regularTripartitionCount_two_mod_twelve (α n : ℕ) :
    12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 4) * n + ∑ i ∈ Finset.range (2 * α + 2), 3 ^ (2 * i) +
          3 ^ (4 * α + 3)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 4) * n + ∑ i ∈ Finset.range (2 * α + 2), 3 ^ (2 * i) +
          2 * 3 ^ (4 * α + 3)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 2) * n + ∑ i ∈ Finset.range (2 * α + 1), 3 ^ (2 * i) +
          3 ^ (4 * α + 1)) ∧
      12 ∣ regularTripartitionCount 2
        (3 ^ (4 * α + 2) * n + ∑ i ∈ Finset.range (2 * α + 1), 3 ^ (2 * i) +
          2 * 3 ^ (4 * α + 1))

/-- The 3-dissection of the generating function of `T_3`:
`∑ T_3(3n) qⁿ = f_2² f_3¹⁵ / (f_1¹¹ f_6⁶) + 8q f_3⁶ f_6³ / (f_1⁸ f_2)
+ 16q² f_6¹² / (f_1⁵ f_2⁴ f_3³)`,
`∑ T_3(3n + 1) qⁿ = 3 f_2 f_3¹² / (f_1¹⁰ f_6³) + 12q f_3³ f_6⁶ / (f_1⁷ f_2²)` and
`∑ T_3(3n + 2) qⁿ = 9 f_3⁹ / f_1⁹`, each stated with its denominators cleared.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 4, eqs. (49)–(51)
(`integers-2024-A86-thm-4`). -/
public theorem_wanted regularTripartitionCount_three_three_dissection :
    𝔣 1 ^ 11 * 𝔣 2 ^ 4 * 𝔣 3 ^ 3 * 𝔣 6 ^ 6 *
          PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n) : ℤ)) =
        𝔣 2 ^ 6 * 𝔣 3 ^ 18 + 8 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 3 * 𝔣 3 ^ 9 * 𝔣 6 ^ 9 +
          16 * X ^ 2 * 𝔣 1 ^ 6 * 𝔣 6 ^ 18 ∧
      𝔣 1 ^ 10 * 𝔣 2 ^ 2 * 𝔣 6 ^ 3 *
          PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n + 1) : ℤ)) =
        3 * 𝔣 2 ^ 3 * 𝔣 3 ^ 12 + 12 * X * 𝔣 1 ^ 3 * 𝔣 3 ^ 3 * 𝔣 6 ^ 9 ∧
      𝔣 1 ^ 9 * PowerSeries.mk (fun n => (regularTripartitionCount 3 (3 * n + 2) : ℤ)) =
        9 * 𝔣 3 ^ 9

end

end MetaMathlibExt
