/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Regular partition functions and a generalized tau function

Statements from S. Sriram and A. David Christopher, *Congruences Relating Regular Partition
Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*,
INTEGERS 24 (2024), Article A39 (arXiv:2509.26559).

`generalizedTau k n` is the paper's `τ_k(n)`: `q ∏ (1 - q^m)^k = ∑ τ_k(n) q^n` (Definition 1.1),
built from Mathlib's `PowerSeries.pentagonalSeries ℤ = ∏ (1 - X^m)`, a unit of `ℤ⟦X⟧`, so that
negative `k` make sense. Ramanujan's `τ` is `generalizedTau 24`. The `t`-regular partition count
`R_t(n)` is `#(Nat.Partition.restricted n (¬ t ∣ ·))`, `p(n)` is `Fintype.card (Nat.Partition n)`,
and the generalized pentagonal numbers `(3r² ± r)/2` are Mathlib's `pentagonal r`, `r ∈ ℤ`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- Euler's product `∏ (1 - X^m)` has constant coefficient `1`.

Source: Euler's pentagonal number theorem as used in Sriram and Christopher, *Congruences
Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function
Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, identity (1). -/
public theorem constantCoeff_pentagonalSeries_int :
    constantCoeff (pentagonalSeries ℤ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  have h := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  have h0 : pentagonal 0 = 0 := by simp [pentagonal_def]
  rw [h0] at h
  simp [h]

/-- Euler's product `∏ (1 - X^m)` is a unit of `ℤ⟦X⟧`, so its integer powers are defined.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1 (negative exponents). -/
public theorem isUnit_pentagonalSeries_int : IsUnit (pentagonalSeries ℤ) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_pentagonalSeries_int]
  exact isUnit_one

/-- The generalized tau function `τ_k(n)`: the `q^n` coefficient of `q ∏_{m ≥ 1} (1 - q^m)^k`,
for any integer `k`. The paper requires `k ≠ 0`; `k = 0` gives `τ_0(1) = 1` and `0` elsewhere.
`τ_{24}` is Ramanujan's tau function, `τ_1(n + 1)` is Euler's `ω(n)`.

Source: Sriram and Christopher, *Congruences Relating Regular Partition Functions, a Generalized
Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article
A39, Definition 1.1, equation (2). -/
public noncomputable def generalizedTau (k : ℤ) (n : ℕ) : ℤ :=
  coeff n (X * ((isUnit_pentagonalSeries_int.unit ^ k : ℤ⟦X⟧ˣ) : ℤ⟦X⟧))

/-- `τ_k(0) = 0`: the series `q ∏ (1 - q^m)^k` has no constant term.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_zero (k : ℤ) : generalizedTau k 0 = 0 := by
  simp [generalizedTau]

/-- `τ_k(1) = 1` for every integer `k`.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_one (k : ℤ) : generalizedTau k 1 = 1 := by
  rw [generalizedTau, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hu : Units.map (constantCoeff (R := ℤ)).toMonoidHom isUnit_pentagonalSeries_int.unit
      = 1 := by
    ext
    simp [constantCoeff_pentagonalSeries_int]
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (congrArg (· ^ k) hu)
  simp only [one_zpow, Units.val_one, ← map_zpow, Units.coe_map] at h
  exact h

/-- For natural `k`, `τ_k(n)` is the `q^n` coefficient of `q (∏ (1 - q^m))^k`.

Source: Sriram and Christopher, INTEGERS 24 (2024), Article A39, Definition 1.1. -/
public theorem generalizedTau_natCast (k n : ℕ) :
    generalizedTau k n = coeff n (X * pentagonalSeries ℤ ^ k) := by
  simp [generalizedTau]

/-- Binomial-weighted partition sums for `τ_k(n + 1)` and `τ_{-k}(n + 1)`: (a) the sum over
partitions of `n` with every frequency `f ≤ k` of `∏ (-1)^f * C(k, f)`; (b) the sum over all
partitions of `n` of `∏ C(f + k - 1, k - 1)`, the products running over the distinct parts.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 1 (`integers-2024-A39-thm-1`). -/
public theorem_wanted generalizedTau_succ_eq_partition_sum (k : ℕ) (hk : 0 < k) (n : ℕ) :
    (generalizedTau k (n + 1) =
        ∑ p ∈ Finset.univ.filter
            (fun p : Nat.Partition n => ∀ a ∈ p.parts, p.parts.count a ≤ k),
          ∏ a ∈ p.parts.toFinset,
            (-1 : ℤ) ^ p.parts.count a * (k.choose (p.parts.count a) : ℤ)) ∧
      (generalizedTau (-(k : ℤ)) (n + 1) =
        ∑ p : Nat.Partition n,
          ∏ a ∈ p.parts.toFinset, ((p.parts.count a + k - 1).choose (k - 1) : ℤ))

/-- Parity of `τ_k(n + 1)`: with `A = {a : 1 ≤ a ≤ k, C(k, a) odd}`, `τ_k(n + 1) ≡ F_A(n) (mod 2)`,
where `F_A(n)` counts partitions of `n` whose every frequency lies in `A`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 2 (`integers-2024-A39-thm-2`). -/
public theorem_wanted generalizedTau_succ_modEq_card_frequency_two (k : ℕ) (hk : 0 < k) (n : ℕ) :
    generalizedTau k (n + 1) ≡
      ((Finset.univ.filter fun p : Nat.Partition n =>
        ∀ i ∈ p.parts,
          p.parts.count i ∈ (Finset.Icc 1 k).filter (fun a => Odd (k.choose a))).card : ℤ)
      [ZMOD 2]

/-- Parity of the `4`-regular partition function: `R_4(n)` is odd exactly when `n` is a
triangular number `m(m + 1)/2`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 3 (`integers-2024-A39-thm-3`). -/
public theorem_wanted odd_card_four_regular_iff_triangular (n : ℕ) (hn : 0 < n) :
    Odd (Nat.Partition.restricted n (¬ 4 ∣ ·)).card ↔ ∃ m : ℕ, n = m * (m + 1) / 2

/-- (a) `τ_{14}(2n + 1) ≡ R_8(n) (mod 2)`; (b) `τ_6(2n + 1)` is odd exactly when `n` is
triangular.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 4 (`integers-2024-A39-thm-4`). -/
public theorem_wanted generalizedTau_fourteen_six_odd_index_mod_two (n : ℕ) (hn : 0 < n) :
    generalizedTau 14 (2 * n + 1) ≡ ((Nat.Partition.restricted (n) (¬ 8 ∣ ·)).card : ℤ) [ZMOD 2] ∧
      (Odd (generalizedTau 6 (2 * n + 1)) ↔ ∃ m : ℕ, n = m * (m + 1) / 2)

/-- `R_{2^s}(n) ≡ τ_{2^s - 1}(n + 1) (mod 2)` for every positive integer `s`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 5 (`integers-2024-A39-thm-5`). -/
public theorem_wanted card_two_pow_regular_modEq_generalizedTau (s : ℕ) (hs : 0 < s) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ 2 ^ s ∣ ·)).card : ℤ)
        ≡ generalizedTau ((2 : ℤ) ^ s - 1) (n + 1) [ZMOD 2]

/-- Ramanujan's `τ` modulo `3`: `τ(n + 1) ≡ R_9(n/3)` if `3 ∣ n` and `≡ 0` otherwise. Here
`τ = generalizedTau 24`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 6 (`integers-2024-A39-thm-6`). -/
public theorem_wanted ramanujanTau_succ_modEq_nine_regular (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      (if 3 ∣ n then ((Nat.Partition.restricted (n / 3) (¬ 9 ∣ ·)).card : ℤ) else 0) [ZMOD 3]

/-- Ramanujan's congruence `τ(3n) ≡ 0 (mod 3)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 1 (`integers-2024-A39-cor-1`). -/
public theorem_wanted ramanujanTau_three_mul_modEq_zero (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (3 * n) ≡ 0 [ZMOD 3]

/-- `R_9(n) ≡ σ(3n + 1) (mod 3)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 2 (`integers-2024-A39-cor-2`). -/
public theorem_wanted card_nine_regular_modEq_sigma (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (n) (¬ 9 ∣ ·)).card : ℤ)
        ≡ (ArithmeticFunction.sigma 1 (3 * n + 1) : ℤ) [ZMOD 3]

/-- `τ(n + 1) ≡ R_{25}(n) (mod 5)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 7 (`integers-2024-A39-thm-7`). -/
public theorem_wanted ramanujanTau_succ_modEq_twentyfive_regular (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡ ((Nat.Partition.restricted (n) (¬ 25 ∣ ·)).card : ℤ) [ZMOD 5]

/-- `R_{25}(n) ≡ (n + 1) σ(n + 1) (mod 5)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 3 (`integers-2024-A39-cor-3`). -/
public theorem_wanted card_twentyfive_regular_modEq_mul_sigma (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (n) (¬ 25 ∣ ·)).card : ℤ) ≡ ((n + 1 : ℕ) : ℤ)
        * (ArithmeticFunction.sigma 1 (n + 1) : ℤ) [ZMOD 5]

/-- `τ(n + 1) ≡ ∑ (-1)^(m + r) (2m + 1)(2r + 1) (mod 7)`, the sum over `m, r ≥ 0` with
`n = m(m + 1)/2 + 7 r(r + 1)/2`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 8 (`integers-2024-A39-thm-8`). -/
public theorem_wanted ramanujanTau_succ_modEq_triangular_sum_seven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ m ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        if m * (m + 1) / 2 + 7 * (r * (r + 1) / 2) = n then
          (-1 : ℤ) ^ (m + r) * ((2 * m + 1 : ℕ) : ℤ) * ((2 * r + 1 : ℕ) : ℤ)
        else 0 [ZMOD 7]

/-- `τ(n + 1) ≡ ∑ (-1)^(l + m + s + r) (mod 11)`, the sum over generalized pentagonal indices
with `n = P(l) + P(m) + 11 P(s) + 11 P(r)`, `P(r) = r(3r - 1)/2`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 9 (`integers-2024-A39-thm-9`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_sum_eleven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ l ∈ Finset.Icc (-(n : ℤ)) n, ∑ m ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
          ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if pentagonal l + pentagonal m + 11 * pentagonal s + 11 * pentagonal r = n then
          ((l + m + s + r).negOnePow : ℤ)
        else 0 [ZMOD 11]

/-- `τ(n + 1) ≡ ∑ (-1)^r τ_11(s + 1) (mod 13)` over `n = 13 P(r) + s`. The record prints
`τ_11(s)`; that is false (at `n = 1`) and the proof's identity
`∏ (1 - q^m)^11 (1 - q^(13m)) = ∑ (-1)^r τ_11(s + 1) q^(13 P(r) + s)`, from Definition 1.1,
gives the shifted index used here.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 10 (`integers-2024-A39-thm-10`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_eleven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 13 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 11 (n - 13 * pentagonal r + 1)
        else 0 [ZMOD 13]

/-- `τ(n + 1) ≡ ∑ (-1)^r τ_7(s + 1) (mod 17)` over `n = 17 P(r) + s`. The record prints
`τ_7(s)`; that is false (at `n = 1`) and the proof's identity
`∏ (1 - q^m)^7 (1 - q^(17m)) = ∑ (-1)^r τ_7(s + 1) q^(17 P(r) + s)`, from Definition 1.1,
gives the shifted index used here.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 11 (`integers-2024-A39-thm-11`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_seven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 17 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 7 (n - 17 * pentagonal r + 1)
        else 0 [ZMOD 17]

/-- `τ(n + 1) ≡ ∑ (-1)^r τ_5(s + 1) (mod 19)` over `n = 19 P(r) + s`. The record prints
`τ_5(s)`; that is false (at `n = 1`) and the proof's identity
`∏ (1 - q^m)^5 (1 - q^(19m)) = ∑ (-1)^r τ_5(s + 1) q^(19 P(r) + s)`, from Definition 1.1,
gives the shifted index used here.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 12 (`integers-2024-A39-thm-12`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_tau_five (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 19 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 5 (n - 19 * pentagonal r + 1)
        else 0 [ZMOD 19]

/-- `τ(n + 1) ≡ ∑ (-1)^(r + s) (mod 23)` over `n = P(r) + 23 P(s)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 13 (`integers-2024-A39-thm-13`). -/
public theorem_wanted ramanujanTau_succ_modEq_pentagonal_sum_twentythree (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if pentagonal r + 23 * pentagonal s = n then ((r + s).negOnePow : ℤ) else 0
      [ZMOD 23]

/-- `τ(n + 1) ≡ ∑ (-1)^(s + t) (2s + 1) R_5(r) (mod 25)` over `n = r + 5 s(s + 1)/2 + 5 P(t)`
with `r, s ≥ 0`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 14 (`integers-2024-A39-thm-14`). -/
public theorem_wanted ramanujanTau_succ_modEq_five_regular_sum_twentyfive (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
        if 5 * (s * (s + 1) / 2) + 5 * pentagonal t ≤ n then
          (((s : ℤ) + t).negOnePow : ℤ) * ((2 * s + 1 : ℕ) : ℤ) *
            ((Nat.Partition.restricted (n - 5 * (s * (s + 1) / 2) - 5 * pentagonal t)
                (¬ 5 ∣ ·)).card : ℤ)
        else 0 [ZMOD 25]

/-- `τ_{p^s}(n + 1) ≡ (-1)^t (mod p)` if `n = p^s P(t)` and `≡ 0` otherwise, written as a sum
over `t` that has at most one nonzero term (`pentagonal` is injective).

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 15 (`integers-2024-A39-thm-15`). -/
public theorem_wanted generalizedTau_prime_pow_succ_modEq (p : ℕ) (hp : p.Prime) (s : ℕ)
    (hs : 0 < s) (n : ℕ) :
    generalizedTau ((p ^ s : ℕ) : ℤ) (n + 1) ≡
      ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
          if n = p ^ s * pentagonal t then (t.negOnePow : ℤ) else 0 [ZMOD p]

/-- `τ_{2p}(n + 1) ≡ ∑ (-1)^(r + s) (mod p)` over `n = p (P(r) + P(s))`, `p` an odd prime. The
record prints the side condition as `n + 1 = p(P(r) + P(s))`; that is false and the proof's
identity `∑ τ_{2p}(n + 1) q^n ≡ ∏ (1 - q^(pm))^2 (mod p)` gives `n = p(P(r) + P(s))`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 16 (`integers-2024-A39-thm-16`). -/
public theorem_wanted generalizedTau_two_mul_prime_succ_modEq (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (n : ℕ) :
    generalizedTau (2 * p) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = p * (pentagonal r + pentagonal s) then ((r + s).negOnePow : ℤ) else 0
      [ZMOD p]

/-- `τ_{2p}(n + 1) ≡ 0 (mod p)` when `p ∤ n`, `p` an odd prime. The record prints the hypothesis
as `p ∤ n + 1`; that is false, and the corollary follows from Theorem 3.26 (the record's
Theorem 16) in its corrected form, which forces `p ∣ n` for a nonzero residue.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 4 (`integers-2024-A39-cor-4`). -/
public theorem_wanted generalizedTau_two_mul_prime_succ_modEq_zero (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) (hn : ¬ p ∣ n) :
    generalizedTau (2 * p) (n + 1) ≡ 0 [ZMOD p]

/-- `τ_{2p + 1}(n + 1) ≡ ∑ (-1)^(r + s + t) (mod p)` over `n = P(r) + p (P(s) + P(t))`, `p` an odd
prime. The record prints `n + 1 = ...`; that is false and the proof's identity
`∑ τ_{2p+1}(n + 1) q^n ≡ ∏ (1 - q^m)(1 - q^(pm))^2 (mod p)` gives the index `n`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 17 (`integers-2024-A39-thm-17`). -/
public theorem_wanted generalizedTau_two_mul_prime_add_one_succ_modEq (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) :
    generalizedTau (2 * p + 1) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n, ∑ t ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + p * (pentagonal s + pentagonal t) then
          ((r + s + t).negOnePow : ℤ)
        else 0 [ZMOD p]

/-- `τ_{p² + 1}(n + 1) ≡ ∑ (-1)^(r + s) (mod p)` over `n = P(r) + p² P(s)`, `p` an odd prime. The
record prints `n + 1 = ...`; that is false and the proof's identity
`∑ τ_{p²+1}(n + 1) q^n ≡ ∏ (1 - q^m)(1 - q^(p² m)) (mod p)` gives the index `n`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 18 (`integers-2024-A39-thm-18`). -/
public theorem_wanted generalizedTau_prime_sq_add_one_succ_modEq (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (n : ℕ) :
    generalizedTau (p ^ 2 + 1) (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, ∑ s ∈ Finset.Icc (-(n : ℤ)) n,
        if n = pentagonal r + p ^ 2 * pentagonal s then ((r + s).negOnePow : ℤ) else 0
      [ZMOD p]

/-- `R_9(4n + 1) ≡ R_9(n) (mod 3)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 19 (`integers-2024-A39-thm-19`). -/
public theorem_wanted card_nine_regular_four_mul_add_one_modEq (n : ℕ) (hn : 0 < n) :
    ((Nat.Partition.restricted (4 * n + 1) (¬ 9 ∣ ·)).card : ℤ)
    ≡ ((Nat.Partition.restricted (n) (¬ 9 ∣ ·)).card : ℤ) [ZMOD 3]

/-- `R_9((r - 1) 4^(s-1) + (4^s - 1)/3) ≡ R_9(r) (mod 3)`, with the particular cases
`R_9((4^s - 1)/3) ≡ 1`, `R_9(4^(s-1) + (4^s - 1)/3) ≡ 2`, `R_9(2·4^(s-1) + (4^s - 1)/3) ≡ 0`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 5 (`integers-2024-A39-cor-5`). -/
public theorem_wanted card_nine_regular_iterate_modEq (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ((Nat.Partition.restricted ((r - 1) * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
        ≡ ((Nat.Partition.restricted (r) (¬ 9 ∣ ·)).card : ℤ) [ZMOD 3] ∧
      ((Nat.Partition.restricted ((4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ) ≡ 1 [ZMOD 3] ∧
      ((Nat.Partition.restricted (4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ) ≡ 2 [ZMOD 3] ∧
      ((Nat.Partition.restricted (2 * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
          ≡ 0 [ZMOD 3]

/-- `R_p(n) ≡ τ_{p-1}(n + 1) (mod p)` for every prime `p`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 20 (`integers-2024-A39-thm-20`). -/
public theorem_wanted card_prime_regular_modEq_generalizedTau_pred (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((Nat.Partition.restricted (n) (¬ p ∣ ·)).card : ℤ)
        ≡ generalizedTau ((p : ℤ) - 1) (n + 1) [ZMOD p]

/-- For an odd prime `l`, `1 ≤ k < l` and `r = n mod l`: `C(n + k, k) ≡ (-1)^r C(l - k - 1, r)
(mod l)` when `r ≤ l - k - 1`, and `≡ 0` when `r ≥ l - k`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Lemma 1 (`integers-2024-A39-lem-1`). -/
public theorem_wanted choose_add_modEq_prime (l : ℕ) (hl : l.Prime) (hodd : Odd l) (k : ℕ)
    (hk : 1 ≤ k) (hkl : k < l) (n : ℕ) :
    ((n + k).choose k : ℤ) ≡
      (if n % l ≤ l - k - 1 then (-1 : ℤ) ^ (n % l) * ((l - k - 1).choose (n % l) : ℤ)
        else 0) [ZMOD l]

/-- For `2 ≤ k < l`, `l` an odd prime: `τ_{-k}(n + 1) ≡ ∑_{n = t + ls} τ_{l-k}(t + 1) p(s) (mod l)`,
and the same right side is congruent to the composition sum
`∑_{a_1 + ⋯ + a_k = n} p(a_1)⋯p(a_k)`. The record prints `τ_{l-k}(t)`; that is false and the
proof's identity `∏ (1 - q^m)^(-k) ≡ ∏ (1 - q^m)^(l-k) (1 - q^(lm))^(-1) (mod l)` together with
Definition 1.1 (`∏ (1 - q^m)^j = ∑ τ_j(t + 1) q^t`) gives `τ_{l-k}(t + 1)`; Corollary 4.3 (the
record's Corollary 6) uses this shifted form, `ω(t) = τ_1(t + 1)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 21 (`integers-2024-A39-thm-21`). -/
public theorem_wanted generalizedTau_neg_succ_modEq_partition_convolution (k : ℕ) (hk : 2 ≤ k)
    (l : ℕ) (hl : l.Prime) (hodd : Odd l) (hkl : k < l) (n : ℕ) :
    generalizedTau (-(k : ℤ)) (n + 1) ≡
        ∑ s ∈ Finset.range (n / l + 1),
          generalizedTau ((l : ℤ) - k) (n - l * s + 1)
              * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD l] ∧
      (∑ a ∈ Finset.Nat.antidiagonalTuple k n,
          ∏ i, (Fintype.card (Nat.Partition (a i)) : ℤ)) ≡
        ∑ s ∈ Finset.range (n / l + 1),
          generalizedTau ((l : ℤ) - k) (n - l * s + 1)
              * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD l]

/-- `∑_{a + b = n} p(a) p(b) ≡ ∑_{n = t + 3s} ω(t) p(s) (mod 3)`, where `ω(t)` is the `q^t`
coefficient of `∏ (1 - q^m)` (Euler's pentagonal series).

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 6 (`integers-2024-A39-cor-6`). -/
public theorem_wanted partition_convolution_two_modEq_three (n : ℕ) :
    (∑ x ∈ Finset.antidiagonal n,
        (Fintype.card (Nat.Partition x.1) : ℤ) * (Fintype.card (Nat.Partition x.2) : ℤ)) ≡
      ∑ s ∈ Finset.range (n / 3 + 1),
        PowerSeries.coeff (n - 3 * s) (PowerSeries.pentagonalSeries ℤ)
            * (Fintype.card (Nat.Partition s) : ℤ) [ZMOD 3]

/-- For a prime `l ≥ 5` and `m ≥ 0` with `m ≢ 0` and `m ≢ (-1)^r C(l - 3, r) (mod l)` for all
`0 ≤ r ≤ (l - 3)/2`: every `n ≡ m (mod l)` has
`∑_{a_1 + ⋯ + a_{l-3} = n} p(a_1)⋯p(a_{l-3}) ≡ 0 (mod l)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 7 (`integers-2024-A39-cor-7`). -/
public theorem_wanted partition_composition_sum_modEq_zero (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (m : ℕ) (hm0 : ¬ (m : ℤ) ≡ 0 [ZMOD l])
    (hm : ∀ r ≤ (l - 3) / 2, ¬ (m : ℤ) ≡ (-1 : ℤ) ^ r * ((l - 3).choose r : ℤ) [ZMOD l])
    (n : ℕ) (hn : n ≡ m [MOD l]) :
    (∑ a ∈ Finset.Nat.antidiagonalTuple (l - 3) n,
        ∏ i, (Fintype.card (Nat.Partition (a i)) : ℤ)) ≡ 0 [ZMOD l]

/-- Ramanujan's congruence `τ(7n) ≡ 0 (mod 7)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Corollary 8 (`integers-2024-A39-cor-8`). -/
public theorem_wanted ramanujanTau_seven_mul_modEq_zero (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (7 * n) ≡ 0 [ZMOD 7]

/-- If `k - 1` is prime and `k - 1 ∤ n - 1 - P` for every generalized pentagonal number
`P ≤ n - 1`, then `τ_k(n) ≡ 0 (mod k - 1)`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 1 (`integers-2024-A39-prop-1`). -/
public theorem_wanted generalizedTau_modEq_zero_of_pentagonal (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hk : (k - 1).Prime)
    (h : ∀ t : ℤ, pentagonal t ≤ n - 1 → ¬ (k - 1) ∣ n - 1 - pentagonal t) :
    generalizedTau k n ≡ 0 [ZMOD ((k - 1 : ℕ) : ℤ)]

/-- `n τ_k(n + 1) ≡ 0 (mod |k|)` for `|k| ≥ 2`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 2 (`integers-2024-A39-prop-2`). -/
public theorem_wanted mul_generalizedTau_succ_modEq_zero (n : ℕ) (hn : 0 < n) (k : ℤ) (hk : 2 ≤ |k|)
    :
    (n : ℤ) * generalizedTau k (n + 1) ≡ 0 [ZMOD |k|]

/-- `τ_k(|k| m + d r + 1) ≡ 0 (mod |k|/d)` for every divisor `d < |k|` of `|k|` and every `r`
coprime to `|k|/d`.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 3 (`integers-2024-A39-prop-3`). -/
public theorem_wanted generalizedTau_modEq_zero_of_coprime (m : ℕ) (k : ℤ) (hk : 2 ≤ |k|) (d : ℕ)
    (hd : d ∣ k.natAbs) (hdk : d < k.natAbs) (r : ℕ)
    (hr : Nat.gcd r (k.natAbs / d) = 1) :
    generalizedTau k (k.natAbs * m + d * r + 1) ≡ 0 [ZMOD ((k.natAbs / d : ℕ) : ℤ)]

/-- Congruences for `τ(24m + r + 1)` modulo divisors of `24`, from Proposition 2.4 at `k = 24`.
Items 1 and 3 are as printed. Items 2, 4, 5 are false as printed (moduli `12`, `6`, `4`); the
moduli `|k|/gcd(r, 24)` that Proposition 2.4 gives (`6`, `3`, `2`) are used instead.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Proposition 4 (`integers-2024-A39-prop-4`). -/
public theorem_wanted ramanujanTau_modEq_divisors_twentyfour (m : ℕ) :
    (∀ r ∈ ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
        generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 24]) ∧
      (∀ r ∈ ({4, 20} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 6]) ∧
      (∀ r ∈ ({3, 9, 6, 15} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 8]) ∧
      (∀ r ∈ ({8, 16} : Finset ℕ), generalizedTau 24 (24 * m + r + 1) ≡ 0 [ZMOD 3]) ∧
      generalizedTau 24 (24 * m + 13) ≡ 0 [ZMOD 2]

end

end MetaMathlibExt
