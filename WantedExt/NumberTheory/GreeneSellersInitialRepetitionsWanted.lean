/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

/-- For `k ≥ 1`, exactly two residues modulo `2^(2k)` are squares modulo `2^(2k-1)` but not
squares modulo `2^(2k)`, namely `2^(2k-1)` and `2^(2k-1) + 2^(2k-2)` (the paper's "values" are
read as residues `0 ≤ x < 2^(2k)`). Stated for all `k`; at `k = 0` both sides are false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 2
(`integers-2025-A32-lem-2`). -/
public theorem_wanted isSquare_mod_two_pow_odd_not_even_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k)) :
    (IsSquare (x : ZMod (2 ^ (2 * k - 1))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k)))) ↔
      x = 2 ^ (2 * k - 1) ∨ x = 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2)

/-- For `k ≥ 1`, `2^(2k) + 2^(2k-2)` is the unique residue modulo `2^(2k+1)` that is a square
modulo `2^(2k)` but not a square modulo `2^(2k+1)`. Stated for all `k`; at `k = 0` both sides are
false.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 3
(`integers-2025-A32-lem-3`). -/
public theorem_wanted isSquare_mod_two_pow_even_not_odd_iff (k : ℕ) (x : ℕ)
    (hx : x < 2 ^ (2 * k + 1)) :
    (IsSquare (x : ZMod (2 ^ (2 * k))) ∧ ¬IsSquare (x : ZMod (2 ^ (2 * k + 1)))) ↔
      x = 2 ^ (2 * k) + 2 ^ (2 * k - 2)

open scoped Classical in
/-- For a prime `p` (the paper assumes `p ≥ 5`; both sides are `0` at `p = 2, 3`), the number of
`r` with `1 ≤ r ≤ p - 1` such that neither `16r + 1` nor
`8r + 1` is a square modulo `p` equals `⌊p / 4⌋`. "Quadratic residue" is read as "square in
`ZMod p`", so `0` counts as a residue; with nonzero residues only the count is `2` at `p = 5`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 5 (`integers-2025-A32-thm-5`). -/
public theorem_wanted card_not_isSquare_sixteen_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((16 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      p / 4

open scoped Classical in
/-- For a prime `p` (the paper assumes `p ≥ 5`; both sides are `0` at `p = 2, 3`), the number of
`r` with `1 ≤ r ≤ p - 1` such that neither `12r + 1` nor
`8r + 1` is a square modulo `p` is `⌊p / 4⌋ - 1` if `p ≡ 5 (mod 24)`, `⌊p / 4⌋ + 1` if
`p ≡ 11 (mod 24)`, and `⌊p / 4⌋` otherwise. "Quadratic residue" is read as "square in `ZMod p`",
so `0` counts as a residue; with nonzero residues only the count is `2` at `p = 5`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 8 (`integers-2025-A32-thm-8`). -/
public theorem_wanted card_not_isSquare_twelve_mul_add_one_eight_mul_add_one (p : ℕ)
    (hp : p.Prime) :
    ((Finset.Icc 1 (p - 1)).filter fun r =>
        ¬IsSquare ((12 * r + 1 : ℕ) : ZMod p) ∧ ¬IsSquare ((8 * r + 1 : ℕ) : ZMod p)).card =
      if p % 24 = 5 then p / 4 - 1 else if p % 24 = 11 then p / 4 + 1 else p / 4

/-- For an odd prime `p` and integers `m, n` with `p ∤ mn(n - m)`, the number `N` of
`0 ≤ r ≤ p - 1` with `mr + 1` and `nr + 1` both quadratic nonresidues modulo `p` satisfies
`N = ⌊p/4⌋ - (1/4)((m/p) - ((n-m)/p))((n/p) - ((m-n)/p))`, stated multiplied by `4`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Lemma 1
(`integers-2025-A32-lem-1`). -/
public theorem_wanted four_mul_card_legendreSym_pair_eq_neg_one (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (m n : ℤ) (hmn : ¬ (p : ℤ) ∣ m * n * (n - m)) :
    4 * ((((Finset.range p).filter fun r : ℕ =>
        legendreSym p (m * r + 1) = -1 ∧ legendreSym p (n * r + 1) = -1).card : ℕ) : ℤ) =
      4 * ((p / 4 : ℕ) : ℤ) -
        (legendreSym p m - legendreSym p (n - m)) * (legendreSym p n - legendreSym p (m - n))

/-- Andrews' theorem on partitions with initial `k`-repetitions (if some `j` appears at least
`k` times, then every positive integer below `j` appears at least `k` times): for `k ≥ 1` their
number equals the number of partitions of `n` into parts not divisible by `2k`, which equals the
number of partitions of `n` in which no part appears more than `2k - 1` times.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 1 (`integers-2025-A32-thm-1`), quoting Andrews. -/
public theorem_wanted card_initialRepetitions_eq_card_not_dvd_eq_card_count_le (n k : ℕ)
    (hk : 1 ≤ k) :
    ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ j ∈ p.parts, k ≤ p.parts.count j → ∀ i ∈ Finset.Ico 1 j, k ≤ p.parts.count i).card =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, ¬ 2 * k ∣ a).card ∧
    ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, ¬ 2 * k ∣ a).card =
      ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
        ∀ a ∈ p.parts, p.parts.count a ≤ 2 * k - 1).card

/-- `c₂(n)`: the number of partitions of `n` with some `j ≥ 1` appearing exactly `j` times as
the only part less than `2j + 1`, even parts `≥ 2j + 2` distinct, odd parts `≥ 2j + 1`
unrestricted.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₂`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC2 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    ∃ j ∈ Finset.Icc 1 n, p.parts.count j = j ∧ (∀ a ∈ p.parts, a = j ∨ 2 * j + 1 ≤ a) ∧
      ∀ a ∈ p.parts, Even a → 2 * j + 2 ≤ a → p.parts.count a = 1).card

/-- `c₃(n)`: the number of partitions of `n` with a positive integer `j` such that `1` appears
`j²` or `j² + 1` times, odd parts larger than `1` are distinct, all even parts are distinct, and
even parts greater than `2j` are at least `4j + 4` and divisible by `4`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₃`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC3 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    ∃ j ∈ Finset.Icc 1 n, (p.parts.count 1 = j ^ 2 ∨ p.parts.count 1 = j ^ 2 + 1) ∧
      (∀ a ∈ p.parts, Odd a → 1 < a → p.parts.count a = 1) ∧
      (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
      ∀ a ∈ p.parts, Even a → 2 * j < a → 4 * j + 4 ≤ a ∧ 4 ∣ a).card

/-- `c₈(n)`: the number of partitions of `n` in which either (a) all parts are even and
distinct, or (b) the largest odd part is `2j - 1`, every odd integer `≤ j` appears once or twice,
every odd integer in `(j, 2j - 1]` appears once, all even parts are distinct, and even parts
greater than `j` are at least `2j + 2`. For `j = 1` the paper's clauses "the largest odd part
`2j - 1` appears once" and "odd integers `≤ j` appear once or twice" conflict; the second governs,
as in the generating function `(q²;q²)_∞ ∑ q^{n²}/(q;q)_n` the paper uses (the other reading gives
`c₈(2) = 1`, contradicting Theorem 11 since `31` is not a square).

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 3 (definition of `c₈`, from Nyirenda and Mugwangwavari). -/
public def initialRepetitionsC8 (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
    (∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1) ∨
      ∃ j ∈ Finset.Icc 1 n, 2 * j - 1 ∈ p.parts ∧ (∀ a ∈ p.parts, Odd a → a ≤ 2 * j - 1) ∧
        (∀ i ∈ Finset.Icc 1 j, Odd i → p.parts.count i = 1 ∨ p.parts.count i = 2) ∧
        (∀ i ∈ Finset.Ioc j (2 * j - 1), Odd i → p.parts.count i = 1) ∧
        (∀ a ∈ p.parts, Even a → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, Even a → j < a → 2 * j + 2 ≤ a).card

/-- `c₈'(n)`: the number of partitions of `n`, with a possibly distinguished part, in which
either (a) all parts are even and distinct and no part is distinguished, or (b) a distinguished
even part `2m` (`m ≥ 1`) is present together with all smaller even parts, even parts `≤ m` appear
at most twice, odd parts `≤ m` are distinct, and every part greater than `m` is even and distinct.
Case (b) is counted once for each admissible `m`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Section 4 (definition of `c₈'`). -/
public def initialRepetitionsC8Prime (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      ∀ a ∈ p.parts, Even a ∧ p.parts.count a = 1).card +
    ∑ m ∈ Finset.Icc 1 n, ((Finset.univ : Finset (Nat.Partition n)).filter fun p =>
      (∀ i ∈ Finset.Icc 1 m, 2 * i ∈ p.parts) ∧
        (∀ a ∈ p.parts, Even a → a ≤ m → p.parts.count a ≤ 2) ∧
        (∀ a ∈ p.parts, Odd a → a ≤ m → p.parts.count a = 1) ∧
        ∀ a ∈ p.parts, m < a → Even a ∧ p.parts.count a = 1).card

/-- Values at `0` and `1`: `c₂(0) = 0`, `c₂(1) = 1`, `c₃(1) = 1`, `c₈(0) = c₈(1) = 1`,
`c₈'(0) = 1` and `c₈'(1) = 0`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Sections 3 and 4 (definitions of `c₂`, `c₃`, `c₈`, `c₈'`). -/
public theorem initialRepetitions_values_zero_one :
    initialRepetitionsC2 0 = 0 ∧ initialRepetitionsC2 1 = 1 ∧ initialRepetitionsC3 1 = 1 ∧
      initialRepetitionsC8 0 = 1 ∧ initialRepetitionsC8 1 = 1 ∧
      initialRepetitionsC8Prime 0 = 1 ∧ initialRepetitionsC8Prime 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initialRepetitionsC2, initialRepetitionsC3, initialRepetitionsC8,
      initialRepetitionsC8Prime, Finset.univ_unique, Finset.filter_singleton]
  all_goals decide

/-- Nyirenda and Mugwangwavari: `c₂(5n + 2)` is even for all `n ≥ 0`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 3 (`integers-2025-A32-thm-3`). -/
public theorem_wanted initialRepetitionsC2_five_mul_add_two_even (n : ℕ) :
    Even (initialRepetitionsC2 (5 * n + 2))

/-- For a prime `p ≥ 5` and `1 ≤ r ≤ p - 1` such that neither `16r + 1` nor `8r + 1` is a
square modulo `p`, `c₂(pn + r)` is even for all `n ≥ 0`. "Quadratic residue" is read as "square
in `ZMod p`", so `0` counts as a residue.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 4 (`integers-2025-A32-thm-4`). -/
public theorem_wanted initialRepetitionsC2_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h16 : ¬ IsSquare ((16 * r + 1 : ℕ) : ZMod p)) (h8 : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC2 (p * n + r))

/-- Nyirenda and Mugwangwavari: `c₃(11n + 5)`, `c₃(11n + 7)` and `c₃(11n + 9)` are even for
all `n ≥ 0`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 6 (`integers-2025-A32-thm-6`). -/
public theorem_wanted initialRepetitionsC3_eleven_mul_add_even (n : ℕ) :
    Even (initialRepetitionsC3 (11 * n + 5)) ∧ Even (initialRepetitionsC3 (11 * n + 7)) ∧
      Even (initialRepetitionsC3 (11 * n + 9))

/-- For a prime `p ≥ 5` and `1 ≤ r ≤ p - 1` such that neither `12r + 1` nor `8r + 1` is a
square modulo `p`, `c₃(pn + r)` is even for all `n ≥ 0`. "Quadratic residue" is read as "square
in `ZMod p`", so `0` counts as a residue.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 7 (`integers-2025-A32-thm-7`). -/
public theorem_wanted initialRepetitionsC3_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h12 : ¬ IsSquare ((12 * r + 1 : ℕ) : ZMod p)) (h8 : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC3 (p * n + r))

/-- Nyirenda and Mugwangwavari: `c₈(49n + r)` is even for all `n ≥ 0` and
`r ∈ {6, 20, 27, 34, 41, 48}`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 9 (`integers-2025-A32-thm-9`). -/
public theorem_wanted initialRepetitionsC8_fortyNine_mul_add_even (n r : ℕ)
    (hr : r ∈ ({6, 20, 27, 34, 41, 48} : Finset ℕ)) :
    Even (initialRepetitionsC8 (49 * n + r))

/-- Andrews' identity (6.22): for `|q| < 1`,
`(q²;q²)_∞ ∑_{j ≥ 0} q^{j²}/(q;q)_j = ∑_{λ ∈ ℤ} (q^{60λ²+4λ} - q^{60λ²+44λ+8} + q^{60λ²+16λ+1}
- q^{60λ²+64λ+17})`. All exponents are nonnegative for integer `λ`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 10 (`integers-2025-A32-thm-10`), quoting Andrews. -/
public theorem_wanted andrews_rogersRamanujan_first_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
      ∑' j : ℕ, q ^ (j ^ 2) / ∏ i ∈ Finset.range j, (1 - q ^ (i + 1)) =
    ∑' l : ℤ, (q ^ (60 * l ^ 2 + 4 * l) - q ^ (60 * l ^ 2 + 44 * l + 8) +
      q ^ (60 * l ^ 2 + 16 * l + 1) - q ^ (60 * l ^ 2 + 64 * l + 17))

/-- `c₈(N)` is even for every `N ≥ 0` such that `15N + 1` is not a square.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 11 (`integers-2025-A32-thm-11`). -/
public theorem_wanted initialRepetitionsC8_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 1)) :
    Even (initialRepetitionsC8 N)

/-- Andrews' identity (6.23): for `|q| < 1`,
`(q²;q²)_∞ ∑_{j ≥ 0} q^{j²+j}/(q;q)_j = ∑_{λ ∈ ℤ} (q^{60λ²+8λ} - q^{60λ²+32λ+4} + q^{60λ²+28λ+3}
- q^{60λ²+52λ+11})`. All exponents are nonnegative for integer `λ`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 12 (`integers-2025-A32-thm-12`), quoting Andrews. -/
public theorem_wanted andrews_rogersRamanujan_second_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInf (q ^ 2) (q ^ 2)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero) *
      ∑' j : ℕ, q ^ (j ^ 2 + j) / ∏ i ∈ Finset.range j, (1 - q ^ (i + 1)) =
    ∑' l : ℤ, (q ^ (60 * l ^ 2 + 8 * l) - q ^ (60 * l ^ 2 + 32 * l + 4) +
      q ^ (60 * l ^ 2 + 28 * l + 3) - q ^ (60 * l ^ 2 + 52 * l + 11))

/-- `c₈'(N)` is even for every `N ≥ 0` such that `15N + 4` is not a square.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Theorem 13 (`integers-2025-A32-thm-13`). -/
public theorem_wanted initialRepetitionsC8Prime_even_of_not_isSquare (N : ℕ)
    (hN : ¬ IsSquare (15 * N + 4)) :
    Even (initialRepetitionsC8Prime N)

/-- For `k ≥ 1` and `n ≥ 0`, `c₈(2^{2k} n + r)` is even when `r < 2^{2k}` and
`15 r ≡ 2^{2k-1} - 1` or `15 r ≡ 2^{2k-1} + 2^{2k-2} - 1 (mod 2^{2k})`, and `c₈(2^{2k+1} n + r)` is
even when `r < 2^{2k+1}` and `15 r ≡ 2^{2k} + 2^{2k-2} - 1 (mod 2^{2k+1})`. These `r` are the
paper's least nonnegative residues `r_{k,1}, r_{k,2}, r_{k,3}`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 1 (`integers-2025-A32-cor-1`). -/
public theorem_wanted initialRepetitionsC8_two_pow_mul_add_even (k n r : ℕ) (hk : 1 ≤ k) :
    (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) - 1 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2) - 1 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k + 1) →
        (15 * r : ℤ) ≡ 2 ^ (2 * k) + 2 ^ (2 * k - 2) - 1 [ZMOD 2 ^ (2 * k + 1)] →
        Even (initialRepetitionsC8 (2 ^ (2 * k + 1) * n + r)))

/-- For a prime `p ≥ 7` and `1 ≤ r ≤ p - 1` such that `15r + 1` is not a square modulo `p`,
`c₈(pn + r)` is even for all `n ≥ 0`. "Quadratic residue" is read as "square in `ZMod p`", so `0`
counts as a residue.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 2 (`integers-2025-A32-cor-2`). -/
public theorem_wanted initialRepetitionsC8_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 1 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8 (p * n + r))

/-- For `k ≥ 1` and `n ≥ 0`, `c₈'(2^{2k} n + r)` is even when `r < 2^{2k}` and
`15 r ≡ 2^{2k-1} - 4` or `15 r ≡ 2^{2k-1} + 2^{2k-2} - 4 (mod 2^{2k})`, and `c₈'(2^{2k+1} n + r)`
is even when `r < 2^{2k+1}` and `15 r ≡ 2^{2k} + 2^{2k-2} - 4 (mod 2^{2k+1})`. These `r` are the
paper's least nonnegative residues `r'_{k,1}, r'_{k,2}, r'_{k,3}`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 3 (`integers-2025-A32-cor-3`). -/
public theorem_wanted initialRepetitionsC8Prime_two_pow_mul_add_even (k n r : ℕ) (hk : 1 ≤ k) :
    (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) - 4 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k) → (15 * r : ℤ) ≡ 2 ^ (2 * k - 1) + 2 ^ (2 * k - 2) - 4 [ZMOD 2 ^ (2 * k)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k) * n + r))) ∧
      (r < 2 ^ (2 * k + 1) →
        (15 * r : ℤ) ≡ 2 ^ (2 * k) + 2 ^ (2 * k - 2) - 4 [ZMOD 2 ^ (2 * k + 1)] →
        Even (initialRepetitionsC8Prime (2 ^ (2 * k + 1) * n + r)))

/-- For a prime `p ≥ 7` and `1 ≤ r ≤ p - 1` such that `15r + 4` is a quadratic nonresidue
modulo `p` (not a square in `ZMod p`), `c₈'(pn + r)` is even for all `n ≥ 0`.

Source: John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and
Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32,
Corollary 4 (`integers-2025-A32-cor-4`). -/
public theorem_wanted initialRepetitionsC8Prime_prime_mul_add_even (p r n : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : r ∈ Finset.Icc 1 (p - 1))
    (h15 : ¬ IsSquare ((15 * r + 4 : ℕ) : ZMod p)) :
    Even (initialRepetitionsC8Prime (p * n + r))

end

end MetaMathlibExt
