/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Interval
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Linear relations for overpartitions into odd parts (statements)

Statement-only targets from Deepthi G. and S. Chandankumar, *Linear Relations for
Overpartitions into Odd Parts*. `po(m)` is `overpartitionOddPartsCount m`, counted with the
existing `Nat.Overpartition` structure; `p(m)` is `Fintype.card (Nat.Partition m)`. The
paper's sums over all `k` (with `po`, `p` vanishing at negative arguments) become finite
sums over the `k` whose shifted argument is nonnegative. The paper's `p̄(m)` (overpartitions),
`pd(m)` (distinct parts) and `pdo(m)` (distinct odd parts) are `Nat.card (Nat.Overpartition m)`,
`(Nat.Partition.distincts m).card` and `(Nat.Partition.oddDistincts m).card`. Statements of
Theorems 1-2, 6, 8-14 and Corollaries 1, 3-5 were checked against the arXiv version
(arXiv:2403.05866v1, numbered Theorems 1.1-1.2 and 3.1-3.9, Corollaries 3.1-3.5).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The number `po(n)` of overpartitions of `n` into odd parts: overpartitions
(`Nat.Overpartition n`) all of whose parts are odd.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, title and Section 1 (values `po(0), …, po(10)`
listed after Theorem 5). -/
public noncomputable def overpartitionOddPartsCount (n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, Odd a}

/-- Characteristic value `po(0) = 1` (the empty overpartition).

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, value `po(0) = 1` listed after Theorem 5. -/
public theorem overpartitionOddPartsCount_zero : overpartitionOddPartsCount 0 = 1 := by
  unfold overpartitionOddPartsCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Nat.Overpartition.ofPartition default, fun a ha => ?_⟩, fun y => ?_⟩
  · simp [Nat.Overpartition.ofPartition_toPartition, Nat.Partition.partition_zero_parts] at ha
  · exact Subtype.ext (Nat.Overpartition.eq_of_zero _ _)

/-- Pentagonal recurrence for overpartitions into odd parts: for `n ≥ 0`,
`∑_{k ∈ ℤ} (-1)^k po(n - k(3k+1)/2)` equals `(-1)^{⌈m/2⌉}` if `n = m(3m+1)/2` for some
`m ∈ ℤ` and `0` otherwise. Only `|k|, |m| ≤ n` can contribute; `⌈m/2⌉ = ⌊(m+1)/2⌋`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 3 (`integers-2026-A60-thm-3`). -/
public theorem_wanted overpartitionOdd_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * (overpartitionOddPartsCount (n - (k * (3 * k + 1) / 2).toNat) : ℤ)
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0

/-- Triangular recurrence for overpartitions into odd parts: for `n ≥ 0`,
`∑_{k ≥ 0} (-1)^{⌈k/2⌉} po(n - k(k+1)/2)` equals `1` if `n = m(m+1)/2` for some `m ≥ 0`
and `0` otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 4 (`integers-2026-A60-thm-4`). -/
public theorem_wanted overpartitionOdd_triangular_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((k + 1) / 2) * (overpartitionOddPartsCount (n - k * (k + 1) / 2) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun m => m * (m + 1) / 2) then 1 else 0

/-- Square recurrence for overpartitions into odd parts: for `n ≥ 0`,
`po(n) + 2 ∑_{k ≥ 1} (-1)^k po(n - 2k²)` equals `2` if `n = m²` with `m ≥ 1`, `1` if
`n = 0`, and `0` otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 5 (`integers-2026-A60-thm-5`). -/
public theorem_wanted overpartitionOdd_square_recurrence (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (overpartitionOddPartsCount (n - 2 * k ^ 2) : ℤ)
      = if n = 0 then 1 else if n ∈ (Finset.Icc 1 n).image (fun m => m ^ 2) then 2 else 0

/-- Overpartitions into odd parts from partitions: for `n ≥ 0`,
`po(n) = ∑_{k ∈ ℤ} (-1)^{⌈k/2⌉} p(n - k(3k+1)/2)`; only `|k| ≤ n` can contribute.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 7 (`integers-2026-A60-thm-7`). -/
public theorem_wanted overpartitionOdd_eq_sum_partition_pentagonal (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
          (-1 : ℤ) ^ ((k + 1) / 2).natAbs
            * (Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat)) : ℤ)

/-- Parity form of Euler's pentagonal recurrence: for `n > 0`,
`∑_{k ∈ ℤ} p(n - k(3k+1)/2) ≡ 0 (mod 2)`; only `|k| ≤ n` can contribute.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 2 (`integers-2026-A60-cor-2`). -/
public theorem_wanted partition_pentagonal_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
      Fintype.card (Nat.Partition (n - (k * (3 * k + 1) / 2).toNat)))

/-- `ped(n)`: the number of partitions of `n` in which the even parts are distinct (odd parts
unrestricted); generating function `(q^4; q^4)_∞ / (q; q)_∞`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 1 (definition of `ped(n)` before Theorem 1). -/
public def distinctEvenPartsCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter
    fun p => ∀ i ∈ p.parts, Even i → p.parts.count i = 1).card

/-- `pod(n)`: the number of partitions of `n` in which the odd parts are distinct (even parts
unrestricted); generating function `(-q; q^2)_∞ / (q^2; q^2)_∞`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `pod(n)` before Theorem 6). -/
public def distinctOddPartsCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter
    fun p => ∀ i ∈ p.parts, Odd i → p.parts.count i = 1).card

/-- `P_2(n)`: the number of partitions of `n` with no part congruent to `2` modulo `4`;
generating function `(q^2; q^4)_∞ / (q; q)_∞`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `P_2(n)` before Theorem 11). -/
public def partsNotTwoModFourCount (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n fun i => i % 4 ≠ 2).card

/-- `q(n)`: the number of bipartitions of `n` into distinct parts, i.e. ordered pairs of
partitions into distinct parts whose sizes add up to `n`; generating function `(-q; q)_∞^2`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `q(n)` before Theorem 12). -/
public def distinctPartsBipartitionCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.Partition.distincts k).card * (Nat.Partition.distincts (n - k)).card

/-- Characteristic values `ped(0) = pod(0) = P_2(0) = q(0) = 1` (the empty partition).

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Sections 1 and 3 (definitions of `ped`, `pod`,
`P_2`, `q`). -/
public theorem distinctEvenParts_distinctOddParts_partsNotTwoModFour_bipartition_zero :
    distinctEvenPartsCount 0 = 1 ∧ distinctOddPartsCount 0 = 1 ∧
      partsNotTwoModFourCount 0 = 1 ∧ distinctPartsBipartitionCount 0 = 1 := by
  decide

/-- Merca's triangular recurrence for `ped`: for `n ≥ 0`,
`∑_{j ≥ 0} (-1)^{⌈j/2⌉} ped(n - j(j+1)/2)` equals `1` if `n = k(k+1)` for some `k ≥ 0` and `0`
otherwise; `⌈j/2⌉ = ⌊(j+1)/2⌋`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 1, quoting M. Merca (via da Silva and Sakai)
(`integers-2026-A60-thm-1`). -/
public theorem_wanted distinctEvenParts_triangular_recurrence (n : ℕ) :
    ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j * (j + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((j + 1) / 2) * (distinctEvenPartsCount (n - j * (j + 1) / 2) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1)) then 1 else 0

/-- Merca's square recurrence for `ped`: for `n ≥ 0`, `∑_{j ∈ ℤ} (-1)^j ped(n - 2j²)` equals
`1` if `n = k(k+1)/2` for some `k ≥ 0` and `0` otherwise; only `|j| ≤ n` can contribute.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 2, quoting M. Merca (via da Silva and Sakai)
(`integers-2026-A60-thm-2`). -/
public theorem_wanted distinctEvenParts_square_recurrence (n : ℕ) :
    ∑ j ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun j : ℤ => 2 * j ^ 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ j.natAbs * (distinctEvenPartsCount (n - (2 * j ^ 2).toNat) : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun k => k * (k + 1) / 2) then 1 else 0

/-- For `n ≥ 0`, `po(n) = ∑_{k ≥ 0} pod(n - k(k+1)/2)`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 6 (`integers-2026-A60-thm-6`). -/
public theorem_wanted overpartitionOdd_eq_sum_distinctOddParts_triangular (n : ℕ) :
    overpartitionOddPartsCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        distinctOddPartsCount (n - k * (k + 1) / 2)

/-- For `n > 0`, `∑_{k ≥ 0} pod(n - k(k+1)/2) ≡ 0 (mod 2)`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 1 (`integers-2026-A60-cor-1`). -/
public theorem_wanted distinctOddParts_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      distinctOddPartsCount (n - k * (k + 1) / 2))

/-- For `n ≥ 0`, `po(n) = ∑_{k ∈ ℤ} (-1)^k p̄(n - 2k²)`, where `p̄(m) = Nat.card
(Nat.Overpartition m)` is the overpartition function; only `|k| ≤ n` can contribute. The
extracted record shows `p`; the overline is displayed in the arXiv version (Theorem 3.3, whose
proof uses the overpartition generating function (1.1)), and with the ordinary partition
function the identity fails at `n = 1` (`po(1) = 2`, `p(1) = 1`).

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 8 (`integers-2026-A60-thm-8`). -/
public theorem_wanted overpartitionOdd_eq_sum_overpartition_square (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ) =
      ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => 2 * k ^ 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs * (Nat.card (Nat.Overpartition (n - (2 * k ^ 2).toNat)) : ℤ)

/-- For `n ≥ 0`, `po(2n+1) = 2 ∑_{k ≥ 0} p̄(n - 2k(k+1))`, with `p̄` the overpartition function
(overline displayed in the arXiv version, Theorem 3.4; with `p` the identity fails at `n = 1`).

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 9 (`integers-2026-A60-thm-9`). -/
public theorem_wanted overpartitionOdd_odd_eq_two_mul_sum_overpartition (n : ℕ) :
    overpartitionOddPartsCount (2 * n + 1) =
      2 * ∑ k ∈ (Finset.range (n + 1)).filter (fun k => 2 * k * (k + 1) ≤ n),
        Nat.card (Nat.Overpartition (n - 2 * k * (k + 1)))

/-- For `n ≥ 0`, `po(2n) = p̄(n) + 2 ∑_{k ≥ 1} p̄(n - 2k²)`, with `p̄` the overpartition
function. Corrected reading: the record prints the sum from `k = 0` and `p` without overline;
the arXiv proof (Theorem 3.5) multiplies the overpartition generating function by
`∑_{k ∈ ℤ} q^{2k²} = 1 + 2 ∑_{k ≥ 1} q^{2k²}`. As printed it fails at `n = 0`
(`po(0) = 1` but `p̄(0) + 2 p̄(0) = 3`).

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 10 (`integers-2026-A60-thm-10`). -/
public theorem_wanted overpartitionOdd_even_eq_sum_overpartition (n : ℕ) :
    overpartitionOddPartsCount (2 * n) =
      Nat.card (Nat.Overpartition n) +
        2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          Nat.card (Nat.Overpartition (n - 2 * k ^ 2))

/-- `po(n) = ∑_{k ≥ 0} P_2(n - k(k+1)/2)`. The paper states it for positive `n`; it also holds
at `n = 0` (both sides `1`), so it is stated for all `n`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 11 (`integers-2026-A60-thm-11`). -/
public theorem_wanted overpartitionOdd_eq_sum_partsNotTwoModFour_triangular (n : ℕ) :
    overpartitionOddPartsCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        partsNotTwoModFourCount (n - k * (k + 1) / 2)

/-- For `n > 0`, `∑_{k ≥ 0} P_2(n - k(k+1)/2) ≡ 0 (mod 2)`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 3 (`integers-2026-A60-cor-3`). -/
public theorem_wanted partsNotTwoModFour_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      partsNotTwoModFourCount (n - k * (k + 1) / 2))

/-- `q(n) = ∑_{k ≥ 0} p(n - k(k+1)/2)`, with `q(n)` the number of bipartitions of `n` into
distinct parts. The paper states it for positive `n`; it also holds at `n = 0` (both sides
`1`), so it is stated for all `n`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 12 (`integers-2026-A60-thm-12`). -/
public theorem_wanted distinctPartsBipartition_eq_sum_partition_triangular (n : ℕ) :
    distinctPartsBipartitionCount n =
      ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        Fintype.card (Nat.Partition (n - k * (k + 1) / 2))

/-- For `n ≥ 0`, `∑_{k ∈ ℤ} (-1)^k po(n - k(3k+1)/2) = ∑_{k ∈ ℤ} (-1)^k pdo(n - k(3k+1))`, with
`pdo(m) = #(Nat.Partition.oddDistincts m)` the number of partitions into distinct odd parts;
only `|k| ≤ n` can contribute.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 13 (`integers-2026-A60-thm-13`). -/
public theorem_wanted overpartitionOdd_pentagonal_sum_eq_oddDistincts (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) / 2 ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * (overpartitionOddPartsCount (n - (k * (3 * k + 1) / 2).toNat) : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
          (-1 : ℤ) ^ k.natAbs
            * ((Nat.Partition.oddDistincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)

/-- Recurrence for partitions into distinct odd parts: for `n ≥ 0`,
`∑_{k ∈ ℤ} (-1)^k pdo(n - k(3k+1))` equals `(-1)^{⌈m/2⌉}` if `n = m(3m+1)/2` for some `m ∈ ℤ`
and `0` otherwise; `⌈m/2⌉ = ⌊(m+1)/2⌋`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 4 (`integers-2026-A60-cor-4`). -/
public theorem_wanted oddDistincts_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * ((Nat.Partition.oddDistincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)
      = ∑ m ∈ Finset.Icc (-(n : ℤ)) n,
          if m * (3 * m + 1) / 2 = n then (-1 : ℤ) ^ ((m + 1) / 2).natAbs else 0

/-- For `n ≥ 0`, `∑_{k ≥ 0} (-1)^{⌈k/2⌉} po(n - k(k+1)/2) = ∑_{k ∈ ℤ} (-1)^k pd(n - k(3k+1))`,
with `pd(m) = #(Nat.Partition.distincts m)`. Corrected reading: the record (and the arXiv
Theorem 3.9) sums the left side over all `k ∈ ℤ`, which fails at `n = 0` (left side `2`, from
`k = 0` and `k = -1`; right side `1`); the proof uses the one-sided series (2.6) over `k ≥ 0`.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 14 (`integers-2026-A60-thm-14`). -/
public theorem_wanted overpartitionOdd_triangular_sum_eq_distincts (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ ((k + 1) / 2) * (overpartitionOddPartsCount (n - k * (k + 1) / 2) : ℤ)
      = ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
          (-1 : ℤ) ^ k.natAbs
            * ((Nat.Partition.distincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)

/-- Recurrence for partitions into distinct parts: for `n ≥ 0`,
`∑_{k ∈ ℤ} (-1)^k pd(n - k(3k+1))` equals `1` if `n = m(m+1)/2` for some `m ≥ 0` and `0`
otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 5 (`integers-2026-A60-cor-5`). -/
public theorem_wanted distincts_pentagonal_recurrence (n : ℕ) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => k * (3 * k + 1) ≤ (n : ℤ)),
        (-1 : ℤ) ^ k.natAbs
          * ((Nat.Partition.distincts (n - (k * (3 * k + 1)).toNat)).card : ℤ)
      = if n ∈ (Finset.range (n + 1)).image (fun m => m * (m + 1) / 2) then 1 else 0

end

end MetaMathlibExt
