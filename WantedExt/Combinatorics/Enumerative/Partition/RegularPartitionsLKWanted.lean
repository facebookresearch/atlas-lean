/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Defs
public import WantedExt.Combinatorics.Enumerative.Partition.PondPendCongruencesWanted

/-!
# Congruences for `(ℓ, k)`-regular partitions

Statements from Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of
Kathiravan, Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of
Integer Sequences 28 (2025), Article 25.6.1.

`b_{ℓ,k}(n)` counts the partitions of `n` with no part divisible by `ℓ` or by `k`. The paper
writes `f_k = (q^k; q^k)_∞`, which is `qEulerProduct k` (written `𝔣 k` below). Eta-quotient
identities are stated in `ℤ⟦X⟧` with denominators cleared.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- `b_{ℓ,k}(n)`, the number of `(ℓ, k)`-regular partitions of `n`: partitions of `n` none of
whose parts is divisible by `ℓ` or by `k`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public def regularPartitionCount (l k n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => ∀ i ∈ p.parts, ¬ l ∣ i ∧ ¬ k ∣ i).card

/-- `b_{4,9}(0) = 1`: the empty partition is `(4, 9)`-regular.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public theorem regularPartitionCount_four_nine_zero : regularPartitionCount 4 9 0 = 1 := by
  decide

/-- If `n < ℓ` and `n < k`, every partition of `n` is `(ℓ, k)`-regular, so `b_{ℓ,k}(n) = p(n)`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public theorem regularPartitionCount_of_lt {l k n : ℕ} (hl : n < l) (hk : n < k) :
    regularPartitionCount l k n = Fintype.card n.Partition := by
  rw [regularPartitionCount, Finset.filter_true_of_mem, Finset.card_univ]
  intro p _ i hi
  have hpos := p.parts_pos hi
  have hle : i ≤ n := by
    rw [← p.parts_sum]
    exact Multiset.le_sum_of_mem hi
  exact ⟨fun h => absurd (Nat.le_of_dvd hpos h) (by omega),
    fun h => absurd (Nat.le_of_dvd hpos h) (by omega)⟩

/-- For a prime `p ≥ 5` and `r` with `8r + 1` a quadratic nonresidue modulo `p`,
`b_{4,p}(pn + r) ≡ 0 (mod 2)` for all `n ≥ 0`. Here `r ∈ ℕ`; every residue class mod `p`
has such a representative.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 1 (`jis-2025-25.6.1-thm-1`). -/
public theorem_wanted regularPartitionCount_four_prime_mod_two {p r : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hr : ¬ IsSquare ((8 * r + 1 : ℕ) : ZMod p)) (n : ℕ) :
    regularPartitionCount 4 p (p * n + r) ≡ 0 [MOD 2]

/-- For a prime `p ≥ 5` and `r` with `24r + 1` a quadratic nonresidue modulo `p`,
`b_{2,p}(pn + r) ≡ 0 (mod 2)` for all `n ≥ 0`. Here `r ∈ ℕ`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 2 (`jis-2025-25.6.1-thm-2`). -/
public theorem_wanted regularPartitionCount_two_prime_mod_two {p r : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hr : ¬ IsSquare ((24 * r + 1 : ℕ) : ZMod p)) (n : ℕ) :
    regularPartitionCount 2 p (p * n + r) ≡ 0 [MOD 2]

/-- For all `n ≥ 0` and `α ≥ 3`, `b_{4,9}(2^α n + 6 · 2^{α-3} + 1) ≡ 0 (mod 12)`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 3 (`jis-2025-25.6.1-thm-3`). -/
public theorem_wanted regularPartitionCount_four_nine_mod_twelve {α : ℕ} (hα : 3 ≤ α) (n : ℕ) :
    regularPartitionCount 4 9 (2 ^ α * n + 6 * 2 ^ (α - 3) + 1) ≡ 0 [MOD 12]

/-- `f_9 / f_1 = f_12^3 f_18 / (f_2^2 f_6 f_36) + q f_4^2 f_6 f_36 / (f_2^3 f_12)`, stated with
denominators cleared (both sides multiplied by `f_1 f_2^3 f_6 f_12 f_36`).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 7 (`jis-2025-25.6.1-lem-7`). -/
public theorem_wanted f9_div_f1_two_dissection :
    𝔣 9 * 𝔣 2 ^ 3 * 𝔣 6 * 𝔣 12 * 𝔣 36 =
      𝔣 1 * 𝔣 2 * 𝔣 12 ^ 4 * 𝔣 18 + X * 𝔣 1 * 𝔣 4 ^ 2 * 𝔣 6 ^ 2 * 𝔣 36 ^ 2

/-- `f_3 / f_1^3 = f_4^6 f_6^3 / (f_2^9 f_12^2) + 3q f_4^2 f_6 f_12^2 / f_2^7`, stated with
denominators cleared (both sides multiplied by `f_1^3 f_2^9 f_12^2`).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 8 (`jis-2025-25.6.1-lem-8`). -/
public theorem_wanted f3_div_f1_cube_two_dissection :
    𝔣 3 * 𝔣 2 ^ 9 * 𝔣 12 ^ 2 =
      𝔣 1 ^ 3 * 𝔣 4 ^ 6 * 𝔣 6 ^ 3 + 3 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 12 ^ 4

/-- `f_3^2 / f_1^2 = f_4^4 f_6 f_12^2 / (f_2^5 f_8 f_24) + 2q f_4 f_6^2 f_8 f_24 / (f_2^4 f_12)`,
stated with denominators cleared (both sides multiplied by `f_1^2 f_2^5 f_8 f_12 f_24`).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 9 (`jis-2025-25.6.1-lem-9`). -/
public theorem_wanted f3_sq_div_f1_sq_two_dissection :
    𝔣 3 ^ 2 * 𝔣 2 ^ 5 * 𝔣 8 * 𝔣 12 * 𝔣 24 =
      𝔣 1 ^ 2 * 𝔣 4 ^ 4 * 𝔣 6 * 𝔣 12 ^ 3 +
        2 * X * 𝔣 1 ^ 2 * 𝔣 2 * 𝔣 4 * 𝔣 6 ^ 2 * 𝔣 8 ^ 2 * 𝔣 24 ^ 2

/-- The 2-dissections of `1 / f_1^4`, `1 / f_1^8` and `1 / f_1^12`:
`1/f_1^4 = f_4^14/(f_2^14 f_8^4) + 4q f_4^2 f_8^4/f_2^10`,
`1/f_1^8 = f_4^28/(f_2^28 f_8^8) + 8q f_4^16/f_2^24 + 16q^2 f_4^4 f_8^8/f_2^20`,
`1/f_1^12 = f_4^42/(f_2^42 f_8^12) + 12q f_4^30/(f_2^38 f_8^4) + 48q^2 f_4^18 f_8^4/f_2^34
+ 64q^3 f_4^6 f_8^12/f_2^30`, each stated with denominators cleared (multiplied by
`f_1^4 f_2^14 f_8^4`, `f_1^8 f_2^28 f_8^8`, `f_1^12 f_2^42 f_8^12` respectively).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 10 (`jis-2025-25.6.1-lem-10`). -/
public theorem_wanted one_div_f1_pow_four_eight_twelve_two_dissection :
    𝔣 2 ^ 14 * 𝔣 8 ^ 4 = 𝔣 1 ^ 4 * 𝔣 4 ^ 14 + 4 * X * 𝔣 1 ^ 4 * 𝔣 2 ^ 4 * 𝔣 4 ^ 2 * 𝔣 8 ^ 8 ∧
      𝔣 2 ^ 28 * 𝔣 8 ^ 8 =
        𝔣 1 ^ 8 * 𝔣 4 ^ 28 + 8 * X * 𝔣 1 ^ 8 * 𝔣 2 ^ 4 * 𝔣 4 ^ 16 * 𝔣 8 ^ 8 +
          16 * X ^ 2 * 𝔣 1 ^ 8 * 𝔣 2 ^ 8 * 𝔣 4 ^ 4 * 𝔣 8 ^ 16 ∧
      𝔣 2 ^ 42 * 𝔣 8 ^ 12 =
        𝔣 1 ^ 12 * 𝔣 4 ^ 42 + 12 * X * 𝔣 1 ^ 12 * 𝔣 2 ^ 4 * 𝔣 4 ^ 30 * 𝔣 8 ^ 8 +
          48 * X ^ 2 * 𝔣 1 ^ 12 * 𝔣 2 ^ 8 * 𝔣 4 ^ 18 * 𝔣 8 ^ 16 +
          64 * X ^ 3 * 𝔣 1 ^ 12 * 𝔣 2 ^ 12 * 𝔣 4 ^ 6 * 𝔣 8 ^ 24

/-- `1 / (f_1 f_3) = f_8^2 f_12^5 / (f_2^2 f_4 f_6^4 f_24^2) + q f_4^5 f_24^2 / (f_2^4 f_6^2 f_8^2
f_12)`, stated with denominators cleared (both sides multiplied by
`f_1 f_3 f_2^4 f_4 f_6^4 f_8^2 f_12 f_24^2`).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 11 (`jis-2025-25.6.1-lem-11`). -/
public theorem_wanted one_div_f1_f3_two_dissection :
    𝔣 2 ^ 4 * 𝔣 4 * 𝔣 6 ^ 4 * 𝔣 8 ^ 2 * 𝔣 12 * 𝔣 24 ^ 2 =
      𝔣 1 * 𝔣 3 * 𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6 +
        X * 𝔣 1 * 𝔣 3 * 𝔣 4 ^ 6 * 𝔣 6 ^ 2 * 𝔣 24 ^ 4

/-- `∑_{n ≥ 0} b_{4,9}(2n + 1) q^n = f_2^3 f_3 / (f_1^3 f_6)`, stated with denominators
cleared (both sides multiplied by `f_1^3 f_6`).

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 12 (`jis-2025-25.6.1-thm-12`). -/
public theorem_wanted regularPartitionCount_four_nine_odd_generatingFunction :
    𝔣 1 ^ 3 * 𝔣 6 * PowerSeries.mk (fun n => (regularPartitionCount 4 9 (2 * n + 1) : ℤ)) =
      𝔣 2 ^ 3 * 𝔣 3

/-- For all `n ≥ 0`, `b_{4,9}(16n + 1) ≡ b_{4,9}(4n + 1) (mod 4)`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 13 (`jis-2025-25.6.1-thm-13`). -/
public theorem_wanted regularPartitionCount_four_nine_internal_mod_four (n : ℕ) :
    regularPartitionCount 4 9 (16 * n + 1) ≡ regularPartitionCount 4 9 (4 * n + 1) [MOD 4]

/-- For all `n ≥ 0`, `b_{4,9}(16n + 13) ≡ 0 (mod 4)`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 14 (`jis-2025-25.6.1-thm-14`). -/
public theorem_wanted regularPartitionCount_four_nine_sixteen_mul_add_thirteen (n : ℕ) :
    regularPartitionCount 4 9 (16 * n + 13) ≡ 0 [MOD 4]

/-- For all `n ≥ 0`, `b_{4,9}(32n + 25) ≡ 0 (mod 4)`.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 15 (`jis-2025-25.6.1-thm-15`). -/
public theorem_wanted regularPartitionCount_four_nine_thirtyTwo_mul_add_twentyFive (n : ℕ) :
    regularPartitionCount 4 9 (32 * n + 25) ≡ 0 [MOD 4]

end

end MetaMathlibExt
