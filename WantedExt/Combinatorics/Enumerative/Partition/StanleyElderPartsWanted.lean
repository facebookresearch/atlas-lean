/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat

/-!
# Stanley's and Elder's theorems on parts of partitions

The two classical results quoted in the introduction of Shruti Sharma and Amandeep Kaur,
*Enumerating Parts of n-Color Partitions*, INTEGERS 25 (2025), Article A94, and the paper's
`n`-color divisor-sum corollaries whose objects the records define (the rest are listed as
blocked in the audit table).

The paper's generating-function theorems (Theorems 3-12, stated "for `|q| < 1`") are stated as
identities of formal power series in `ℚ⟦X⟧`, with `q = X`, infinite sums and products taken in
the coefficientwise (`PowerSeries.WithPiTopology`) topology and `(1 ∓ q^k)⁻¹` the power-series
inverse.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- Elder's theorem: for `k ≥ 1`, the total number of appearances of the part `k` in the
partitions of `n` equals the number of distinct parts appearing at least `k` times in a
partition of `n`, summed over all partitions of `n`. The hypothesis `k ≥ 1` (parts are
positive) is needed: for `k = 0`, `n = 1` the left side is `0` and the right side `1`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 2 (Elder's theorem). -/
public theorem_wanted sum_count_eq_sum_card_parts_count_ge (n k : ℕ) (hk : 1 ≤ k) :
    ∑ p : Nat.Partition n, p.parts.count k =
      ∑ p : Nat.Partition n, (p.parts.toFinset.filter fun i => k ≤ p.parts.count i).card

/-- Stanley's theorem: the total number of `1`s in the partitions of `n` equals the number of
distinct parts of a partition of `n`, summed over all partitions of `n`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 1 (Stanley's theorem). -/
public theorem_wanted sum_count_one_eq_sum_card_toFinset (n : ℕ) :
    ∑ p : Nat.Partition n, p.parts.count 1 = ∑ p : Nat.Partition n, p.parts.toFinset.card


/-! ### `n`-color partitions

An `n`-color partition (Agarwal and Andrews) of `m` is a partition of `m` in which a part of
size `k` comes in `k` colors `k_1, …, k_k`. It is encoded as a multiset of colored parts
`(k, j)` with `1 ≤ j ≤ k`, whose sizes `k` sum to `m`; "distinct" means no colored part
repeats, "odd parts" means every size `k` is odd, and the number of parts counts colored parts
with multiplicity. -/

/-- The colored parts `k_j` (pairs `(k, j)` with `1 ≤ j ≤ k ≤ m`) of size at most `m`, listed
in the order `1_1, 2_1, 2_2, 3_1, …`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public def nColorPartsUpTo (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun k => (List.range (k + 1)).map fun j => (k + 1, j + 1)

/-- Membership in `nColorPartsUpTo m`: `(k, j)` is listed exactly when `1 ≤ j ≤ k ≤ m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public theorem mem_nColorPartsUpTo (m : ℕ) (x : ℕ × ℕ) :
    x ∈ nColorPartsUpTo m ↔ 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ x.1 ≤ m := by
  obtain ⟨k, j⟩ := x
  simp only [nColorPartsUpTo, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨k - 1, by omega, j - 1, by omega, by omega, by omega⟩

/-- The multisets of colored parts drawn from the list `L` whose sizes sum to `n`, generated
part by part (choose how many copies of the head, then recurse on the tail), so only multisets
of the right total are built.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; helper for `C(m)`). -/
public def multisetsWithSizeSum : List (ℕ × ℕ) → ℕ → Finset (Multiset (ℕ × ℕ))
  | [], n => if n = 0 then {0} else ∅
  | c :: cs, n => (Finset.range (n + 1)).biUnion fun i =>
      if i * c.1 ≤ n then
        (multisetsWithSizeSum cs (n - i * c.1)).image (Multiset.replicate i c + ·)
      else ∅

/-- Membership in `multisetsWithSizeSum L n` when every listed part has positive size: the
multisets whose elements all lie in `L` and whose sizes sum to `n`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; helper for `C(m)`). -/
public theorem mem_multisetsWithSizeSum (L : List (ℕ × ℕ)) (hL : ∀ c ∈ L, 1 ≤ c.1) (n : ℕ)
    (s : Multiset (ℕ × ℕ)) :
    s ∈ multisetsWithSizeSum L n ↔ (∀ x ∈ s, x ∈ L) ∧ (s.map Prod.fst).sum = n := by
  induction L generalizing n s with
  | nil =>
    simp only [multisetsWithSizeSum, List.not_mem_nil, imp_false]
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact Multiset.eq_zero_iff_forall_notMem.mpr h
    · simp only [hn, ite_false, Finset.notMem_empty, false_iff, not_and]
      intro h
      rw [Multiset.eq_zero_iff_forall_notMem.mpr h]
      simpa using Ne.symm hn
  | cons c cs ih =>
    have hc : 1 ≤ c.1 := hL c (by simp)
    have hcs : ∀ d ∈ cs, 1 ≤ d.1 := fun d hd => hL d (by simp [hd])
    simp only [multisetsWithSizeSum, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, -, hs⟩
      split_ifs at hs with hi
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨htm, hts⟩ := (ih hcs _ t).mp ht
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases Multiset.mem_add.mp hx with hx | hx
          · simp [Multiset.eq_of_mem_replicate hx]
          · simp [htm x hx]
        · simp [Multiset.map_replicate, Multiset.sum_replicate, hts]
          omega
      · simp at hs
    · rintro ⟨hmem, hsum⟩
      set i := s.count c
      set t := s.filter (· ≠ c)
      have hsplit : s = Multiset.replicate i c + t := by
        rw [← Multiset.filter_add_not (· = c) s, Multiset.filter_eq' s c]
      have hsum' : i * c.1 + (t.map Prod.fst).sum = n := by
        rw [← hsum]; conv_rhs => rw [hsplit]
        simp [Multiset.map_replicate, Multiset.sum_replicate]
      have htmem : ∀ x ∈ t, x ∈ cs := by
        intro x hx
        obtain ⟨hxs, hxc⟩ := Multiset.mem_filter.mp hx
        rcases List.mem_cons.mp (hmem x hxs) with h | h
        · exact absurd h hxc
        · exact h
      refine ⟨i, ?_, ?_⟩
      · have : i ≤ i * c.1 := Nat.le_mul_of_pos_right i hc
        omega
      · split_ifs with hi
        · exact Finset.mem_image.mpr ⟨t, (ih hcs _ t).mpr ⟨htmem, by omega⟩, hsplit.symm⟩
        · omega

/-- The `n`-color partitions of `m`: multisets of colored parts `(k, j)`, `1 ≤ j ≤ k`, whose
sizes sum to `m` (see `mem_nColorPartitions`).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions; `C(m)` is their number). -/
public def nColorPartitions (m : ℕ) : Finset (Multiset (ℕ × ℕ)) :=
  multisetsWithSizeSum (nColorPartsUpTo m) m

/-- Membership in `nColorPartitions m`: every colored part `(k, j)` has `1 ≤ j ≤ k`, and the
sizes `k` sum to `m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`n`-color partitions). -/
public theorem mem_nColorPartitions (m : ℕ) (s : Multiset (ℕ × ℕ)) :
    s ∈ nColorPartitions m ↔ (∀ x ∈ s, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧ (s.map Prod.fst).sum = m := by
  rw [nColorPartitions, mem_multisetsWithSizeSum _ (fun c hc => by
    have := (mem_nColorPartsUpTo m c).mp hc; omega)]
  simp only [mem_nColorPartsUpTo]
  constructor
  · rintro ⟨h, hs⟩; exact ⟨fun x hx => ⟨(h x hx).1, (h x hx).2.1⟩, hs⟩
  · rintro ⟨h, hs⟩
    refine ⟨fun x hx => ⟨(h x hx).1, (h x hx).2, ?_⟩, hs⟩
    rw [← hs]
    exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hx)

/-- Characteristic values: `C(0) = C(1) = 1`, `C(2) = 3` (`2_1`, `2_2`, `1_1 + 1_1`),
`C(3) = 6`, and the `n`-color partitions of `2` listed explicitly.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Section 1 (`C(m)`, generating function
`∏_{m ≥ 1} (1 - q^m)^{-m}`). -/
public theorem nColorPartitions_card_small :
    (nColorPartitions 0).card = 1 ∧ (nColorPartitions 1).card = 1 ∧
      (nColorPartitions 2).card = 3 ∧ (nColorPartitions 3).card = 6 ∧
      nColorPartitions 2 = {{(1, 1), (1, 1)}, {(2, 1)}, {(2, 2)}} := by
  decide +kernel

/-- The sum of the odd divisors of `k` (`σ_odd`).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollaries 2, 4, 7, 10, 12 (`σ_odd`). -/
public def sigmaOdd (k : ℕ) : ℕ := ∑ d ∈ k.divisors.filter Odd, d

/-- The sum of the even divisors of `k` (`σ_even`).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`σ_even`). -/
public def sigmaEven (k : ℕ) : ℕ := ∑ d ∈ k.divisors.filter Even, d

/-- Characteristic values: `σ_odd(12) = 1 + 3 = 4`, `σ_even(12) = 2 + 4 + 6 + 12 = 24`,
`σ_odd(9) = 13`, `σ_even(9) = 0`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollaries 3 and 4. -/
public theorem sigmaOdd_sigmaEven_small :
    sigmaOdd 12 = 4 ∧ sigmaEven 12 = 24 ∧ sigmaOdd 9 = 13 ∧ sigmaEven 9 = 0 := by
  decide

/-- Corollary 1: for `m ≥ 1`, `T_o(m) + T_e(m) = ∑_{k=1}^{m} σ(k) C(m-k)`, where `T_o(m)`
(resp. `T_e(m)`) is the total number of parts over the `n`-color partitions of `m` with an odd
(resp. even) number of parts, `C(m)` the number of `n`-color partitions of `m`, and `σ` the
divisor sum.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 1 (`integers-2025-A94-cor-1`). -/
public theorem_wanted nColor_totalParts_eq_sum_sigma (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, ArithmeticFunction.sigma 1 k * (nColorPartitions (m - k)).card

/-- Corollary 2: for `m ≥ 1`, `σ_odd(m) = ∑_{k=1}^{m} (T_o(k) - T_e(k)) C(D, m-k)`, with
`T_o`, `T_e` as in Corollary 1 and `C(D, m)` the number of `n`-color partitions of `m` into
distinct parts.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 2 (`integers-2025-A94-cor-2`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_partsDiff_mul_distinct (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => Even s.card), s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- Corollary 3: for `m ≥ 1`, `A_e(m) = ∑_{k=1}^{m} σ_even(k) C(m-k)`, where `A_e(m)` is the
total number of even parts over the `n`-color partitions of `m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 3 (`integers-2025-A94-cor-3`). -/
public theorem_wanted nColor_evenParts_eq_sum_sigmaEven (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Even p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaEven k * (nColorPartitions (m - k)).card

/-- Corollary 4: for `m ≥ 1`, `A_o(m) = ∑_{k=1}^{m} σ_odd(k) C(m-k)`, where `A_o(m)` is the
total number of odd parts over the `n`-color partitions of `m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 4 (`integers-2025-A94-cor-4`). -/
public theorem_wanted nColor_oddParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => Odd p.1).card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * (nColorPartitions (m - k)).card

/-- Corollary 5: for `m ≥ t ≥ 1`, `N^t(m) = ∑_{k=1}^{⌊m/t⌋} k C(m - tk)`, where `N^t(m)` is
the number of distinct colored parts with multiplicity at least `t`, summed over the `n`-color
partitions of `m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 5 (`integers-2025-A94-cor-5`). -/
public theorem_wanted nColor_partsMultiplicityGe_eq_sum (m t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) :
    ∑ s ∈ nColorPartitions m, (s.toFinset.filter fun p => t ≤ s.count p).card =
      ∑ k ∈ Finset.Icc 1 (m / t), k * (nColorPartitions (m - t * k)).card

/-- Corollary 6: for `m ≥ 1`, `r ≥ 1` and `0 < k < r`,
`C(k mod r, m) = ∑_{j=1}^{m} (∑_{rd+k ∣ j} (rd+k)) C(m-j)`, where `C(k mod r, m)` is the
total number of parts of size `≡ k (mod r)` over the `n`-color partitions of `m`; the inner sum
runs over the divisors of `j` that are `≡ k (mod r)`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 6 (`integers-2025-A94-cor-6`). -/
public theorem_wanted nColor_partsModEq_eq_sum (m r k : ℕ) (hm : 1 ≤ m) (hk : 0 < k)
    (hkr : k < r) :
    ∑ s ∈ nColorPartitions m, (s.filter fun p => p.1 % r = k).card =
      ∑ j ∈ Finset.Icc 1 m,
        (∑ d ∈ j.divisors.filter (fun d => d % r = k), d) * (nColorPartitions (m - j)).card

/-- Corollary 7: for `m ≥ 1`, `C_o(D, m) + C_e(D, m) = ∑_{k=1}^{m} σ_odd(k) C(D, m-k)`, where
`C_o(D, m)` (resp. `C_e(D, m)`) is the total number of parts over the `n`-color partitions of
`m` into an odd (resp. even) number of distinct parts, and `C(D, m)` the number of `n`-color
partitions of `m` into distinct parts.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 7 (`integers-2025-A94-cor-7`). -/
public theorem_wanted nColor_distinctTotalParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => s.Nodup ∧ Even s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m, sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => s.Nodup).card

/-- Corollary 8: for `m ≥ 1`, `σ(m) = ∑_{k=1}^{m} (C_o(D, k) - C_e(D, k)) C(m-k)`, with
`C_o(D, ·)`, `C_e(D, ·)` as in Corollary 7.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 8 (`integers-2025-A94-cor-8`). -/
public theorem_wanted sigma_eq_sum_nColor_distinctPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (ArithmeticFunction.sigma 1 m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) :
              ℤ)) *
          (nColorPartitions (m - k)).card

/-- Corollary 10: for `m ≥ 1`, `Q(O, m) = ∑_{k=1}^{m} σ_odd(k) C(O, m-k)`, where `Q(O, m)` is
the total number of parts over the `n`-color partitions of `m` into odd parts and `C(O, m)` the
number of such partitions.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 10 (`integers-2025-A94-cor-10`). -/
public theorem_wanted nColor_oddPartitionParts_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    ∑ s ∈ (nColorPartitions m).filter (fun s => ∀ p ∈ s, Odd p.1), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card

/-- Corollary 12: for `m ≥ 1`, `U_o(m) + U_e(m) = ∑_{k=1}^{m} σ_odd(k) C(O, m-k)`, where
`U_o(m) + U_e(m)` is the total number of parts over the `n`-color partitions of `m` into odd
parts, split by the parity of the number of parts, and `C(O, m)` as in Corollary 10.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 12 (`integers-2025-A94-cor-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_eq_sum_sigmaOdd (m : ℕ) (hm : 1 ≤ m) :
    (∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card) +
        ∑ s ∈ (nColorPartitions m).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card =
      ∑ k ∈ Finset.Icc 1 m,
        sigmaOdd k * ((nColorPartitions (m - k)).filter fun s => ∀ p ∈ s, Odd p.1).card


/-- Theorem 3: with `T_o(m)` (resp. `T_e(m)`) the total number of parts over the `n`-color
partitions of `m` with an odd (resp. even) number of parts,
`∑_{m ≥ 1} m q^m / (1 ∓ q^m) = ∏_{m ≥ 1} (1 ∓ q^m)^m ∑_{m ≥ 1} (T_o(m) ± T_e(m)) q^m`; both
sign choices, as a conjunction (upper signs first).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 3 (`integers-2025-A94-thm-3`). -/
public theorem_wanted nColor_totalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => Even s.card), s.card : ℕ) : ℚ)

/-- Theorem 4: with `A_e(m)` the total number of even parts over the `n`-color partitions of `m`,
`∑_{m ≥ 1} 2m q^{2m} / (1 - q^{2m}) = ∏_{m ≥ 1} (1 - q^m)^m ∑_{m ≥ 1} A_e(m) q^m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 4 (`integers-2025-A94-thm-4`). -/
public theorem_wanted nColor_evenParts_generatingFunction :
    ∑' m : ℕ, ((2 * (m + 1) : ℕ) : ℚ⟦X⟧) * X ^ (2 * (m + 1)) * (1 - X ^ (2 * (m + 1)))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n => ((∑ s ∈ nColorPartitions n, (s.filter fun p => Even p.1).card : ℕ) : ℚ)

/-- Theorem 5: with `A_o(m)` the total number of odd parts over the `n`-color partitions of `m`,
`∑_{m ≥ 1} (2m-1) q^{2m-1} / (1 - q^{2m-1}) = ∏_{m ≥ 1} (1 - q^m)^m ∑_{m ≥ 1} A_o(m) q^m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 5 (`integers-2025-A94-thm-5`). -/
public theorem_wanted nColor_oddParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n => ((∑ s ∈ nColorPartitions n, (s.filter fun p => Odd p.1).card : ℕ) : ℚ)

/-- Theorem 6: for `t ≥ 1`, with `N^t(m)` the number of distinct colored parts of multiplicity at
least `t`, summed over the `n`-color partitions of `m`,
`∑_{m ≥ 1} m q^{mt} = ∏_{m ≥ 1} (1 - q^m)^m ∑_{m ≥ 1} N^t(m) q^m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 6 (`integers-2025-A94-thm-6`). -/
public theorem_wanted nColor_partsMultiplicityGe_generatingFunction (t : ℕ) (ht : 1 ≤ t) :
    ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ ((m + 1) * t) =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.toFinset.filter fun p => t ≤ s.count p).card : ℕ) : ℚ)

/-- Theorem 7: for `0 < k < r`, with `C(k mod r, m)` the total number of parts of size `≡ k (mod r)`
over the `n`-color partitions of `m`,
`∑_{m ≥ 0} (rm+k) q^{rm+k} / (1 - q^{rm+k}) = ∏_{m ≥ 1} (1 - q^m)^m ∑_{m ≥ 1} C(k mod r, m) q^m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 7 (`integers-2025-A94-thm-7`). -/
public theorem_wanted nColor_partsModEq_generatingFunction (r k : ℕ) (hk : 0 < k) (hkr : k < r) :
    ∑' m : ℕ, ((r * m + k : ℕ) : ℚ⟦X⟧) * X ^ (r * m + k) * (1 - X ^ (r * m + k))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ nColorPartitions n, (s.filter fun p => p.1 % r = k).card : ℕ) : ℚ)

/-- Theorem 8: with `C_o(D, m)` (resp. `C_e(D, m)`) the total number of parts over the `n`-color
partitions of `m` into an odd (resp. even) number of distinct colored parts,
`∑_{m ≥ 1} m q^m / (1 ± q^m) = (∏_{m ≥ 1} (1 ± q^m)^m)⁻¹ ∑_{m ≥ 1} (C_o(D, m) ± C_e(D, m)) q^m`;
both sign choices, as a conjunction (upper signs first).

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 8 (`integers-2025-A94-thm-8`). -/
public theorem_wanted nColor_distinctTotalParts_generatingFunction :
    (∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 + X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) +
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (m + 1) * (1 - X ^ (m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (m + 1)) ^ (m + 1) : ℚ⟦X⟧)⁻¹ *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Odd s.card), s.card : ℕ) : ℚ) -
              ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℚ)

/-- Corollary 9, in the reading given by the paper's derivation from Theorem 8 and Eq. (3):
for `m ≥ 1`, `σ_odd(m) = ∑_{k=1}^{m} (C_o(D, k) + C_e(D, k)) C_{e-o}(m-k)`, where
`C_{e-o}(n) = ∑ (-1)^{#parts}` over the `n`-color partitions of `n`. As printed, with the number
`C(D, k)` of distinct `n`-color partitions in place of `C_o(D, k) + C_e(D, k)`, it fails at
`m = 3`: `σ_odd(3) = 4` but `∑_{k=1}^{3} C(D, k) C_{e-o}(3-k) = 1·(-1) + 2·(-1) + 5·1 = 2`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 9 (`integers-2025-A94-cor-9`). -/
public theorem_wanted sigmaOdd_eq_sum_nColor_distinctTotalParts_mul_signed (m : ℕ) (hm : 1 ≤ m) :
    (sigmaOdd m : ℤ) =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Odd s.card), s.card) +
            ∑ s ∈ (nColorPartitions k).filter (fun s => s.Nodup ∧ Even s.card), s.card : ℕ) : ℤ) *
          ∑ s ∈ nColorPartitions (m - k), (-1 : ℤ) ^ s.card

/-- Theorem 9: with `Q(O, m)` the total number of parts over the `n`-color partitions of `m` into
odd parts,
`∑_{m ≥ 1} (2m-1) q^{2m-1} / (1 - q^{2m-1}) = ∏_{m ≥ 1} (1 - q^{2m-1})^{2m-1} ∑_{m ≥ 1} Q(O, m) q^m`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 9 (`integers-2025-A94-thm-9`). -/
public theorem_wanted nColor_oddPartitionParts_generatingFunction :
    ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
      (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
        PowerSeries.mk fun n =>
          ((∑ s ∈ (nColorPartitions n).filter (fun s => ∀ p ∈ s, Odd p.1), s.card : ℕ) : ℚ)

/-- Theorem 11: for every `j`, with `Q(D, j, m)` the total number of parts of size `j` (any color)
over the `n`-color partitions of `m` into distinct colored parts and `C(D, m)` the number of such
partitions, `∑_{m ≥ 1} Q(D, j, m) q^m = j q^j / (1 + q^j) ∑_{m ≥ 0} C(D, m) q^m`. The paper
assumes `j ≥ 1`; for `j = 0` both sides vanish.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 11 (`integers-2025-A94-thm-11`). -/
public theorem_wanted nColor_distinctPartsCountOf_generatingFunction (j : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ s ∈ (nColorPartitions n).filter (fun s => s.Nodup), (s.filter fun p => p.1 = j).card :
          ℕ) : ℚ)) =
      (j : ℚ⟦X⟧) * X ^ j * (1 + X ^ j)⁻¹ *
        PowerSeries.mk fun n => (((nColorPartitions n).filter fun s => s.Nodup).card : ℚ)

/-- Theorem 12, with `U_o(m)` (resp. `U_e(m)`) the total number of parts over the `n`-color
partitions of `m` into odd parts having an odd (resp. even) number of parts, the convention of
`T_o`, `T_e` (Theorem 3) and `C_o(D, ·)`, `C_e(D, ·)` (Theorem 8):
`∑_{m ≥ 1} (2m-1) q^{2m-1} / (1 ∓ q^{2m-1}) = ∏_{m ≥ 1} (1 ∓ q^{2m-1})^{2m-1} ∑_{m ≥ 1} (U_o(m) ± U_e(m)) q^m`;
both sign choices, as a conjunction (upper signs first). The printed definition swaps the
subscripts (`U_e` for an odd number of parts); with it the lower-sign identity fails at `q^1`:
the left side has coefficient `1`, the right side `U_o(1) - U_e(1) = 0 - 1 = -1`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Theorem 12 (`integers-2025-A94-thm-12`). -/
public theorem_wanted nColor_oddPartitionParts_byParity_generatingFunction :
    (∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 - X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 - X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) +
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card :
              ℕ) : ℚ)) ∧
      ∑' m : ℕ, ((2 * m + 1 : ℕ) : ℚ⟦X⟧) * X ^ (2 * m + 1) * (1 + X ^ (2 * m + 1))⁻¹ =
        (∏' m : ℕ, (1 + X ^ (2 * m + 1)) ^ (2 * m + 1) : ℚ⟦X⟧) *
          PowerSeries.mk fun n =>
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℚ) -
            ((∑ s ∈ (nColorPartitions n).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card), s.card :
              ℕ) : ℚ)

/-- Corollary 13: for `m ≥ 1`,
`(-1)^{m+1} σ_odd(m) = ∑_{k=1}^{m} (U_o(k) - U_e(k)) C(O, D, m-k)`, with `U_o`, `U_e` as in
`nColor_oddPartitionParts_byParity_generatingFunction` (subscript = parity of the number of
parts) and `C(O, D, m)` the number of `n`-color partitions of `m` into distinct odd colored parts.
With the printed (swapped) definition of `U_o`, `U_e` it fails at `m = 1`: `1` vs `(0 - 1)·1 = -1`.

Source: Shruti Sharma and Amandeep Kaur, *Enumerating Parts of n-Color Partitions*,
INTEGERS 25 (2025), Article A94, Corollary 13 (`integers-2025-A94-cor-13`). -/
public theorem_wanted neg_one_pow_mul_sigmaOdd_eq_sum_nColor_oddPartsDiff (m : ℕ) (hm : 1 ≤ m) :
    (-1 : ℤ) ^ (m + 1) * sigmaOdd m =
      ∑ k ∈ Finset.Icc 1 m,
        (((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Odd s.card), s.card :
              ℕ) : ℤ) -
            ((∑ s ∈ (nColorPartitions k).filter (fun s => (∀ p ∈ s, Odd p.1) ∧ Even s.card),
              s.card : ℕ) : ℤ)) *
          ((nColorPartitions (m - k)).filter fun s => s.Nodup ∧ ∀ p ∈ s, Odd p.1).card

end

end MetaMathlibExt
