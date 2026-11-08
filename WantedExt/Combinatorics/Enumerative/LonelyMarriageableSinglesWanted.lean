/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.NoncrossingPartition.Small

/-!
# Lonely singles and marriageable singles partitions (statements)

Statement-only targets from Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to
Crossroads and Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1.

Noncrossing partitions of `[n]` are `NoncrossingPartition n` (partitions of `Fin n`). A
noncrossing partition is a *marriageable singles* partition if two of its singleton blocks can be
merged with the result still noncrossing, and a *lonely singles* partition otherwise; `M_n` and
`L_n` count them.

For the road-intersection statements, a standard road intersection of size `n` has entries
`E_1, …, E_n` and exits `X_1, …, X_n` alternating clockwise on a circle; the lane `E_iX_j` is the
pair `(i, j) : Fin n × Fin n`, and its endpoints sit at the circle positions `2i` (entry) and
`2j + 1` (exit) (zero-based).
-/

namespace MetaMathlibExt

@[expose] public section

open NoncrossingPartition

/-- `x` and `y` lie in one block of the partition obtained from `P` by merging the blocks of
`i` and `j`: either they already share a block, or each lies in the block of `i` or of `j`
(for singleton blocks `{i}`, `{j}` this joins them into `{i, j}`).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3 (the
partition `π'` obtained by joining `{i}` and `{j}`). -/
def mergedSameBlock {n : ℕ} (P : SetPartition n) (i j x y : Fin n) : Prop :=
  P.part x = P.part y ∨ ((x ∈ P.part i ∨ x ∈ P.part j) ∧ (y ∈ P.part i ∨ y ∈ P.part j))

instance {n : ℕ} (P : SetPartition n) (i j x y : Fin n) :
    Decidable (mergedSameBlock P i j x y) := by
  unfold mergedSameBlock
  infer_instance

/-- The partition obtained from `P` by joining the blocks of `i` and `j` has a crossing: there are
`a < b < c < d` with `a, c` in one of its blocks and `b, d` in another.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 2 and 3
(crossing partitions, the partition `π'`). -/
def mergedHasCrossing {n : ℕ} (P : SetPartition n) (i j : Fin n) : Prop :=
  ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧ mergedSameBlock P i j a c ∧
    mergedSameBlock P i j b d ∧ ¬ mergedSameBlock P i j a b

instance {n : ℕ} (P : SetPartition n) (i j : Fin n) : Decidable (mergedHasCrossing P i j) := by
  unfold mergedHasCrossing
  infer_instance

/-- A partition `P` of `[n]` is a marriageable singles partition if it has two distinct singleton
blocks `{i}`, `{j}` such that the partition obtained by joining them into `{i, j}` is
noncrossing.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def IsMarriageableSingles {n : ℕ} (P : SetPartition n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ P.part i = {i} ∧ P.part j = {j} ∧ ¬ mergedHasCrossing P i j

instance {n : ℕ} (P : SetPartition n) : Decidable (IsMarriageableSingles P) := by
  unfold IsMarriageableSingles
  infer_instance

/-- `M_n`, the number of marriageable singles partitions of `[n]`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def marriageableSinglesCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n => IsMarriageableSingles P.val).card

/-- `L_n`, the number of lonely singles partitions of `[n]` (noncrossing partitions that are not
marriageable singles partitions).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def lonelySinglesCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n => ¬ IsMarriageableSingles P.val).card

/-- `M_0 = M_1 = 0`: a marriageable singles partition needs two distinct points.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Table 1. -/
theorem marriageableSinglesCount_of_le_one {n : ℕ} (hn : n ≤ 1) :
    marriageableSinglesCount n = 0 := by
  rw [marriageableSinglesCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro P - ⟨i, j, hij, -⟩
  exact hij (Fin.ext (by omega))

/-- `L_0 = L_1 = 1`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Table 1. -/
theorem lonelySinglesCount_zero_one : lonelySinglesCount 0 = 1 ∧ lonelySinglesCount 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [lonelySinglesCount, Finset.filter_true_of_mem, Finset.card_univ]
    · exact NoncrossingPartition.card_zero
    · rintro P - ⟨i, j, hij, -⟩
      exact hij (Fin.ext (by omega))
  · rw [lonelySinglesCount, Finset.filter_true_of_mem, Finset.card_univ]
    · exact NoncrossingPartition.card_one
    · rintro P - ⟨i, j, hij, -⟩
      exact hij (Fin.ext (by omega))

/-- `NC_{n,m,k}`, the number of noncrossing partitions of `[n]` with `m` blocks of which `k` are
singletons.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 23. -/
def noncrossingBlockSingletonCount (n m k : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n =>
    P.val.parts.card = m ∧ (P.val.parts.filter fun B => B.card = 1).card = k).card

/-- `NC_{0,0,0} = 1`: the empty partition of `[0]` has no blocks.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Remark 25. -/
theorem noncrossingBlockSingletonCount_zero : noncrossingBlockSingletonCount 0 0 0 = 1 := by
  have h : ∀ P : _root_.NoncrossingPartition 0, P.val.parts = ∅ := fun P =>
    Finpartition.parts_eq_empty_iff.mpr (by simp)
  rw [noncrossingBlockSingletonCount, Finset.filter_true_of_mem (fun P _ => by simp [h P]),
    Finset.card_univ]
  exact NoncrossingPartition.card_zero

/-- The binomial coefficient `binom(a, b)` for integers `a`, `b`, taken to be `0` unless
`0 ≤ a` and `0 ≤ b`. This is the convention under which the paper's formulas "give `0`" in the
degenerate cases (for example `binom(-1, 0) = 0` in `NC_{1,1,0}`).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
def zeroExtendedChoose (a b : ℤ) : ℕ :=
  if 0 ≤ a ∧ 0 ≤ b then a.toNat.choose b.toNat else 0

/-- On natural arguments `zeroExtendedChoose` is `Nat.choose`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
theorem zeroExtendedChoose_natCast (a b : ℕ) : zeroExtendedChoose a b = a.choose b := by
  simp [zeroExtendedChoose]

/-- `binom(-1, 0) = 0` under this convention.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
theorem zeroExtendedChoose_neg_one_zero : zeroExtendedChoose (-1) 0 = 0 := by
  simp [zeroExtendedChoose]

/-- Two lanes `E_iX_j = (i, j)` and `E_{i'}X_{j'} = (i', j')` of a standard road intersection
have a common point: they share an entry or an exit, or their chords cross, i.e. exactly one
endpoint of the second chord lies strictly between the endpoints `2i`, `2j + 1` of the first
(all four endpoints being distinct when no entry or exit is shared).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 10 and 13
(lanes, noncrossing lanes). -/
def lanesMeet {n : ℕ} (ℓ ℓ' : Fin n × Fin n) : Prop :=
  ℓ.1 = ℓ'.1 ∨ ℓ.2 = ℓ'.2 ∨
    (let lo := min (2 * ℓ.1.val) (2 * ℓ.2.val + 1)
     let hi := max (2 * ℓ.1.val) (2 * ℓ.2.val + 1)
     ((lo < 2 * ℓ'.1.val ∧ 2 * ℓ'.1.val < hi) ↔ ¬ (lo < 2 * ℓ'.2.val + 1 ∧ 2 * ℓ'.2.val + 1 < hi)))

instance {n : ℕ} (ℓ ℓ' : Fin n × Fin n) : Decidable (lanesMeet ℓ ℓ') := by
  unfold lanesMeet
  infer_instance

/-- `S` is a maximal set of lanes (MSL) among the lanes `allowed`: its lanes pairwise have no
common point, and every other allowed lane meets one of them. The standard road intersection
allows every lane; the restricted one forbids the U-turns `E_iX_i`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 12 and 13
(restricted standard road intersection, MSL). -/
def IsMaximalSetOfLanes {n : ℕ} (allowed S : Finset (Fin n × Fin n)) : Prop :=
  S ⊆ allowed ∧ (∀ ℓ ∈ S, ∀ ℓ' ∈ S, ℓ ≠ ℓ' → ¬ lanesMeet ℓ ℓ') ∧
    ∀ ℓ ∈ allowed, ℓ ∉ S → ∃ ℓ' ∈ S, lanesMeet ℓ ℓ'

instance {n : ℕ} (allowed S : Finset (Fin n × Fin n)) :
    Decidable (IsMaximalSetOfLanes allowed S) := by
  unfold IsMaximalSetOfLanes
  infer_instance

/-- An MSL of the standard road intersection is absolute when it has no two U-turns `E_iX_i`,
`E_jX_j` (`i ≠ j`) whose replacement by `E_iX_j` and `E_jX_i` gives another MSL.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 15. -/
def IsAbsoluteMaximalSetOfLanes {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  IsMaximalSetOfLanes Finset.univ S ∧
    ¬ ∃ i j : Fin n, i ≠ j ∧ (i, i) ∈ S ∧ (j, j) ∈ S ∧
      IsMaximalSetOfLanes Finset.univ (insert (i, j) (insert (j, i) ((S.erase (i, i)).erase (j, j))))

instance {n : ℕ} (S : Finset (Fin n × Fin n)) : Decidable (IsAbsoluteMaximalSetOfLanes S) := by
  unfold IsAbsoluteMaximalSetOfLanes
  infer_instance

/-- The standard road intersection of size `2` has the two MSL `{E₁X₁, E₂X₂}` and
`{E₁X₂, E₂X₁}`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 13 (MSL). -/
theorem maximalSetsOfLanes_two :
    (Finset.univ.filter fun S : Finset (Fin 2 × Fin 2) => IsMaximalSetOfLanes Finset.univ S) =
      {{(0, 0), (1, 1)}, {(0, 1), (1, 0)}} := by
  decide

/-! ## Statements -/

/-- The number `C_n` of noncrossing partitions of `[n]` is `L_n + M_n`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Lemma 6
(`jis-2025-25.1.1-lem-6`). -/
public theorem_wanted card_noncrossingPartition_eq_lonely_add_marriageable (n : ℕ) :
    Fintype.card (_root_.NoncrossingPartition n) =
      lonelySinglesCount n + marriageableSinglesCount n

/-- The MSL of a standard road intersection of size `n` are in bijection with the noncrossing
partitions of `[n]`, and there are `C_n` (the Catalan number) of them.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Lemma 16
(`jis-2025-25.1.1-lem-16`). -/
public theorem_wanted maximalSetsOfLanes_equiv_noncrossingPartition (n : ℕ) :
    Nonempty ({S : Finset (Fin n × Fin n) // IsMaximalSetOfLanes Finset.univ S} ≃
      _root_.NoncrossingPartition n) ∧
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes Finset.univ S).card = catalan n

/-- The number of nonabsolute MSL of a standard road intersection of size `n` is `M_n`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 17
(`jis-2025-25.1.1-cor-17`). -/
public theorem_wanted card_nonabsolute_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes Finset.univ S ∧ ¬ IsAbsoluteMaximalSetOfLanes S).card =
      marriageableSinglesCount n

/-- The number of absolute MSL of a standard road intersection of size `n` is `L_n`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 18
(`jis-2025-25.1.1-cor-18`). -/
public theorem_wanted card_absolute_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) => IsAbsoluteMaximalSetOfLanes S).card =
      lonelySinglesCount n

/-- The number of MSL of a restricted standard road intersection of size `n` (U-turns `E_iX_i`
forbidden) is `L_n`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 19
(`jis-2025-25.1.1-cor-19`). -/
public theorem_wanted card_restricted_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes (Finset.univ.filter fun ℓ : Fin n × Fin n => ℓ.1 ≠ ℓ.2) S).card =
      lonelySinglesCount n

/-- `L_n < L_{n+1}` for `n ≥ 2` and `M_n < M_{n+1}` for `n ≥ 3`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 20
(`jis-2025-25.1.1-prop-20`). -/
public theorem_wanted lonely_marriageable_strictMono :
    (∀ n, 2 ≤ n → lonelySinglesCount n < lonelySinglesCount (n + 1)) ∧
    ∀ n, 3 ≤ n → marriageableSinglesCount n < marriageableSinglesCount (n + 1)

/-- `M_n → ∞` and `L_n → ∞`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 21
(`jis-2025-25.1.1-cor-21`). -/
public theorem_wanted tendsto_marriageable_lonely_atTop :
    Filter.Tendsto marriageableSinglesCount Filter.atTop Filter.atTop ∧
      Filter.Tendsto lonelySinglesCount Filter.atTop Filter.atTop

/-- `C_n + 3M_n ≤ M_{n+2}` for every `n ≥ 0`, with `C_n` the number of noncrossing partitions of
`[n]`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 22
(`jis-2025-25.1.1-prop-22`). -/
public theorem_wanted card_add_three_mul_marriageable_le (n : ℕ) :
    Fintype.card (_root_.NoncrossingPartition n) + 3 * marriageableSinglesCount n ≤
      marriageableSinglesCount (n + 2)

/-- For `(n, m) ≠ (0, 0)`, `NC_{n,m,0} = binom(n, m) binom(n-m-1, m-1) / (n-m+1)`, and for
`(n, m) ≠ (1, 1)`, `NC_{n,m,1} = binom(n, m-1) binom(n-m-1, m-2)`; binomials with a negative
argument are `0` (`zeroExtendedChoose`), and the quotient is in `ℚ` (where `1/0 = 0`; the
denominator vanishes only for `m = n + 1`, where `binom(n, m) = 0`).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 24
(`jis-2025-25.1.1-prop-24`). -/
public theorem_wanted noncrossingBlockSingletonCount_formulas (n m : ℕ) :
    ((n, m) ≠ (0, 0) →
      (noncrossingBlockSingletonCount n m 0 : ℚ) =
        1 / ((n : ℚ) - m + 1) * zeroExtendedChoose n m *
          zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 1)) ∧
    ((n, m) ≠ (1, 1) →
      noncrossingBlockSingletonCount n m 1 =
        zeroExtendedChoose n ((m : ℤ) - 1) * zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 2))

/-- For `n ≥ 2`, `L_n` is at least the number of noncrossing partitions with at most one
singleton block, written with the formulas of Proposition 24:
`L_n ≥ ∑_{m=1}^{⌊n/2⌋} binom(n, m) binom(n-m-1, m-1)/(n-m+1)
  + ∑_{m=2}^{⌊(n+1)/2⌋} binom(n, m-1) binom(n-m-1, m-2)`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 26
(`jis-2025-25.1.1-prop-26`). -/
public theorem_wanted lonelySinglesCount_ge_sum (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.Icc 1 (n / 2), 1 / ((n : ℚ) - m + 1) * zeroExtendedChoose n m *
        zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 1)) +
      (∑ m ∈ Finset.Icc 2 ((n + 1) / 2),
        (zeroExtendedChoose n ((m : ℤ) - 1) * zeroExtendedChoose ((n : ℤ) - m - 1) ((m : ℤ) - 2) :
          ℚ)) ≤
      lonelySinglesCount n

/-- For `n ≥ 3`, `M_n` is at least the double sum over `1 ≤ i < j ≤ n` of the products of the
singleton-free counts (via Proposition 24) for `[n+i-j-1]` and `[j-i-1]`:
`M_n ≥ ∑_{i=1}^{n-1} ∑_{j=i+1}^{n}
  (∑_{m=0}^{⌊(n+i-j-1)/2⌋} binom(n+i-j-1, m) binom(n+i-j-m-2, m-1)/(n+i-j-m))
  (∑_{m=0}^{⌊(j-i-1)/2⌋} binom(j-i-1, m) binom(j-i-m-2, m-1)/(j-i-m))`,
binomials with a negative argument being `0`.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 27
(`jis-2025-25.1.1-prop-27`). -/
public theorem_wanted marriageableSinglesCount_ge_sum (n : ℕ) (hn : 3 ≤ n) :
    (∑ i ∈ Finset.Icc 1 (n - 1), ∑ j ∈ Finset.Icc (i + 1) n,
      (∑ m ∈ Finset.range ((n + i - j - 1) / 2 + 1),
          1 / ((n : ℚ) + i - j - m) * zeroExtendedChoose ((n : ℤ) + i - j - 1) m *
            zeroExtendedChoose ((n : ℤ) + i - j - m - 2) ((m : ℤ) - 1)) *
        (∑ m ∈ Finset.range ((j - i - 1) / 2 + 1),
          1 / ((j : ℚ) - i - m) * zeroExtendedChoose ((j : ℤ) - i - 1) m *
            zeroExtendedChoose ((j : ℤ) - i - m - 2) ((m : ℤ) - 1))) ≤
      marriageableSinglesCount n

end

end MetaMathlibExt
