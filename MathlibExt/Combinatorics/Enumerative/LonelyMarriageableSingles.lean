/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Prod
public import MathlibExt.Combinatorics.NoncrossingPartition.Small

/-!
# Lonely and marriageable singles partitions

The number of noncrossing partitions of `Fin n` is the sum of the lonely and marriageable
singles counts. The marriageable partitions have two singleton blocks that can be merged
without creating a crossing.

The module also defines the block and singleton counts and the lane configurations used by
Rouyer and Ninet in *Two New Integer Sequences Related to Crossroads and Catalan Numbers*.
-/

namespace MetaMathlibExt

@[expose] public section

open NoncrossingPartition

/-- **Same block after merging two blocks.** Let $P$ be a set partition of $\{0, \dots, n-1\}$ and
let $i, j, x, y \in \{0, \dots, n-1\}$. Then $x$ and $y$ lie in the same block after merging the
blocks of $i$ and $j$ if either $x$ and $y$ lie in the same block of $P$, or each of $x$ and $y$
lies in the block of $i$ or in the block of $j$. For singleton blocks $\{i\}$ and $\{j\}$ this
joins them into the block $\{i, j\}$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3 (the
partition `π'` obtained by joining `{i}` and `{j}`). -/
def mergedSameBlock {n : ℕ} (P : SetPartition n) (i j x y : Fin n) : Prop :=
  P.part x = P.part y ∨ ((x ∈ P.part i ∨ x ∈ P.part j) ∧ (y ∈ P.part i ∨ y ∈ P.part j))

instance instDecidableMergedSameBlock {n : ℕ} (P : SetPartition n) (i j x y : Fin n) :
    Decidable (mergedSameBlock P i j x y) := by
  unfold mergedSameBlock
  infer_instance

/-- **Crossing after merging two blocks.** Let $P$ be a set partition of $\{0, \dots, n-1\}$ and
let $i, j \in \{0, \dots, n-1\}$. The partition obtained from $P$ by merging the blocks of $i$ and
$j$ has a crossing if there are $a < b < c < d$ in $\{0, \dots, n-1\}$ such that $a$ and $c$ lie
in one of its blocks and $b$ and $d$ lie in a different one of its blocks.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 2 and 3
(crossing partitions, the partition `π'`). -/
def mergedHasCrossing {n : ℕ} (P : SetPartition n) (i j : Fin n) : Prop :=
  ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧ mergedSameBlock P i j a c ∧
    mergedSameBlock P i j b d ∧ ¬ mergedSameBlock P i j a b

instance instDecidableMergedHasCrossing {n : ℕ} (P : SetPartition n) (i j : Fin n) :
    Decidable (mergedHasCrossing P i j) := by
  unfold mergedHasCrossing
  infer_instance

/-- **Marriageable singles partition.** A set partition $P$ of $\{0, \dots, n-1\}$ is a
marriageable singles partition if it has two distinct singleton blocks $\{i\}$ and $\{j\}$ such
that the partition obtained from $P$ by joining them into the block $\{i, j\}$ has no crossing.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def IsMarriageableSingles {n : ℕ} (P : SetPartition n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ P.part i = {i} ∧ P.part j = {j} ∧ ¬ mergedHasCrossing P i j

instance instDecidableIsMarriageableSingles {n : ℕ} (P : SetPartition n) :
    Decidable (IsMarriageableSingles P) := by
  unfold IsMarriageableSingles
  infer_instance

/-- **Number of marriageable singles partitions.** For $n \ge 0$, $M_n$ is the number of
noncrossing partitions of $\{0, \dots, n-1\}$ that are marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def marriageableSinglesCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n => IsMarriageableSingles P.val).card

/-- **Number of lonely singles partitions.** For $n \ge 0$, $L_n$ is the number of lonely singles
partitions of $\{0, \dots, n-1\}$, that is, of noncrossing partitions of $\{0, \dots, n-1\}$ that
are not marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 3. -/
def lonelySinglesCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n => ¬ IsMarriageableSingles P.val).card

/-- **Noncrossing partitions split into lonely and marriageable singles partitions.** For every
$n \ge 0$, the number $C_n$ of noncrossing partitions of $\{0, \dots, n-1\}$ equals $L_n + M_n$,
where $M_n$ is the number of those that are marriageable singles partitions and $L_n$ is the
number of those that are not.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Lemma 6
(`jis-2025-25.1.1-lem-6`). -/
theorem card_noncrossingPartition_eq_lonely_add_marriageable (n : ℕ) :
    Fintype.card (_root_.NoncrossingPartition n) =
      lonelySinglesCount n + marriageableSinglesCount n := by
  rw [lonelySinglesCount, marriageableSinglesCount, Nat.add_comm,
    Finset.card_filter_add_card_filter_not, Finset.card_univ]

/-- **Small values of the marriageable singles count.** For every $n \le 1$, the number of
marriageable singles partitions of $\{0, \dots, n-1\}$ is $M_n = 0$: a marriageable singles
partition needs two distinct points.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Table 1. -/
theorem marriageableSinglesCount_of_le_one {n : ℕ} (hn : n ≤ 1) :
    marriageableSinglesCount n = 0 := by
  rw [marriageableSinglesCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro P - ⟨i, j, hij, -⟩
  exact hij (Fin.ext (by omega))

/-- **Small values of the lonely singles count.** The numbers of lonely singles partitions of
$\{0, \dots, n-1\}$ for $n = 0$ and $n = 1$ are $L_0 = 1$ and $L_1 = 1$.

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

/-- **Noncrossing partitions by number of blocks and of singleton blocks.** For natural numbers
$n$, $m$ and $k$, $NC_{n,m,k}$ is the number of noncrossing partitions of $\{0, \dots, n-1\}$
that have exactly $m$ blocks, exactly $k$ of which are singletons.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 23. -/
def noncrossingBlockSingletonCount (n m k : ℕ) : ℕ :=
  (Finset.univ.filter fun P : _root_.NoncrossingPartition n =>
    P.val.parts.card = m ∧ (P.val.parts.filter fun B => B.card = 1).card = k).card

/-- **Base value of the noncrossing block and singleton count.** Exactly one noncrossing partition
of the empty set has $0$ blocks, $0$ of which are singletons, namely the empty partition; that
is, $NC_{0,0,0} = 1$, where $NC_{n,m,k}$ is the number of noncrossing partitions of
$\{0, \dots, n-1\}$ with $m$ blocks of which $k$ are singletons.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Remark 25. -/
theorem noncrossingBlockSingletonCount_zero : noncrossingBlockSingletonCount 0 0 0 = 1 := by
  have h : ∀ P : _root_.NoncrossingPartition 0, P.val.parts = ∅ := fun P =>
    Finpartition.parts_eq_empty_iff.mpr (by simp)
  rw [noncrossingBlockSingletonCount, Finset.filter_true_of_mem (fun P _ => by simp [h P]),
    Finset.card_univ]
  exact NoncrossingPartition.card_zero

/-- **Zero-extended binomial coefficient.** For integers $a$ and $b$, the zero-extended binomial
coefficient $\binom{a}{b}$ is the usual binomial coefficient of $a$ and $b$ when $a \ge 0$ and
$b \ge 0$, and $0$ otherwise.

This is the convention under which the paper's formulas "give $0$" in the degenerate cases (for
example $\binom{-1}{0} = 0$ in the count of noncrossing partitions of a one-element set with
one block and no singleton block).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
def zeroExtendedChoose (a b : ℤ) : ℕ :=
  if 0 ≤ a ∧ 0 ≤ b then a.toNat.choose b.toNat else 0

/-- **The zero-extended binomial coefficient on natural numbers.** Extend the binomial coefficient
$\binom{a}{b}$ to all integers $a$, $b$ by setting it to $0$ when $a < 0$ or $b < 0$. For all
natural numbers $a$ and $b$, this extended binomial coefficient at $a$ and $b$ viewed as integers
equals the usual binomial coefficient $\binom{a}{b}$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
theorem zeroExtendedChoose_natCast (a b : ℕ) : zeroExtendedChoose a b = a.choose b := by
  simp [zeroExtendedChoose]

/-- **The zero-extended binomial coefficient vanishes at $(-1, 0)$.** Extend the binomial
coefficient $\binom{a}{b}$ to all integers $a$, $b$ by setting it to $0$ when $a < 0$ or $b < 0$.
Under this convention $\binom{-1}{0} = 0$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, proof of
Proposition 24 (degenerate cases giving `0`). -/
theorem zeroExtendedChoose_neg_one_zero : zeroExtendedChoose (-1) 0 = 0 := by
  simp [zeroExtendedChoose]

/-- **Lanes with a common point.** The standard road intersection of size $n$ has entries
$E_0, \dots, E_{n-1}$ and exits $X_0, \dots, X_{n-1}$ on a circle, with $E_i$ at position $2i$
and $X_j$ at position $2j + 1$; the lane $E_iX_j$ is the chord from $E_i$ to $X_j$. Two lanes
$E_iX_j$ and $E_{i'}X_{j'}$ have a common point if $i = i'$, or $j = j'$, or exactly one of the
positions $2i'$ and $2j' + 1$ lies strictly between $2i$ and $2j + 1$ (that is, the chords cross).

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 10 and 13
(lanes, noncrossing lanes). -/
def lanesMeet {n : ℕ} (ℓ ℓ' : Fin n × Fin n) : Prop :=
  ℓ.1 = ℓ'.1 ∨ ℓ.2 = ℓ'.2 ∨
    (let lo := min (2 * ℓ.1.val) (2 * ℓ.2.val + 1)
     let hi := max (2 * ℓ.1.val) (2 * ℓ.2.val + 1)
     ((lo < 2 * ℓ'.1.val ∧ 2 * ℓ'.1.val < hi) ↔
       ¬ (lo < 2 * ℓ'.2.val + 1 ∧ 2 * ℓ'.2.val + 1 < hi)))

instance instDecidableLanesMeet {n : ℕ} (ℓ ℓ' : Fin n × Fin n) :
    Decidable (lanesMeet ℓ ℓ') := by
  unfold lanesMeet
  infer_instance

/-- **Maximal set of lanes.** In the standard road intersection of size $n$, the lane $E_iX_j$
joins the entry $E_i$ to the exit $X_j$, for $i, j \in \{0, \dots, n-1\}$. Given a set $A$ of
allowed lanes, a set $S$ of lanes is a maximal set of lanes (MSL) among $A$ if $S \subseteq A$,
no two distinct lanes of $S$ have a common point, and every lane of $A$ not in $S$ has a common
point with some lane of $S$. The standard road intersection allows every lane; the restricted one
forbids the U-turns $E_iX_i$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definitions 12 and 13
(restricted standard road intersection, MSL). -/
def IsMaximalSetOfLanes {n : ℕ} (allowed S : Finset (Fin n × Fin n)) : Prop :=
  S ⊆ allowed ∧ (∀ ℓ ∈ S, ∀ ℓ' ∈ S, ℓ ≠ ℓ' → ¬ lanesMeet ℓ ℓ') ∧
    ∀ ℓ ∈ allowed, ℓ ∉ S → ∃ ℓ' ∈ S, lanesMeet ℓ ℓ'

instance instDecidableIsMaximalSetOfLanes {n : ℕ} (allowed S : Finset (Fin n × Fin n)) :
    Decidable (IsMaximalSetOfLanes allowed S) := by
  unfold IsMaximalSetOfLanes
  infer_instance

/-- **Absolute maximal set of lanes.** In the standard road intersection of size $n$, the lane
$E_iX_j$ joins the entry $E_i$ to the exit $X_j$, for $i, j \in \{0, \dots, n-1\}$. A set $S$ of
lanes is absolute if it is a maximal set of lanes among all lanes and there are no $i \ne j$ such
that $S$ contains both U-turns $E_iX_i$ and $E_jX_j$ and replacing these two lanes in $S$ by
$E_iX_j$ and $E_jX_i$ gives again a maximal set of lanes among all lanes.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 15. -/
def IsAbsoluteMaximalSetOfLanes {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  IsMaximalSetOfLanes Finset.univ S ∧
    ¬ ∃ i j : Fin n, i ≠ j ∧ (i, i) ∈ S ∧ (j, j) ∈ S ∧
      IsMaximalSetOfLanes Finset.univ
        (insert (i, j) (insert (j, i) ((S.erase (i, i)).erase (j, j))))

instance instDecidableIsAbsoluteMaximalSetOfLanes {n : ℕ} (S : Finset (Fin n × Fin n)) :
    Decidable (IsAbsoluteMaximalSetOfLanes S) := by
  unfold IsAbsoluteMaximalSetOfLanes
  infer_instance

/-- **Maximal sets of lanes for an intersection of size two.** Write $E_iX_j$ for the lane from the
$i$-th entry to the $j$-th exit. In the standard road intersection of size $2$, in which every lane
is allowed, the maximal sets of lanes are exactly $\{E_1X_1, E_2X_2\}$ and $\{E_1X_2, E_2X_1\}$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Definition 13 (MSL). -/
theorem maximalSetsOfLanes_two :
    (Finset.univ.filter fun S : Finset (Fin 2 × Fin 2) => IsMaximalSetOfLanes Finset.univ S) =
      {{(0, 0), (1, 1)}, {(0, 1), (1, 0)}} := by
  decide

end

end MetaMathlibExt
