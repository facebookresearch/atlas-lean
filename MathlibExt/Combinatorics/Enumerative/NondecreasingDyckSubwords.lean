/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.NumberTheory.LucasSequence

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Subwords in non-decreasing Dyck paths

The main theorems give both generating functions and the Fibonacci–Lucas closed forms
for three consecutive up steps, valleys, peaks, and the subword UDU.

The definitions follow Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in
Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article
25.1.6. Dyck paths are Mathlib's `DyckWord`s. A Dyck path is non-decreasing when
the heights of its valley vertices (the low points of the factors `DU`), read
from left to right, form a non-decreasing sequence; this is the `0`-Dyck case
of Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. A subword is a contiguous factor, and
`nondecreasingDyckSubwordTotal w n` is the total number of occurrences of `w`
(overlapping occurrences counted separately) summed over the non-decreasing
Dyck paths of semilength `n`. The bivariate generating function
`F_w(x, y) = ∑_{n ≥ 1} ∑_{P} x^n y^{#w(P)}` is a power series in `x` with
coefficients in `ℤ[y]`, and the univariate `D_w(x) = ∑ d_w(n) x^n`. Generating
function identities are stated with the denominator cleared, and the closed
forms with the rational factor cleared, over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- **Valley heights.** For a finite sequence $l$ of up steps $U$ and down steps $D$, the valley
heights of $l$ form the list with one entry for each factor $DU$ of $l$, from left to right:
the number of $U$ steps minus the number of $D$ steps in $l$ up to and including the $D$ of
that factor, taken to be $0$ when negative.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1, the definition of non-decreasing Dyck paths used by
Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck
Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6. -/
public def dyckValleyHeights (l : List DyckStep) : List ℕ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some D ∧ l[i + 1]? = some U)).map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- **Valley heights of UUDUDDUD.** The Dyck path $UUDUDDUD$ has exactly two valleys, of heights
$1$ and $0$ from left to right.

In particular this path is not non-decreasing.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UUDUDDUD :
    dyckValleyHeights [U, U, D, U, D, D, U, D] = [1, 0] := by decide

/-- **Valley heights of UDUUDUDD.** The Dyck path $UDUUDUDD$ has exactly two valleys, of heights
$0$ and $1$ from left to right.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public theorem dyckValleyHeights_UDUUDUDD :
    dyckValleyHeights [U, D, U, U, D, U, D, D] = [0, 1] := by decide

/-- **Non-decreasing Dyck paths.** A Dyck path is non-decreasing when its valley heights (the
heights reached after the $D$ of each factor $DU$), read from left to right, form a
non-decreasing sequence.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1 (the `0`-Dyck paths), as used by Flórez, Junes,
Montoya, and Ramírez, *Counting Subwords in Non-Decreasing Dyck Paths*, Journal of
Integer Sequences 28 (2025), Article 25.1.6. -/
public def IsNondecreasingDyckPath (p : DyckWord) : Prop :=
  (dyckValleyHeights p.toList).Pairwise (· ≤ ·)

/-- Non-decreasing is decidable.

Source: Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. -/
public instance : DecidablePred IsNondecreasingDyckPath := fun p => by
  unfold IsNondecreasingDyckPath
  infer_instance

/-- **Non-decreasing Dyck paths of semilength $n$.** For a natural number $n$, $D_n$ is the finite
set of Dyck paths of semilength $n$ that are non-decreasing: the heights of their valleys (the
height reached after the $D$ of each factor $DU$), read from left to right, form a non-decreasing
sequence.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckWords (n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p => IsNondecreasingDyckPath p.1

/-- **Five non-decreasing Dyck paths of semilength 3.** There are exactly $5$ non-decreasing
Dyck paths of semilength $3$.

These are all five Dyck paths of semilength $3$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_three : (nondecreasingDyckWords 3).card = 5 := by
  decide +kernel

/-- **Thirteen non-decreasing Dyck paths of semilength 4.** There are exactly $13$
non-decreasing Dyck paths of semilength $4$.

They are all $14$ Dyck paths of semilength $4$ except $UUDUDDUD$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem card_nondecreasingDyckWords_four : (nondecreasingDyckWords 4).card = 13 := by
  decide +kernel

/-- **Number of occurrences of a subword.** For finite words $w$ and $l$ in the up step $U$ and
the down step $D$, the number of occurrences of $w$ in $l$ is the number of suffixes of $l$,
including $l$ itself and the empty suffix, that begin with $w$. Thus every occurrence of $w$ as a
contiguous subword of $l$ is counted, overlapping occurrences separately.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def dyckSubwordCount (w l : List DyckStep) : ℕ :=
  l.tails.countP fun t => w.isPrefixOf t

/-- **Occurrences of UU in UUUDDD.** The contiguous subword $UU$ occurs exactly $2$ times in
$UUUDDD$; the two occurrences overlap.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UU_UUUDDD :
    dyckSubwordCount [U, U] [U, U, U, D, D, D] = 2 := by decide

/-- **Occurrences of UDU in UDUDUD.** The contiguous subword $UDU$ occurs exactly $2$ times in
$UDUDUD$; the two occurrences overlap.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem dyckSubwordCount_UDU_UDUDUD :
    dyckSubwordCount [U, D, U] [U, D, U, D, U, D] = 2 := by decide

/-- **Total occurrences of a subword in non-decreasing Dyck paths.** For a word $w$ in the steps
$U$ and $D$ and for $n \ge 0$, $d_w(n)$ is the total number of occurrences of $w$ as a contiguous
subword (overlapping occurrences counted separately), summed over all non-decreasing Dyck paths
of semilength $n$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public def nondecreasingDyckSubwordTotal (w : List DyckStep) (n : ℕ) : ℕ :=
  ∑ p ∈ nondecreasingDyckWords n, dyckSubwordCount w p.1.toList

/-- **Peaks in the non-decreasing Dyck paths of semilength three.** Let $d_w(n)$ be the total
number of occurrences of the subword $w$ over all non-decreasing Dyck paths of semilength $n$.
Then $d_{UD}(3) = 10$; that is, the non-decreasing Dyck paths of semilength $3$ have $10$ peaks
$UD$ in total.

All five Dyck paths of semilength $3$ are non-decreasing.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public theorem nondecreasingDyckSubwordTotal_UD_three :
    nondecreasingDyckSubwordTotal [U, D] 3 = 10 := by
  decide +kernel

/-- **Bivariate generating function of a subword in non-decreasing Dyck paths.** For a word $w$
in the steps $U$ and $D$, let $D_n$ be the set of non-decreasing Dyck paths of semilength $n$,
and let $\#w(P)$ be the number of occurrences of $w$ as a contiguous subword of a path $P$,
overlapping occurrences counted separately. The bivariate generating function $F_w(x, y)$ is
the power series in $x$ with coefficients in $\mathbb{Z}[y]$ given by
$$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in D_n} y^{\#w(P)} x^n,$$
so its constant coefficient is $0$: the empty path is not counted.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordBivariateGF (w : List DyckStep) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else ∑ p ∈ nondecreasingDyckWords n, Polynomial.X ^ dyckSubwordCount w p.1.toList

/-- **Generating function of the total subword count in non-decreasing Dyck paths.** For a word
$w$ in the steps $U$ and $D$, let $d_w(n)$ be the total number of occurrences of $w$ as a
contiguous subword (overlapping occurrences counted separately) over all non-decreasing Dyck
paths of semilength $n$. The univariate generating function of $w$ is the integer power series
$$D_w(x) = \sum_{n \ge 0} d_w(n) x^n.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Section 1. -/
public noncomputable def nondecreasingDyckSubwordTotalGF (w : List DyckStep) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (nondecreasingDyckSubwordTotal w n : ℤ)

/-- **Height of the last peak.** For a finite sequence $l$ of up steps $U$ and down steps $D$,
the last peak height of $l$ is undefined when $l$ has no factor $UD$. Otherwise it is the
height of the peak of the rightmost factor $UD$: the number of $U$ steps minus the number of
$D$ steps in $l$ up to and including the $U$ of that factor, taken to be $0$ when negative.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def dyckLastPeakHeight (l : List DyckStep) : Option ℕ :=
  ((List.range l.length).filter fun i =>
      decide (l[i]? = some U ∧ l[i + 1]? = some D)).getLast?.map
    fun i => (l.take (i + 1)).count U - (l.take (i + 1)).count D

/-- **Last peak height of UDUUDD.** The last peak of the Dyck path $UDUUDD$ has height $2$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem dyckLastPeakHeight_UDUUDD :
    dyckLastPeakHeight [U, D, U, U, D, D] = some 2 := by decide

/-- **Non-decreasing Dyck paths by height of the last peak.** For natural numbers $n$ and $k$,
$l_{n,k}$ is the number of non-decreasing Dyck paths of semilength $n$ whose last peak (the last
factor $UD$) has height $k$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public def nondecreasingDyckLastPeakCount (n k : ℕ) : ℕ :=
  ((nondecreasingDyckWords n).filter fun p => dyckLastPeakHeight p.1.toList = some k).card

/-- **Non-decreasing Dyck paths of semilength four with last peak at height one.** Exactly four
non-decreasing Dyck paths of semilength $4$ have their last peak at height $1$; that is,
$l_{4,1} = 4$, where $l_{n,k}$ is the number of non-decreasing Dyck paths of semilength $n$
whose last peak has height $k$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16. -/
public theorem nondecreasingDyckLastPeakCount_four_one :
    nondecreasingDyckLastPeakCount 4 1 = 4 := by
  decide +kernel

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `y` of the bivariate generating functions, a constant in `ℤ[y]`. -/
local notation "𝒚" => PowerSeries.C (Polynomial.X : Polynomial ℤ)
/-- The variable `x` of the univariate generating functions. -/
local notation "𝒛" => (PowerSeries.X : PowerSeries ℤ)

namespace nondecreasingDyck_subword_UUU

private def balance (l : List DyckStep) : ℤ := (l.count U : ℤ) - l.count D

private def valleys (h : ℤ) (l : List DyckStep) : List ℤ :=
  ((List.range l.length).filter fun i => decide (l[i]? = some D ∧ l[i + 1]? = some U)).map
    fun i => h + balance (l.take (i + 1))

private lemma valleys_cons (s : DyckStep) (l : List DyckStep) (h : ℤ) :
    valleys h (s :: l) =
      (if s = D ∧ l[0]? = some U then [h - 1] else []) ++
        valleys (h + (if s = U then 1 else -1)) l := by
  cases s <;> by_cases hh : l[0]? = some U <;>
    simp [valleys, List.range_succ_eq_map, List.filter_map, List.map_map, Function.comp_def,
      balance, hh, Int.sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma valleys_append_down (l q : List DyckStep) (h : ℤ) :
    valleys h (l ++ D :: q) = valleys h l ++ valleys (h + balance l) (D :: q) := by
  induction l generalizing h with
  | nil => simp [balance, valleys]
  | cons s l ih =>
    simp only [List.cons_append, valleys_cons, ih, List.append_assoc]
    have head : (l ++ D :: q)[0]? = some U ↔ l[0]? = some U := by cases l <;> simp
    simp only [head]
    cases s <;> simp [balance] <;> ring_nf

private lemma valleys_nat (p : DyckWord) :
    valleys 0 p.toList = (dyckValleyHeights p.toList).map (Nat.cast : ℕ → ℤ) := by
  simp only [valleys, dyckValleyHeights, List.map_map, Function.comp_def, zero_add]
  apply List.map_congr_left
  intro i _
  simp [balance, Nat.cast_sub (p.count_D_le_count_U _)]

private lemma valleys_shift (p : DyckWord) :
    valleys 1 p.toList = (valleys 0 p.toList).map (1 + ·) := by
  simp [valleys, List.map_map, Function.comp_def]

private lemma valleys_nonneg (p : DyckWord) {x : ℤ} (h : x ∈ valleys 0 p.toList) : 0 ≤ x := by
  rw [valleys_nat, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  positivity

private lemma valleys_node (p q : DyckWord) :
    valleys 0 (p.nest + q).toList =
      (valleys 0 p.toList).map (1 + ·) ++
        (if q = 0 then [] else [0]) ++ valleys 0 q.toList := by
  change valleys 0 ((U :: p.toList ++ [D]) ++ q.toList) = _
  simp only [List.cons_append, List.append_assoc]
  simp only [valleys_cons, reduceCtorEq, false_and, ite_false,
    List.nil_append, ite_true, zero_add, valleys_append_down, valleys_shift]
  have hb : balance p.toList = 0 := by simp [balance, p.count_U_eq_count_D]
  rw [hb, add_zero]
  by_cases hq : q = 0
  · subst q
    rfl
  · have hh : q.toList[0]? = some U := by
      have hn := DyckWord.toList_ne_nil.mpr hq
      rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr hn), ← List.head_eq_getElem hn,
        q.head_eq_U hn]
    simp [hh, hq]

private lemma nondecreasing_iff (p : DyckWord) :
    IsNondecreasingDyckPath p ↔ (valleys 0 p.toList).Pairwise (· ≤ ·) := by
  simp [IsNondecreasingDyckPath, valleys_nat, List.pairwise_map]

-- A nonempty right part creates a valley at zero after all the valleys of the nested part.
private lemma good_node (p q : DyckWord) :
    IsNondecreasingDyckPath (p.nest + q) ↔
      if q = 0 then IsNondecreasingDyckPath p
      else valleys 0 p.toList = [] ∧ IsNondecreasingDyckPath q := by
  simp only [nondecreasing_iff, valleys_node]
  split_ifs with h
  · subst q
    simp [show valleys 0 (0 : DyckWord).toList = [] from rfl, List.pairwise_map]
  · simp only [List.append_assoc, List.singleton_append, List.pairwise_append,
      List.pairwise_cons, List.mem_cons, List.mem_map, List.pairwise_map]
    constructor
    · rintro ⟨_, ⟨_, hq⟩, cross⟩
      refine ⟨List.eq_nil_iff_forall_not_mem.mpr ?_, hq⟩
      intro x hx
      have := cross (1 + x) ⟨x, hx, rfl⟩ 0 (Or.inl rfl)
      have := valleys_nonneg p hx
      omega
    · rintro ⟨hp, hq⟩
      simpa [hp, hq] using fun x hx => @valleys_nonneg q x hx

private lemma flat_node (p q : DyckWord) :
    valleys 0 (p.nest + q).toList = [] ↔ valleys 0 p.toList = [] ∧ q = 0 := by
  rw [valleys_node]
  by_cases h : q = 0 <;> simp [h, show valleys 0 (0 : DyckWord).toList = [] from rfl]

private abbrev occurrences := dyckSubwordCount [U, U, U]

private lemma occurrences_cons (s : DyckStep) (l : List DyckStep) :
    occurrences (s :: l) = occurrences l +
      (if s = U ∧ l[0]? = some U ∧ l[1]? = some U then 1 else 0) := by
  unfold occurrences dyckSubwordCount
  rw [List.tails_cons, List.countP_cons]
  congr 1
  cases s <;> cases l with
  | nil => rfl
  | cons a l =>
    cases a <;> cases l with
    | nil => rfl
    | cons b l => cases b <;> rfl

private lemma occurrences_append_down (l q : List DyckStep) :
    occurrences (l ++ D :: q) = occurrences l + occurrences q := by
  induction l with
  | nil => simp [occurrences_cons, show occurrences [] = 0 from rfl]
  | cons s l ih =>
    have head : (l ++ D :: q)[0]? = some U ∧ (l ++ D :: q)[1]? = some U ↔
        l[0]? = some U ∧ l[1]? = some U := by
      cases l with
      | nil => simp
      | cons a l => cases l <;> simp
    simp only [List.cons_append, occurrences_cons, head, ih]
    omega

private def countFrom (t : ℕ) (p : DyckWord) : ℕ :=
  occurrences (List.replicate t U ++ p.toList)

private lemma countFrom_node (t : ℕ) (p q : DyckWord) :
    countFrom t (p.nest + q) = countFrom (t + 1) p + countFrom 0 q := by
  unfold countFrom
  change occurrences (List.replicate t U ++ ((U :: p.toList ++ [D]) ++ q.toList)) = _
  simp only [List.cons_append, List.append_assoc, List.replicate_zero,
    List.nil_append, List.replicate_succ']
  simpa only [List.append_assoc, List.cons_append] using
    occurrences_append_down (List.replicate t U ++ U :: p.toList) q.toList

private lemma countFrom_three (p : DyckWord) : countFrom 3 p = countFrom 2 p + 1 := by
  change occurrences (U :: U :: U :: p.toList) = occurrences (U :: U :: p.toList) + 1
  rw [occurrences_cons]
  rfl

open BinaryTree Finset PowerSeries

-- Enumerating by binary trees turns the first-return decomposition into a Cauchy product.
private noncomputable def enumerator (w : DyckWord → Polynomial ℤ) :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n => ∑ t ∈ treesOfNumNodesEq n, w (DyckWord.ofTree t)

private lemma enum_paths (w : DyckWord → Polynomial ℤ) (n : ℕ) :
    coeff n (enumerator w) = ∑ p : {p : DyckWord // p.semilength = n}, w p.val := by
  rw [enumerator, coeff_mk, ← Finset.sum_attach]
  symm
  apply Fintype.sum_equiv (DyckWord.equivTreesOfNumNodesEq n)
  intro p
  simp [DyckWord.equivTreesOfNumNodesEq, DyckWord.ofTree_toTree]

private lemma coeff_enum_succ (w : DyckWord → Polynomial ℤ) (n : ℕ) :
    coeff (n + 1) (enumerator w) = ∑ ij ∈ antidiagonal n,
      ∑ p ∈ treesOfNumNodesEq ij.1, ∑ q ∈ treesOfNumNodesEq ij.2,
        w ((DyckWord.ofTree p).nest + DyckWord.ofTree q) := by
  rw [enumerator, coeff_mk, treesOfNumNodesEq_succ, sum_biUnion]
  · apply sum_congr rfl
    intro ij _
    simp only [pairwiseNode, sum_map, sum_product]
    rfl
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

private lemma enum_node (w a b c d : DyckWord → Polynomial ℤ)
    (h : ∀ p q, w (p.nest + q) = a p * b q + c p * d q) :
    enumerator w = C (w 0) + X * (enumerator a * enumerator b + enumerator c * enumerator d) := by
  ext1 n
  cases n with
  | zero => simp [enumerator, DyckWord.ofTree]
  | succ n =>
    rw [coeff_enum_succ, map_add, coeff_succ_C, zero_add, coeff_succ_X_mul, map_add,
      coeff_mul, coeff_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro ij _
    simp only [h, enumerator, coeff_mk, sum_add_distrib, sum_mul, mul_sum]
    congr 1 <;> apply sum_comm

private noncomputable def emptyWeight (p : DyckWord) : Polynomial ℤ := if p = 0 then 1 else 0

private lemma enum_empty : enumerator emptyWeight = 1 := by
  ext1 n
  cases n with
  | zero =>
    rw [enumerator, coeff_mk, treesOfNumNodesEq_zero, sum_singleton, coeff_zero_one]
    rfl
  | succ n =>
    rw [coeff_enum_succ, coeff_one, ite_eq_right (Nat.succ_ne_zero _)]
    simp [emptyWeight, DyckWord.nest_ne_zero]

private lemma enum_zero : enumerator 0 = 0 := by ext1; simp [enumerator]

local notation "F" => nondecreasingDyckSubwordBivariateGF [U, U, U]

-- The prefix of t up steps records occurrences that cross into the current path.
private noncomputable def goodWeight (t : ℕ) (p : DyckWord) : Polynomial ℤ :=
  if IsNondecreasingDyckPath p then Polynomial.X ^ countFrom t p else 0

private noncomputable def flatWeight (t : ℕ) (p : DyckWord) : Polynomial ℤ :=
  if valleys 0 p.toList = [] then Polynomial.X ^ countFrom t p else 0

private noncomputable def rightWeight (w : List DyckStep) (p : DyckWord) : Polynomial ℤ :=
  if p = 0 then 0 else
    if IsNondecreasingDyckPath p then Polynomial.X ^ dyckSubwordCount w p.toList else 0

private lemma good_node_weight (t : ℕ) (p q : DyckWord) :
    goodWeight t (p.nest + q) =
      goodWeight (t + 1) p * emptyWeight q + flatWeight (t + 1) p * rightWeight [U, U, U] q := by
  simp only [goodWeight, good_node, countFrom_node, pow_add, emptyWeight, flatWeight, rightWeight,
    show ∀ q, dyckSubwordCount [U, U, U] q.toList = countFrom 0 q from fun _ => rfl]
  by_cases h : q = 0
  · subst q
    simp [show countFrom 0 0 = 0 from rfl]
  · simp only [h, ite_false, mul_zero, zero_add]
    split_ifs <;> simp_all

private lemma flat_node_weight (t : ℕ) (p q : DyckWord) :
    flatWeight t (p.nest + q) = flatWeight (t + 1) p * emptyWeight q +
      (0 : DyckWord → Polynomial ℤ) p * (0 : DyckWord → Polynomial ℤ) q := by
  simp only [flatWeight, flat_node, countFrom_node, emptyWeight, Pi.zero_apply, mul_zero, add_zero]
  by_cases h : q = 0
  · subst q
    simp [show countFrom 0 0 = 0 from rfl]
  · simp [h]

private lemma enum_right (w : List DyckStep) :
    enumerator (rightWeight w) = nondecreasingDyckSubwordBivariateGF w := by
  ext1 n
  cases n with
  | zero => simp [enumerator, rightWeight, nondecreasingDyckSubwordBivariateGF, DyckWord.ofTree]
  | succ n =>
    rw [enum_paths, nondecreasingDyckSubwordBivariateGF, coeff_mk,
      ite_eq_right (Nat.succ_ne_zero _), nondecreasingDyckWords, sum_filter]
    apply sum_congr rfl
    intro p _
    have h : p.val ≠ 0 := fun hp => by simpa [hp] using p.property
    simp [rightWeight, h]

private lemma enum_good_zero (w : List DyckStep) (hw : dyckSubwordCount w [] = 0) :
    enumerator (fun p => if IsNondecreasingDyckPath p then
      Polynomial.X ^ dyckSubwordCount w p.toList else 0) =
        1 + nondecreasingDyckSubwordBivariateGF w := by
  change dyckSubwordCount w (0 : DyckWord).toList = 0 at hw
  rw [← enum_right, ← enum_empty]
  ext1 n
  simp only [map_add, enumerator, coeff_mk, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases h : DyckWord.ofTree p = 0
  · simp [h, rightWeight, emptyWeight, show IsNondecreasingDyckPath 0 from by decide, hw]
  · simp [h, rightWeight, emptyWeight]

private lemma enum_good_rec (t : ℕ) (ht : t ≤ 2) :
    enumerator (goodWeight t) = 1 + 𝒙 *
      (enumerator (goodWeight (t + 1)) + enumerator (flatWeight (t + 1)) * F) := by
  rw [enum_node _ _ _ _ _ (good_node_weight t), enum_empty, enum_right, mul_one]
  have h : countFrom t 0 = 0 := by interval_cases t <;> rfl
  simp [goodWeight, show IsNondecreasingDyckPath 0 from by decide, h]

private lemma enum_flat_rec (t : ℕ) (ht : t ≤ 2) :
    enumerator (flatWeight t) = 1 + 𝒙 * enumerator (flatWeight (t + 1)) := by
  rw [enum_node _ _ _ _ _ (flat_node_weight t), enum_empty, enum_zero]
  have h : countFrom t 0 = 0 := by interval_cases t <;> rfl
  simp [flatWeight, show valleys 0 (0 : DyckWord).toList = [] from rfl, h]

private lemma enum_mark (a b : DyckWord → Polynomial ℤ)
    (h : ∀ p, a p = Polynomial.X * b p) : enumerator a = 𝒚 * enumerator b := by
  ext1 n
  simp [enumerator, h, mul_sum, coeff_C_mul]

private lemma enum_good_three : enumerator (goodWeight 3) = 𝒚 * enumerator (goodWeight 2) := by
  apply enum_mark
  intro p
  simp [goodWeight, countFrom_three, pow_succ, mul_ite, mul_comm]

private lemma enum_flat_three : enumerator (flatWeight 3) = 𝒚 * enumerator (flatWeight 2) := by
  apply enum_mark
  intro p
  simp [flatWeight, countFrom_three, pow_succ, mul_ite, mul_comm]

private lemma bivariate : (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * F = (1 - 𝒙 * 𝒚) * 𝒙 := by
  have g₀ := enum_good_rec 0 (by decide)
  have g₁ := enum_good_rec 1 (by decide)
  have g₂ := enum_good_rec 2 (by decide)
  have p₁ := enum_flat_rec 1 (by decide)
  have p₂ := enum_flat_rec 2 (by decide)
  rw [show enumerator (goodWeight 0) = 1 + F from enum_good_zero [U, U, U] rfl] at g₀
  rw [enum_good_three, enum_flat_three] at g₂
  rw [enum_flat_three] at p₂
  -- Eliminate the series with one or two prefixed up steps.
  let a := 1 - 𝒙 * 𝒚
  have h₁ : a * enumerator (goodWeight 1) =
      a + 𝒙 + 𝒙 * enumerator (flatWeight 2) * F := by
    dsimp [a]
    linear_combination (1 - 𝒙 * 𝒚) * g₁ + 𝒙 * g₂
  have h₂ : a * (1 - 𝒙) * F = 𝒙 * (a + 𝒙) +
      (1 + a) * 𝒙 ^ 2 * enumerator (flatWeight 2) * F := by
    linear_combination a * g₀ + a * 𝒙 * F * p₁ + 𝒙 * h₁
  have hn : a + 𝒙 ≠ 0 := by
    intro e
    have := congrArg PowerSeries.constantCoeff e
    simp [a] at this
  apply mul_left_cancel₀ hn
  dsimp [a] at h₂ ⊢
  linear_combination (1 - 𝒙 * 𝒚) * h₂ + (2 - 𝒙 * 𝒚) * 𝒙 ^ 2 * F * p₂

local notation "T" => nondecreasingDyckSubwordTotalGF [U, U, U]

private noncomputable abbrev value := PowerSeries.map (Polynomial.evalRingHom (1 : ℤ))

-- Differentiate the marking polynomial at one to count all marked positions.
private noncomputable def slope (s : PowerSeries (Polynomial ℤ)) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((coeff n s).derivative).eval 1

private lemma slope_add (u v : PowerSeries (Polynomial ℤ)) :
    slope (u + v) = slope u + slope v := by ext1; simp [slope]

private lemma slope_sub (u v : PowerSeries (Polynomial ℤ)) :
    slope (u - v) = slope u - slope v := by ext1; simp [slope]

private lemma slope_X (u : PowerSeries (Polynomial ℤ)) :
    slope (𝒙 * u) = 𝒛 * slope u := by
  ext1 n
  cases n <;> simp [slope, coeff_succ_X_mul]

private lemma slope_Y (u : PowerSeries (Polynomial ℤ)) :
    slope (𝒚 * u) = value u + slope u := by
  ext1 n
  simp [slope, value, Polynomial.derivative_mul, coeff_C_mul, coeff_map]

private lemma slope_one : slope 1 = 0 := by
  ext1 n
  by_cases h : n = 0 <;> simp [slope, coeff_one, h]

private lemma slope_F (w : List DyckStep) (h : nondecreasingDyckSubwordTotal w 0 = 0) :
    slope (nondecreasingDyckSubwordBivariateGF w) = nondecreasingDyckSubwordTotalGF w := by
  ext1 n
  cases n with
  | zero =>
    simp [slope, nondecreasingDyckSubwordBivariateGF, nondecreasingDyckSubwordTotalGF,
      h]
  | succ n =>
    simp [slope, nondecreasingDyckSubwordBivariateGF, nondecreasingDyckSubwordTotalGF,
      nondecreasingDyckSubwordTotal, Polynomial.eval_finsetSum,
      Polynomial.derivative_X_pow]

private lemma totalGF : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * T = 𝒛 ^ 3 := by
  have h : F = 𝒙 * 1 - 𝒙 * (𝒙 * (𝒚 * 1)) +
      𝒙 * (F + F + 𝒚 * F) - 𝒙 * (𝒙 * (𝒚 * F)) := by
    linear_combination bivariate
  have e := congrArg value h
  simp [value, PowerSeries.map_X, PowerSeries.map_C] at e
  have d := congrArg slope h
  simp only [slope_sub, slope_add, slope_X, slope_Y, slope_one,
    slope_F [U, U, U] (by decide +kernel), map_one] at d
  linear_combination (1 - 3 * 𝒛 + 𝒛 ^ 2) * d + (𝒛 - 𝒛 ^ 2) * e

-- A common squared denominator gives a fourth-order recurrence for both subwords.
private abbrev total (w : List DyckStep) (n : ℕ) : ℤ := nondecreasingDyckSubwordTotal w n

private def closedForm (a b c d : ℤ) (n : ℕ) : ℤ :=
  (a * n + b) * (Nat.fib (2 * n) : ℤ) + (c * n + d) * (lucasNumber (2 * n) : ℤ)

private lemma total_rec (w : List DyckStep) (rhs : PowerSeries ℤ)
    (hg : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * nondecreasingDyckSubwordTotalGF w = rhs)
    (n : ℕ) (hn : coeff (n + 4) rhs = 0) : total w (n + 4) =
      6 * total w (n + 3) - 11 * total w (n + 2) + 6 * total w (n + 1) - total w n := by
  let t := nondecreasingDyckSubwordTotalGF w
  have h : t - 𝒛 * (6 * t) + 𝒛 * (𝒛 * (11 * t)) -
      𝒛 * (𝒛 * (𝒛 * (6 * t))) + 𝒛 * (𝒛 * (𝒛 * (𝒛 * t))) = rhs := by
    dsimp only [t]
    linear_combination hg
  have e := congrArg (coeff (n + 4)) h
  simp only [map_add, map_sub, coeff_succ_X_mul, coeff_ofNat_mul, hn, t,
    nondecreasingDyckSubwordTotalGF, coeff_mk] at e
  linear_combination e

private lemma closedForm_rec (a b c d : ℤ) (n : ℕ) : closedForm a b c d (n + 4) =
    6 * closedForm a b c d (n + 3) - 11 * closedForm a b c d (n + 2) +
      6 * closedForm a b c d (n + 1) - closedForm a b c d n := by
  have hf (k : ℕ) : (Nat.fib (k + 2) : ℤ) = Nat.fib k + (Nat.fib (k + 1) : ℤ) := by
    rw [Nat.fib_add_two, Nat.cast_add]
  have hl (k : ℕ) : (lucasNumber (k + 2) : ℤ) = lucasNumber (k + 1) + (lucasNumber k : ℤ) := by
    rw [lucasNumber, Nat.cast_add]
  simp only [closedForm, Nat.mul_add, Nat.reduceMul, Nat.cast_add, Nat.cast_ofNat]
  generalize 2 * n = k
  rw [hf (k + 6), hl (k + 6), hf (k + 5), hl (k + 5), hf (k + 4), hl (k + 4),
    hf (k + 3), hl (k + 3), hf (k + 2), hl (k + 2), hf (k + 1), hl (k + 1), hf k, hl k]
  ring

private lemma closed (w : List DyckStep) (a b c d : ℤ) (rhs : PowerSeries ℤ)
    (hg : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * nondecreasingDyckSubwordTotalGF w = rhs)
    (hn : ∀ n, coeff (n + 4) rhs = 0)
    (hbase : ∀ n < 4, 10 * total w n = closedForm a b c d n) (n : ℕ) :
    10 * total w n = closedForm a b c d n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => exact hbase _ (by decide)
    | k + 4 =>
      rw [total_rec w rhs hg k (hn k), closedForm_rec]
      linear_combination 6 * ih (k + 3) (by omega) - 11 * ih (k + 2) (by omega) +
        6 * ih (k + 1) (by omega) - ih k (by omega)

end nondecreasingDyck_subword_UUU

/-- **Subword $UUU$ in non-decreasing Dyck paths.** Let $F_{UUU}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUU$ in $P$ (overlapping occurrences counted
separately). Let $d_{UUU}(n)$ be the total number of occurrences of $UUU$ over all non-decreasing
Dyck paths of semilength $n$, let $D_{UUU}(x) = \sum_{n \ge 0} d_{UUU}(n) x^n \in \mathbb{Z}[[x]]$,
and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$(1 - x(2 + y) + x^2 y) F_{UUU}(x, y) = (1 - xy) x$, $(1 - 3x + x^2)^2 D_{UUU}(x) = x^3$, and
for every $n \ge 1$, $10\, d_{UUU}(n) = -(5n + 4) F_{2n} + 3n L_{2n}$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 4
(`jis-2025-25.1.6-thm-4`). -/
public theorem nondecreasingDyck_subword_UUU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, U, U]
        = (1 - 𝒙 * 𝒚) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ) :=
  ⟨nondecreasingDyck_subword_UUU.bivariate, nondecreasingDyck_subword_UUU.totalGF, fun n _ => by
    have h := nondecreasingDyck_subword_UUU.closed [U, U, U] (-5) (-4) 3 0 _
      nondecreasingDyck_subword_UUU.totalGF
      (fun k => by simp [PowerSeries.coeff_X_pow, show k + 4 ≠ 3 by omega])
      (fun k hk => by interval_cases k <;> decide +kernel) n
    unfold nondecreasingDyck_subword_UUU.closedForm at h
    linear_combination h⟩

namespace nondecreasingDyck_subword_DU

open nondecreasingDyck_subword_UUU (valleys valleys_cons valleys_node good_node flat_node
  enumerator enum_node enum_empty enum_zero enum_right enum_good_zero enum_mark emptyWeight
  rightWeight value slope slope_sub slope_add slope_X slope_Y slope_one slope_F)
open PowerSeries

local notation "F" => nondecreasingDyckSubwordBivariateGF [D, U]
local notation "T" => nondecreasingDyckSubwordTotalGF [D, U]

-- Each occurrence of DU contributes one valley, regardless of the starting height.
private lemma count_eq_length (l : List DyckStep) (h : ℤ) :
    dyckSubwordCount [D, U] l = (valleys h l).length := by
  induction l generalizing h with
  | nil => rfl
  | cons s l ih =>
    have step : dyckSubwordCount [D, U] (s :: l) = dyckSubwordCount [D, U] l +
        (if s = D ∧ l[0]? = some U then 1 else 0) := by
      unfold dyckSubwordCount
      rw [List.tails_cons, List.countP_cons]
      congr 1
      cases s <;> cases l with
      | nil => rfl
      | cons a l => cases a <;> rfl
    rw [step, valleys_cons, List.length_append, ← ih]
    split <;> simp [Nat.add_comm]

private lemma count_node (p q : DyckWord) :
    dyckSubwordCount [D, U] (p.nest + q).toList =
      dyckSubwordCount [D, U] p.toList + dyckSubwordCount [D, U] q.toList +
        (if q = 0 then 0 else 1) := by
  simp only [fun l => count_eq_length l 0, valleys_node, List.length_append, List.length_map]
  split <;> simp [Nat.add_right_comm]

private noncomputable def weight (p : DyckWord) : Polynomial ℤ :=
  if IsNondecreasingDyckPath p then Polynomial.X ^ dyckSubwordCount [D, U] p.toList else 0

private noncomputable def pyramidWeight (p : DyckWord) : Polynomial ℤ :=
  if valleys 0 p.toList = [] then 1 else 0

-- With a nonempty suffix, the nested path must be a pyramid and the join is a new valley.
private lemma weight_node (p q : DyckWord) :
    weight (p.nest + q) = weight p * emptyWeight q +
      (Polynomial.X * pyramidWeight p) * rightWeight [D, U] q := by
  simp only [weight, count_node, good_node]
  by_cases hq : q = 0
  · subst q
    simp [emptyWeight, rightWeight,
      show dyckSubwordCount [D, U] (0 : DyckWord).toList = 0 from rfl]
  · by_cases hp : valleys 0 p.toList = []
    · have hc : dyckSubwordCount [D, U] p.toList = 0 := by rw [count_eq_length _ 0, hp]; rfl
      simp [rightWeight, emptyWeight, pyramidWeight, hq, hp, hc,
        pow_succ, mul_ite, mul_comm]
    · simp [rightWeight, emptyWeight, pyramidWeight, hq, hp]

private lemma pyramid_series : enumerator pyramidWeight = 1 + 𝒙 * enumerator pyramidWeight := by
  have h (p q : DyckWord) : pyramidWeight (p.nest + q) =
      pyramidWeight p * emptyWeight q +
        (0 : DyckWord → Polynomial ℤ) p * (0 : DyckWord → Polynomial ℤ) q := by
    simp only [pyramidWeight, flat_node]
    by_cases hq : q = 0 <;> simp [emptyWeight, hq]
  simpa [enum_empty, enum_zero, show pyramidWeight 0 = 1 from rfl] using enum_node _ _ _ _ _ h

private lemma bivariate : (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * F = (1 - 𝒙) * 𝒙 := by
  have h := enum_node _ _ _ _ _ weight_node
  rw [show enumerator weight = 1 + F from enum_good_zero [D, U] rfl, enum_empty, enum_right,
    enum_mark _ pyramidWeight (fun _ => rfl), show weight 0 = 1 from rfl, map_one, mul_one] at h
  linear_combination (1 - 𝒙) * h + 𝒙 * 𝒚 * F * pyramid_series

private lemma totalGF : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * T = (1 - 𝒛) * 𝒛 ^ 2 := by
  have h : F = 𝒙 * 1 - 𝒙 * (𝒙 * 1) + 𝒙 * (F + F + 𝒚 * F) - 𝒙 * (𝒙 * F) := by
    linear_combination bivariate
  have e := congrArg value h
  simp [value, PowerSeries.map_X, PowerSeries.map_C] at e
  have d := congrArg slope h
  simp only [slope_sub, slope_add, slope_X, slope_Y, slope_one,
    slope_F [D, U] (by decide +kernel)] at d
  linear_combination (1 - 3 * 𝒛 + 𝒛 ^ 2) * d + 𝒛 * e

end nondecreasingDyck_subword_DU

/-- **The subword $DU$ in non-decreasing Dyck paths.** Let $F_{DU}(x, y)$ and $D_{DU}(x)$ be the
bivariate and univariate generating functions of the subword $DU$ in non-decreasing Dyck paths,
let $d_{DU}(n)$ be the total number of occurrences of $DU$ over all non-decreasing Dyck paths of
semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 2x + x^2 - xy) F_{DU}(x, y) = (1 - x) x$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DU}(x) = (1 - x) x^2$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 1$,
$$10 d_{DU}(n) = (5n - 2) F_{2n} - n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 2
(`jis-2025-25.1.6-thm-2`). -/
public theorem nondecreasingDyck_subword_DU :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U] = (1 - 𝒛) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U] n : ℤ) =
        (5 * (n : ℤ) - 2) * (Nat.fib (2 * n) : ℤ) - (n : ℤ) * (lucasNumber (2 * n) : ℤ) :=
  ⟨nondecreasingDyck_subword_DU.bivariate, nondecreasingDyck_subword_DU.totalGF, fun n _ => by
    have h := nondecreasingDyck_subword_UUU.closed [D, U] 5 (-2) (-1) 0 _
      nondecreasingDyck_subword_DU.totalGF
      (fun k => by
        simp [sub_mul, ← pow_succ', PowerSeries.coeff_X_pow, show k + 4 ≠ 2 by omega,
          show k + 4 ≠ 3 by omega])
      (fun k hk => by interval_cases k <;> decide +kernel) n
    unfold nondecreasingDyck_subword_UUU.closedForm at h
    linear_combination h⟩

namespace nondecreasingDyck_subword_UD

open nondecreasingDyck_subword_UUU (value slope_Y slope_F total closedForm total_rec closedForm_rec)
open PowerSeries

private lemma count_pair_cons (s t a b : DyckStep) (l : List DyckStep) :
    dyckSubwordCount [s, t] (a :: b :: l) =
      dyckSubwordCount [s, t] (b :: l) + (if a = s ∧ b = t then 1 else 0) := by
  unfold dyckSubwordCount
  rw [List.tails_cons, List.countP_cons]
  congr 1
  cases s <;> cases t <;> cases a <;> cases b <;> rfl

-- Each adjacent transition changes the indicator of an up step by its signed contribution.
private lemma transition_balance (l : List DyckStep) :
    dyckSubwordCount [U, D] l + (if l.getLast? = some U then 1 else 0) =
      dyckSubwordCount [D, U] l + (if l.head? = some U then 1 else 0) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => cases a <;> decide
    | cons b l =>
      simp only [count_pair_cons, List.getLast?_cons_cons, List.head?_cons]
      simp only [List.head?_cons] at ih
      cases a <;> cases b <;> simp_all
      omega

private lemma count_eq (p : DyckWord) (hp : p ≠ 0) :
    dyckSubwordCount [U, D] p.toList = dyckSubwordCount [D, U] p.toList + 1 := by
  have h := DyckWord.toList_ne_nil.mpr hp
  simpa [List.head?_eq_some_head h, List.getLast?_eq_some_getLast h,
    p.head_eq_U h, p.getLast_eq_D h] using transition_balance p.toList

local notation "FUD" => nondecreasingDyckSubwordBivariateGF [U, D]
local notation "FDU" => nondecreasingDyckSubwordBivariateGF [D, U]
local notation "TUD" => nondecreasingDyckSubwordTotalGF [U, D]
local notation "TDU" => nondecreasingDyckSubwordTotalGF [D, U]

private lemma bivariate_shift : FUD = 𝒚 * FDU := by
  ext1 n
  by_cases hn : n = 0
  · simp [nondecreasingDyckSubwordBivariateGF, coeff_C_mul, hn]
  · simp only [nondecreasingDyckSubwordBivariateGF, coeff_C_mul, coeff_mk, hn, ↓reduceIte,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : p.val ≠ 0 := by
      intro h
      exact hn (by simpa [h] using p.property.symm)
    rw [count_eq _ hp, pow_succ']

private lemma bivariate : (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * FUD = (1 - 𝒙) * 𝒙 * 𝒚 := by
  rw [bivariate_shift, mul_left_comm, nondecreasingDyck_subword_DU.1, mul_comm]

private lemma totalGF : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * TUD = 𝒛 * (1 - 𝒛) ^ 3 := by
  have hvalue : (1 - 3 * 𝒛 + 𝒛 ^ 2) * value FDU = (1 - 𝒛) * 𝒛 := by
    have h := congrArg value nondecreasingDyck_subword_DU.1
    simp [value, PowerSeries.map_X, PowerSeries.map_C, map_ofNat] at h
    linear_combination h
  have htotal : TUD = value FDU + TDU := by
    rw [← slope_F [U, D] (by decide +kernel), bivariate_shift, slope_Y,
      slope_F [D, U] (by decide +kernel)]
  rw [htotal]
  linear_combination (1 - 3 * 𝒛 + 𝒛 ^ 2) * hvalue + nondecreasingDyck_subword_DU.2.1

private lemma closed (n : ℕ) (hn : 1 ≤ n) : 10 * total [U, D] n = closedForm 5 (-7) (-1) 5 n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => omega
    | 1 | 2 | 3 | 4 => decide +kernel
    | k + 5 =>
      have hpoly : 𝒛 * (1 - 𝒛) ^ 3 = 𝒛 ^ 1 - 3 * 𝒛 ^ 2 + 3 * 𝒛 ^ 3 - 𝒛 ^ 4 := by ring
      have hz : coeff ((k + 1) + 4) (𝒛 * (1 - 𝒛) ^ 3) = 0 := by
        simp only [hpoly, map_sub, map_add, coeff_X_pow, coeff_ofNat_mul]
        split_ifs <;> omega
      rw [total_rec _ _ totalGF (k + 1) hz, closedForm_rec 5 (-7) (-1) 5 (k + 1)]
      linear_combination 6 * ih (k + 1 + 3) (by omega) (by omega) -
        11 * ih (k + 1 + 2) (by omega) (by omega) +
        6 * ih (k + 1 + 1) (by omega) (by omega) - ih (k + 1) (by omega) (by omega)

end nondecreasingDyck_subword_UD

/-- **Generating functions and closed form for the subword $UD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UD}(P)$ be the number of occurrences of the subword $UD$ in a path $P$, and let
$d_{UD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UD}(P)$. Let
$F_{UD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UD}(P)} x^n$, a power series in
$x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UD}(x) = \sum_{n \ge 0} d_{UD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - 2x + x^2 - xy) F_{UD}(x, y) = (1 - x) x y$ and
$(1 - 3x + x^2)^2 D_{UD}(x) = x (1 - x)^3$, and for every $n \ge 1$,
$$10\, d_{UD}(n) = (5n - 7) F_{2n} - (n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 1
(`jis-2025-25.1.6-thm-1`). -/
public theorem nondecreasingDyck_subword_UD :
    (1 - 2 * 𝒙 + 𝒙 ^ 2 - 𝒙 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D] = (1 - 𝒙) * 𝒙 * 𝒚 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D] = 𝒛 * (1 - 𝒛) ^ 3 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D] n : ℤ) =
        (5 * (n : ℤ) - 7) * (Nat.fib (2 * n) : ℤ) - ((n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ) :=
  ⟨nondecreasingDyck_subword_UD.bivariate, nondecreasingDyck_subword_UD.totalGF, fun n hn => by
    have h := nondecreasingDyck_subword_UD.closed n hn
    unfold nondecreasingDyck_subword_UUU.closedForm at h
    linear_combination h⟩

namespace nondecreasingDyck_subword_UDU

open nondecreasingDyck_subword_UUU (valleys good_node flat_node enumerator enum_node enum_empty
  enum_zero enum_right enum_good_zero emptyWeight rightWeight value slope slope_sub slope_add
  slope_X slope_Y slope_one slope_F total closedForm total_rec closedForm_rec)
open nondecreasingDyck_subword_DU (pyramidWeight pyramid_series)
open PowerSeries

private abbrev occurrences := dyckSubwordCount [U, D, U]

private lemma occurrences_pair (a b : DyckStep) (l : List DyckStep) :
    occurrences (a :: b :: l) = occurrences (b :: l) +
      (if a = U ∧ b = D ∧ l.head? = some U then 1 else 0) := by
  unfold occurrences dyckSubwordCount
  rw [List.tails_cons, List.countP_cons]
  congr 1
  cases a <;> cases b <;> cases l with
  | nil => rfl
  | cons c l => cases c <;> rfl

private lemma occurrences_down (l : List DyckStep) : occurrences (D :: l) = occurrences l := by
  unfold occurrences dyckSubwordCount
  rw [List.tails_cons, List.countP_cons]
  rfl

-- The separating down step can only be the middle letter of a new occurrence.
private lemma occurrences_join (l q : List DyckStep) :
    occurrences (l ++ D :: q) = occurrences l + occurrences q +
      (if l.getLast? = some U ∧ q.head? = some U then 1 else 0) := by
  induction l with
  | nil => simp [occurrences_down, show occurrences [] = 0 from rfl]
  | cons a l ih =>
    cases l with
    | nil =>
      simp [occurrences_pair, occurrences_down, show occurrences [a] = 0 by cases a <;> rfl]
    | cons b l =>
      have hh : (l ++ D :: q).head? = some U ↔ l.head? = some U := by cases l <;> simp
      simp only [List.cons_append, occurrences_pair, hh, List.getLast?_cons_cons]
      simp only [List.cons_append] at ih
      omega

private lemma count_node (p q : DyckWord) :
    occurrences (p.nest + q).toList = occurrences p.toList + occurrences q.toList +
      (if p = 0 ∧ q ≠ 0 then 1 else 0) := by
  change occurrences ((U :: p.toList ++ [D]) ++ q.toList) = _
  rw [List.append_assoc, List.singleton_append, occurrences_join]
  have hq : q.toList.head? = some U ↔ q ≠ 0 := by
    by_cases h : q = 0
    · subst q; decide
    · have hn := DyckWord.toList_ne_nil.mpr h
      simp [h, List.head?_eq_some_head hn, q.head_eq_U hn]
  simp only [hq]
  by_cases h : p = 0
  · subst p
    simp [show (0 : DyckWord).toList = [] from rfl,
      show occurrences [U] = occurrences [] from rfl]
  · have hn := DyckWord.toList_ne_nil.mpr h
    have hl : (U :: p.toList).getLast? = some D := by
      rw [List.getLast?_cons_of_ne_nil hn, List.getLast?_eq_some_getLast hn, p.getLast_eq_D hn]
    have hc : occurrences (U :: p.toList) = occurrences p.toList := by
      have hh : U :: p.toList.tail = p.toList := by
        simpa [p.head_eq_U hn] using List.cons_head_tail hn
      rw [← hh, occurrences_pair]
      simp
    simp [hl, hc, h]

private lemma occurrences_flat (p : DyckWord) (hp : valleys 0 p.toList = []) :
    occurrences p.toList = 0 := by
  rw [← DyckWord.ofTree_toTree p] at hp ⊢
  generalize p.toTree = t at hp ⊢
  induction t with
  | nil => rfl
  | node _ l r ih _ =>
    obtain ⟨hl, hr⟩ := (flat_node _ _).mp hp
    rw [DyckWord.ofTree, count_node, hr, ih hl]
    simp [show occurrences (0 : DyckWord).toList = 0 from rfl]

private noncomputable def weight (p : DyckWord) : Polynomial ℤ :=
  if IsNondecreasingDyckPath p then Polynomial.X ^ occurrences p.toList else 0

-- When the right part is nonempty, the nested part must be a pyramid.
-- Only the empty interior gives the extra UDU at their join.
private noncomputable def joinWeight (p : DyckWord) : Polynomial ℤ :=
  if p = 0 then Polynomial.X else pyramidWeight p

private lemma weight_node (p q : DyckWord) :
    weight (p.nest + q) =
      weight p * emptyWeight q + joinWeight p * rightWeight [U, D, U] q := by
  simp only [weight, count_node, good_node, joinWeight, pyramidWeight, emptyWeight, rightWeight]
  by_cases hq : q = 0
  · subst q
    simp [show occurrences (0 : DyckWord).toList = 0 from rfl]
  · by_cases hp : p = 0
    · subst p
      simp [hq, show valleys 0 (0 : DyckWord).toList = [] from rfl,
        show occurrences (0 : DyckWord).toList = 0 from rfl, pow_succ', mul_ite, occurrences]
    · by_cases hf : valleys 0 p.toList = []
      · simp [hp, hq, hf, occurrences_flat p hf, occurrences]
      · simp [hp, hq, hf]

private lemma join_series : enumerator joinWeight = 𝒚 + 𝒙 * enumerator pyramidWeight := by
  have h (p q : DyckWord) : joinWeight (p.nest + q) = pyramidWeight p * emptyWeight q +
      (0 : DyckWord → Polynomial ℤ) p * (0 : DyckWord → Polynomial ℤ) q := by
    simp only [joinWeight, add_eq_zero, DyckWord.nest_ne_zero, false_and, ite_false,
      pyramidWeight, flat_node]
    by_cases hq : q = 0 <;> simp [emptyWeight, hq]
  simpa [enum_empty, enum_zero, show joinWeight 0 = Polynomial.X from rfl]
    using enum_node _ _ _ _ _ h

local notation "F" => nondecreasingDyckSubwordBivariateGF [U, D, U]
local notation "T" => nondecreasingDyckSubwordTotalGF [U, D, U]

private lemma bivariate : (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * F = (1 - 𝒙) * 𝒙 := by
  have h := enum_node _ _ _ _ _ weight_node
  rw [show enumerator weight = 1 + F from enum_good_zero [U, D, U] rfl, enum_empty, enum_right,
    join_series, show weight 0 = 1 from rfl, map_one, mul_one] at h
  linear_combination (1 - 𝒙) * h + 𝒙 ^ 2 * F * pyramid_series

private lemma totalGF : (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2 * T = 𝒛 ^ 2 * (1 - 𝒛) ^ 2 := by
  have h : F = 𝒙 * 1 - 𝒙 * (𝒙 * 1) +
      𝒙 * (F + F + 𝒚 * F) - 𝒙 * (𝒙 * (𝒚 * F)) := by
    linear_combination bivariate
  have e := congrArg value h
  simp [value, PowerSeries.map_X, PowerSeries.map_C] at e
  have d := congrArg slope h
  simp only [slope_sub, slope_add, slope_X, slope_Y, slope_one,
    slope_F [U, D, U] (by decide +kernel)] at d
  linear_combination (1 - 3 * 𝒛 + 𝒛 ^ 2) * d + (𝒛 - 𝒛 ^ 2) * e

private lemma closed (n : ℕ) (hn : 1 ≤ n) :
    10 * total [U, D, U] n = closedForm (-5) 11 3 (-5) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => omega
    | 1 | 2 | 3 | 4 => decide +kernel
    | k + 5 =>
      have hpoly : 𝒛 ^ 2 * (1 - 𝒛) ^ 2 = 𝒛 ^ 2 - 2 * 𝒛 ^ 3 + 𝒛 ^ 4 := by ring
      have hz : coeff ((k + 1) + 4) (𝒛 ^ 2 * (1 - 𝒛) ^ 2) = 0 := by
        simp only [hpoly, map_sub, map_add, coeff_X_pow, coeff_ofNat_mul]
        split_ifs <;> omega
      rw [total_rec _ _ totalGF (k + 1) hz, closedForm_rec (-5) 11 3 (-5) (k + 1)]
      linear_combination 6 * ih (k + 1 + 3) (by omega) (by omega) -
        11 * ih (k + 1 + 2) (by omega) (by omega) +
        6 * ih (k + 1 + 1) (by omega) (by omega) - ih (k + 1) (by omega) (by omega)

end nondecreasingDyck_subword_UDU

/-- **Generating functions and closed form for the subword $UDU$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDU}(P)$ be the number of occurrences of the subword $UDU$ in a path $P$, and let
$d_{UDU}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDU}(P)$. Let
$F_{UDU}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDU}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDU}(x) = \sum_{n \ge 0} d_{UDU}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x(2 + y) + x^2 y) F_{UDU}(x, y) = (1 - x) x$ and
$(1 - 3x + x^2)^2 D_{UDU}(x) = x^2 (1 - x)^2$, and for every $n \ge 1$,
$$10\, d_{UDU}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 5
(`jis-2025-25.1.6-thm-5`). -/
public theorem nondecreasingDyck_subword_UDU :
    (1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * nondecreasingDyckSubwordBivariateGF [U, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, U] = 𝒛 ^ 2 * (1 - 𝒛) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, D, U] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) +
          (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ) :=
  ⟨nondecreasingDyck_subword_UDU.bivariate, nondecreasingDyck_subword_UDU.totalGF, fun n hn => by
    have h := nondecreasingDyck_subword_UDU.closed n hn
    unfold nondecreasingDyck_subword_UUU.closedForm at h
    linear_combination h⟩

namespace nondecreasingDyck_subword_U_pow

open nondecreasingDyck_subword_UUU (valleys good_node flat_node enumerator enum_node enum_paths
  enum_empty enum_zero enum_right enum_good_zero emptyWeight rightWeight value slope slope_add
  slope_X slope_F)
open PowerSeries Finset

private abbrev starts (r : ℕ) (l : List DyckStep) : Bool := (List.replicate r U).isPrefixOf l

private abbrev count (r : ℕ) := dyckSubwordCount (List.replicate (r + 1) U)

private lemma starts_append_down (r : ℕ) (l q : List DyckStep) :
    starts r (l ++ D :: q) = starts r l := by
  induction r generalizing l with
  | zero => rfl
  | succ r ih =>
    cases l with
    | nil => rfl
    | cons s l =>
      simp only [starts, List.cons_append, List.replicate_succ, List.isPrefixOf_cons_cons, ih]

private lemma count_zero (r : ℕ) : count r (0 : DyckWord).toList = 0 := rfl

private lemma count_nil (r : ℕ) : count r [] = 0 := rfl

private lemma count_up (r : ℕ) (l : List DyckStep) :
    count r (U :: l) = count r l + (if starts r l then 1 else 0) := by
  simp only [count, dyckSubwordCount, List.tails_cons, List.countP_cons, List.replicate_succ,
    List.isPrefixOf_cons_cons, show (U == U) = true from rfl, Bool.true_and]

private lemma count_down (r : ℕ) (l : List DyckStep) : count r (D :: l) = count r l := rfl

private lemma count_append_down (r : ℕ) (l q : List DyckStep) :
    count r (l ++ D :: q) = count r l + count r q := by
  induction l with
  | nil => simp [count_down, count_nil]
  | cons s l ih =>
    cases s <;> simp [count_up, count_down, starts_append_down, ih, Nat.add_right_comm]

private lemma starts_node (r : ℕ) (p q : DyckWord) :
    starts (r + 1) (p.nest + q).toList = starts r p.toList := by
  change starts (r + 1) ((U :: p.toList ++ [D]) ++ q.toList) = _
  simpa only [starts, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append,
    List.replicate_succ, List.isPrefixOf_cons_cons, show (U == U) = true from rfl,
    Bool.true_and] using starts_append_down r p.toList q.toList

private lemma count_node (r : ℕ) (p q : DyckWord) :
    count r (p.nest + q).toList = count r (U :: p.toList) + count r q.toList := by
  change count r ((U :: p.toList ++ [D]) ++ q.toList) = _
  simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
    count_append_down r (U :: p.toList) q.toList

private abbrev Flat (p : DyckWord) : Prop := valleys 0 p.toList = []

-- The extra initial U records the one possible occurrence starting before the inner path.
private noncomputable def marked (g : DyckWord → Prop) [DecidablePred g]
    (r : ℕ) (prefixed : Bool) (p : DyckWord) : Polynomial ℤ :=
  if g p then Polynomial.X ^ count r (if prefixed then U :: p.toList else p.toList) else 0

private noncomputable def indicator (g : DyckWord → Prop) [DecidablePred g]
    (r : ℕ) (p : DyckWord) : Polynomial ℤ :=
  if g p ∧ starts r p.toList then 1 else 0

private noncomputable def prefixSeries (g : DyckWord → Prop) [DecidablePred g]
    (r : ℕ) : PowerSeries ℤ := value (enumerator (indicator g r))

local notation "A" => prefixSeries IsNondecreasingDyckPath
local notation "B" => prefixSeries Flat
local notation "F" => fun r => nondecreasingDyckSubwordBivariateGF (List.replicate (r + 1) U)
local notation "T" => fun r => nondecreasingDyckSubwordTotalGF (List.replicate (r + 1) U)

private lemma flat_zero : Flat 0 := rfl

private lemma good_zero : IsNondecreasingDyckPath 0 := by decide

private lemma value_X : value 𝒙 = 𝒛 := PowerSeries.map_X _

private lemma value_enum_marked (g : DyckWord → Prop) [DecidablePred g] (r : ℕ) (f : Bool) :
    value (enumerator (marked g r f)) = prefixSeries g 0 := by
  ext1 n
  simp only [prefixSeries, value, coeff_map, enum_paths, map_sum, indicator, marked]
  apply sum_congr rfl
  intro p _
  by_cases h : g p.val <;> simp [h]

private lemma good_series (r : ℕ) :
    enumerator (marked IsNondecreasingDyckPath r false) = 1 + F r :=
  enum_good_zero _ (count_nil r)

private lemma value_F (r : ℕ) : value (F r) = A 0 - 1 := by
  have h := congrArg value (good_series r)
  rw [value_enum_marked, map_add, map_one] at h
  linear_combination -h

private lemma slope_mul (u v : PowerSeries (Polynomial ℤ)) :
    slope (u * v) = slope u * value v + value u * slope v := by
  ext1 n
  simp only [slope, coeff_mk, coeff_mul, map_add, Polynomial.derivative_sum,
    Polynomial.derivative_mul, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_mul,
    value, coeff_map, Polynomial.coe_evalRingHom, sum_add_distrib]

private lemma slope_marked (g : DyckWord → Prop) [DecidablePred g] (r : ℕ) :
    slope (enumerator (marked g r true)) =
      slope (enumerator (marked g r false)) + prefixSeries g r := by
  ext1 n
  simp only [slope, prefixSeries, coeff_mk, value, coeff_map, map_add, enum_paths,
    Polynomial.eval_finsetSum, map_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases h : g p.val <;> by_cases h' : starts r p.val.toList <;>
    simp [marked, indicator, h, h', count_up, Polynomial.derivative_X_pow]

private lemma flat_series (r : ℕ) :
    enumerator (marked Flat r false) = 1 + 𝒙 * enumerator (marked Flat r true) := by
  have h (p q : DyckWord) : marked Flat r false (p.nest + q) =
      marked Flat r true p * emptyWeight q +
        (0 : DyckWord → Polynomial ℤ) p * (0 : DyckWord → Polynomial ℤ) q := by
    simp only [marked, Bool.false_eq_true, ↓reduceIte, flat_node, count_node, Pi.zero_apply,
      mul_zero, add_zero]
    by_cases hq : q = 0
    · subst q
      simp [emptyWeight, count_zero]
    · simp [emptyWeight, hq]
  have h₀ : marked Flat r false 0 = 1 := by simp [marked, flat_zero, count_zero]
  simpa only [enum_empty, enum_zero, h₀, map_one, mul_one, mul_zero, add_zero] using
    enum_node _ _ _ _ _ h

private lemma subword_total_zero (r : ℕ) :
    nondecreasingDyckSubwordTotal (List.replicate (r + 1) U) 0 = 0 := by
  apply sum_eq_zero
  intro p _
  have h := p.val.two_mul_semilength_eq_length
  rw [p.property, mul_zero, eq_comm, List.length_eq_zero_iff, DyckWord.toList_eq_nil] at h
  change count r p.val.toList = 0
  rw [h, count_zero]

private lemma marked_series (r : ℕ) :
    1 + F r = 1 + 𝒙 * (enumerator (marked IsNondecreasingDyckPath r true) +
      enumerator (marked Flat r true) * F r) := by
  have h (p q : DyckWord) : marked IsNondecreasingDyckPath r false (p.nest + q) =
      marked IsNondecreasingDyckPath r true p * emptyWeight q +
        marked Flat r true p * rightWeight (List.replicate (r + 1) U) q := by
    simp only [marked, good_node, count_node, pow_add, emptyWeight, rightWeight,
      Bool.false_eq_true, ↓reduceIte]
    by_cases hq : q = 0
    · subst q
      simp [count_zero]
    · simp only [hq, ite_false, mul_zero, zero_add]
      split_ifs <;> simp_all
  have h₀ : marked IsNondecreasingDyckPath r false 0 = 1 := by
    simp [marked, good_zero, count_zero]
  simpa only [good_series, enum_empty, enum_right, h₀, map_one, mul_one] using
    enum_node _ _ _ _ _ h

private abbrev fibEven (n : ℕ) : ℤ := Nat.fib (2 * n)

private noncomputable def evenFib : PowerSeries ℤ := PowerSeries.mk fibEven

private lemma fib_rec (n : ℕ) : fibEven (n + 2) = 3 * fibEven (n + 1) - fibEven n := by
  have hf (k : ℕ) : (Nat.fib (k + 2) : ℤ) = Nat.fib k + (Nat.fib (k + 1) : ℤ) := by
    rw [Nat.fib_add_two, Nat.cast_add]
  simp only [fibEven, Nat.mul_add, Nat.mul_one, Nat.reduceMul]
  generalize 2 * n = k
  rw [show k + 4 = (k + 2) + 2 from rfl, hf (k + 2), show k + 2 + 1 = (k + 1) + 2 from rfl,
    hf (k + 1), hf k]
  ring

local notation "Q" => (1 - 3 * 𝒛 + 𝒛 ^ 2)

private lemma evenFib_series : Q * evenFib = 𝒛 := by
  have h : Q * evenFib = evenFib - 𝒛 * (3 * evenFib) + 𝒛 * (𝒛 * evenFib) := by ring
  rw [h]
  ext1 n
  obtain _ | _ | n := n
  · simp [evenFib, fibEven]
  · simp [evenFib, fibEven, coeff_succ_X_mul]
  · simp [evenFib, coeff_succ_X_mul, coeff_X, fib_rec n]

-- At y = 1 the UUU enumerator simply counts all the nonempty paths.
private lemma nonempty_series : A 0 - 1 = (1 - 𝒛) * evenFib := by
  have h := congrArg value nondecreasingDyck_subword_UUU.1
  change value ((1 - 𝒙 * (2 + 𝒚) + 𝒙 ^ 2 * 𝒚) * F 2) = value ((1 - 𝒙 * 𝒚) * 𝒙) at h
  have hY : value 𝒚 = 1 := by simp [value, PowerSeries.map_C]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, value_X, hY, mul_one,
    value_F] at h
  have hQ : Q ≠ 0 := by
    intro e
    have := congrArg PowerSeries.constantCoeff e
    simp at this
  apply mul_left_cancel₀ hQ
  linear_combination h - (1 - 𝒛) * evenFib_series

private lemma flat_shape : (1 - 𝒛) * B 0 = 1 := by
  have h := congrArg value (flat_series 0)
  rw [value_enum_marked, map_add, map_one, map_mul, value_X, value_enum_marked] at h
  linear_combination h

private lemma prefix_empty {g : DyckWord → Prop} [DecidablePred g] (r : ℕ) :
    indicator g (r + 1) 0 = 0 := by
  have h : starts (r + 1) (0 : DyckWord).toList = false := rfl
  simp [indicator, h]

private lemma flat_prefix (r : ℕ) : B (r + 1) = 𝒛 * B r := by
  have h (p q : DyckWord) : indicator Flat (r + 1) (p.nest + q) =
      indicator Flat r p * emptyWeight q +
        (0 : DyckWord → Polynomial ℤ) p * (0 : DyckWord → Polynomial ℤ) q := by
    simp only [indicator, flat_node, starts_node, Pi.zero_apply, mul_zero, add_zero]
    by_cases hq : q = 0 <;> simp [emptyWeight, hq]
  have h' := congrArg value (enum_node _ _ _ _ _ h)
  simpa only [prefix_empty, map_zero, zero_add, enum_empty, enum_zero, mul_one, mul_zero,
    add_zero, map_mul, value_X, prefixSeries] using h'

private lemma flat_prefix_pow (r : ℕ) : B r = 𝒛 ^ r * B 0 := by
  induction r with
  | zero => simp
  | succ r ih => rw [flat_prefix, ih, pow_succ']; ring

private lemma good_prefix (r : ℕ) : A (r + 1) = 𝒛 * (A r + B r * (A 0 - 1)) := by
  -- Only the value at y = 1 matters; use a constant nonempty weight in the node equation.
  let nonempty : DyckWord → Polynomial ℤ := fun q =>
    if q ≠ 0 ∧ IsNondecreasingDyckPath q then 1 else 0
  have hnode (p q : DyckWord) : indicator IsNondecreasingDyckPath (r + 1) (p.nest + q) =
      indicator IsNondecreasingDyckPath r p * emptyWeight q + indicator Flat r p * nonempty q := by
    simp only [indicator, good_node, starts_node, emptyWeight, nonempty]
    by_cases hq : q = 0
    · simp [hq]
    · simp only [hq, ite_false, mul_zero, zero_add, ne_eq, not_false_eq_true, true_and]
      split_ifs <;> simp_all
  have hn : value (enumerator nonempty) = A 0 - 1 := by
    rw [← value_F 0]
    change value (enumerator nonempty) = value (nondecreasingDyckSubwordBivariateGF [U])
    rw [← enum_right]
    ext1 n
    simp only [value, coeff_map, enum_paths, map_sum]
    apply sum_congr rfl
    intro p _
    by_cases hq : p.val = 0 <;> by_cases hg : IsNondecreasingDyckPath p.val <;>
      simp [nonempty, rightWeight, hq, hg]
  have eq := congrArg value (enum_node _ _ _ _ _ hnode)
  simpa only [prefix_empty, map_zero, zero_add, enum_empty, mul_one, map_mul, map_add,
    value_X, hn, prefixSeries] using eq

private lemma good_prefix_pow (r : ℕ) :
    A r = 𝒛 ^ r * (A 0 + (r : ℤ) * B 0 * (A 0 - 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [good_prefix, ih, flat_prefix_pow r, pow_succ', Nat.cast_succ, Int.cast_add, Int.cast_one]
    ring

private lemma flat_slope (r : ℕ) :
    (1 - 𝒛) * slope (enumerator (marked Flat r true)) = B r := by
  have h := congrArg slope (flat_series r)
  rw [slope_add, slope_X, nondecreasingDyck_subword_UUU.slope_one, zero_add] at h
  linear_combination h + slope_marked Flat r

private lemma up_run_series (r : ℕ) : Q * T r =
    𝒛 ^ (r + 1) * ((r : ℤ) + 1 + (1 - (r : ℤ)) * 𝒛) * evenFib + 𝒛 ^ (r + 1) := by
  let P := slope (enumerator (marked Flat r true))
  have d := congrArg slope (marked_series r)
  simp only [slope_add, nondecreasingDyck_subword_UUU.slope_one, zero_add] at d
  rw [slope_X] at d
  simp only [slope_add, slope_mul, value_enum_marked, value_F,
    slope_F _ (subword_total_zero r)] at d
  rw [slope_marked IsNondecreasingDyckPath r, good_series, slope_add,
    nondecreasingDyck_subword_UUU.slope_one, zero_add, slope_F _ (subword_total_zero r)] at d
  change T r = 𝒛 * (T r + A r + (P * (A 0 - 1) + B 0 * T r)) at d
  have h : Q * T r = (1 - 𝒛) * 𝒛 * A r + 𝒛 * B r * (A 0 - 1) := by
    linear_combination (1 - 𝒛) * d + 𝒛 * (T r) * flat_shape +
      𝒛 * (A 0 - 1) * flat_slope r
  rw [h, good_prefix_pow r, flat_prefix_pow r, pow_succ']
  have hA : A 0 = 1 + (1 - 𝒛) * evenFib := by linear_combination nonempty_series
  rw [hA]
  linear_combination (𝒛 * 𝒛 ^ r) * ((r : ℤ) * (1 - 𝒛) + 1) * evenFib * flat_shape +
    (𝒛 * 𝒛 ^ r) * evenFib_series

-- The paper's finite Fibonacci sum telescopes using the even-index recurrence.
private lemma fib_sum_telescopes (r n : ℕ) (h : r + 1 < n) :
    fibEven (n - 2) - ∑ k ∈ Icc 1 (r - 1), (k : ℤ) * fibEven (n - k - 2) =
      (r : ℤ) * fibEven (n - (r + 1)) + (1 - (r : ℤ)) * fibEven (n - (r + 2)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    cases r with
    | zero => simp
    | succ r =>
      have hi := ih (by omega)
      have he : Icc 1 (r + 1) = insert (r + 1) (Icc 1 r) := by
        ext k
        simp only [mem_insert, mem_Icc]
        omega
      have hn : r + 1 ∉ Icc 1 r := by simp
      have hf := fib_rec (n - (r + 4))
      rw [show n - (r + 4) + 2 = n - (r + 2) by omega,
        show n - (r + 4) + 1 = n - (r + 3) by omega] at hf
      simp only [Nat.add_sub_cancel, he, sum_insert hn, Nat.cast_succ] at hi ⊢
      rw [show n - (r + 1) - 2 = n - (r + 3) by omega,
        show r + 1 + 1 + 1 = r + 3 by omega, show r + 1 + 1 + 2 = r + 4 by omega]
      rw [show r + 1 + 1 = r + 2 by omega, show r + 1 + 2 = r + 3 by omega] at hi
      linear_combination hi + ((r : ℤ) + 1) * hf

private abbrev total (r n : ℕ) : ℤ := nondecreasingDyckSubwordTotal (List.replicate (r + 1) U) n

private lemma coeff_total (r n : ℕ) : coeff n (T r) = total r n := by
  simp [nondecreasingDyckSubwordTotalGF]

private lemma coeff_recurrence (r n : ℕ) :
    coeff n (Q * T r) = total r n - 3 * total r (n - 1) + total r (n - 2) := by
  have h : Q * T r = T r - 𝒛 * (3 * T r) + 𝒛 * (𝒛 * T r) := by ring
  rw [h]
  obtain _ | _ | n := n
  · simp [nondecreasingDyckSubwordTotalGF, total, subword_total_zero]
  · simp [coeff_succ_X_mul, coeff_total, total, subword_total_zero]
  · simp [coeff_succ_X_mul, coeff_total]

private lemma coeff_shift_fib (m n : ℕ) : coeff n (𝒛 ^ m * evenFib) = fibEven (n - m) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [evenFib]
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    rfl

private lemma recurrence (r n : ℕ) : total r n - 3 * total r (n - 1) + total r (n - 2) =
    (if n = r + 1 then 1 else 0) +
      ((r : ℤ) + 1) * fibEven (n - (r + 1)) + (1 - (r : ℤ)) * fibEven (n - (r + 2)) := by
  have h : Q * T r = 𝒛 ^ (r + 1) + C ((r : ℤ) + 1) * (𝒛 ^ (r + 1) * evenFib) +
      C (1 - (r : ℤ)) * (𝒛 ^ (r + 2) * evenFib) := by
    rw [up_run_series, map_add, map_sub, map_one, pow_succ' 𝒛 (r + 1)]
    have hc : C (r : ℤ) = ((r : ℤ) : PowerSeries ℤ) := map_intCast C r
    rw [hc]
    ring
  have e := congrArg (coeff n) h
  rwa [coeff_recurrence, map_add, map_add, coeff_X_pow, coeff_C_mul, coeff_C_mul,
    coeff_shift_fib, coeff_shift_fib] at e

private lemma below (r n : ℕ) (hn : n < r + 1) : total r n = 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h : n = 0
    · subst n
      exact_mod_cast subword_total_zero r
    · have e := recurrence r n
      rw [ite_eq_right (by omega), Nat.sub_eq_zero_of_le (show n ≤ r + 1 by omega),
        Nat.sub_eq_zero_of_le (show n ≤ r + 2 by omega), ih (n - 1) (by omega) (by omega),
        ih (n - 2) (by omega) (by omega)] at e
      simpa [fibEven] using e

private lemma diagonal (r : ℕ) : total r (r + 1) = 1 := by
  have h := recurrence r (r + 1)
  rw [below r (r + 1 - 1) (by omega), below r (r + 1 - 2) (by omega),
    Nat.sub_eq_zero_of_le (show r + 1 ≤ r + 2 by omega)] at h
  simpa [fibEven] using h

private lemma above (r n : ℕ) (h : r + 1 < n) : total r n =
    3 * total r (n - 1) - total r (n - 2) + fibEven (n - (r + 1)) + fibEven (n - 2)
      - ∑ k ∈ Icc 1 (r - 1), (k : ℤ) * fibEven (n - k - 2) := by
  have e := recurrence r n
  rw [ite_eq_right (by omega), zero_add] at e
  linear_combination e - fib_sum_telescopes r n h

end nondecreasingDyck_subword_U_pow

/-- **Recurrence for the subword $U^m$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n > m$,
$$d_{U^m}(n) = 3\,d_{U^m}(n-1) - d_{U^m}(n-2) + F_{2(n-m)} + F_{2(n-2)} -
\sum_{k=1}^{m-2} k\,F_{2(n-k-2)}$$
(the sum is empty when $m \le 2$); moreover $d_{U^m}(n) = 0$ for every $n < m$, and
$d_{U^m}(m) = 1$.

The source writes $n \le m$ for the vanishing case, which contradicts $d_{U^m}(m) = 1$; the
vanishing case is stated for $n < m$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 13
(`jis-2025-25.1.6-thm-13`). -/
public theorem nondecreasingDyck_subword_U_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n →
      (nondecreasingDyckSubwordTotal (List.replicate m U) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m)) : ℤ) + (Nat.fib (2 * (n - 2)) : ℤ)
          - ∑ k ∈ Finset.Icc 1 (m - 2), (k : ℤ) * (Nat.fib (2 * (n - k - 2)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U) m = 1 := by
  obtain _ | r := m
  · omega
  refine ⟨fun n hn => nondecreasingDyck_subword_U_pow.above r n hn, ?_, ?_⟩
  · intro n hn
    exact_mod_cast nondecreasingDyck_subword_U_pow.below r n hn
  · exact_mod_cast nondecreasingDyck_subword_U_pow.diagonal r

end

end MetaMathlibExt
