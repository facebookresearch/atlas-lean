/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Basic

import Mathlib.Data.Finset.Max

/-!
# The threshold algorithm for top-k aggregation

A database of `N` objects of a type `α` with `m` attributes is given by sorted lists
(`GradedLists`): `grade i x ∈ [0, 1]` is the grade of the object `x` under the attribute `i`, and
the list of attribute `i` holds every object exactly once, in nonincreasing order of grade, equal
grades in any order. The aggregate grade of an object is `t (grade · x)` for an aggregation
function `t : (Fin m → ℝ) → ℝ` (`GradedLists.aggregate`).

A top-`k` answer (`IsTopK`) is a set of exactly `k` objects each of which has aggregate grade at
least that of every object outside it; ties may be resolved either way, and no tie-breaking order
is fixed.

The threshold algorithm (TA) of Fagin, Lotem and Naor reads the lists by sorted access in parallel,
one round per position, and finds every grade of each object it reads by random access. A run of it
(`GradedLists.ThresholdRun`) is the sequence of its buffers: the buffer is empty before the first
round, and round `d + 1` reads the objects at position `d` of the lists (`GradedLists.row`) and
keeps `k` objects of highest aggregate grade among the old buffer and the objects just read, or all
of them if there are fewer than `k`, resolving ties arbitrarily (`IsTopKAmong`). Every choice of
ties gives a run, and runs exist (the `Nonempty` instance). After round `p + 1` the threshold is `t`
applied to the grades at position `p` of the lists, the last grades read (`GradedLists.threshold`),
and the stopping rule holds once the buffer holds `k` objects of aggregate grade at least the
threshold (`GradedLists.ThresholdRun.StoppingRuleHolds`). TA halts at the first such round and
returns its buffer. The source states the rule for all objects seen, not only the buffered ones: at
least `k` objects seen have aggregate grade at least the threshold. The two forms agree
(`GradedLists.ThresholdRun.stoppingRuleHolds_iff_seen`); with the buffered form, every decision of
the algorithm depends only on its buffer and the round.

## Main results

* `GradedLists.ThresholdRun.isTopKAmong_seen`: after every round the buffer holds `k` objects of
  highest aggregate grade among all objects read so far (`GradedLists.seen`), or all of them.
* `GradedLists.ThresholdRun.card_buf_le`: the buffer never holds more than `k` objects.
* `GradedLists.ThresholdRun.stoppingRuleHolds_iff_seen`: the stopping rule holds exactly when at
  least `k` objects seen have aggregate grade at least the threshold, the source's form of it.
* `GradedLists.ThresholdRun.exists_stoppingRuleHolds`: when `t` is monotone on `[0, 1]^m`,
  `m ≥ 1` and `1 ≤ k ≤ N`, the stopping rule holds after some round `p + 1 ≤ N`.
* `GradedLists.ThresholdRun.isTopK_of_stoppingRuleHolds`: when `t` is monotone on `[0, 1]^m`,
  the buffer is a top-`k` answer after every round at which the stopping rule holds, in
  particular after the first.
* `thresholdAlgorithm_correct` gathers these five facts.

## References

* R. Fagin, A. Lotem and M. Naor, *Optimal aggregation algorithms for middleware*, J. Comput.
  System Sci. 66 (2003), 614–656; arXiv:cs/0204046, Section 1 (the model; ties broken
  arbitrarily), Section 2 (sorted and random access) and Section 4 (the threshold algorithm,
  Theorems 4.1 and 4.2).
-/

@[expose] public section

namespace Cslib.Databases

variable {α β : Type*}

section TopK

variable [LinearOrder β]

/-- **Top-k answer.** Let $f$ assign to each object a score in a linearly ordered set, and let
$k \in \mathbb{N}$. A finite set $Y$ of objects is a top-$k$ answer for $f$ when it has exactly
$k$ elements and $f(z) \le f(y)$ for every $y \in Y$ and every object $z \notin Y$. Objects with
equal scores may fall on either side of $Y$: no tie-breaking order is fixed, and there may be
several top-$k$ answers. -/
def IsTopK (f : α → β) (k : ℕ) (Y : Finset α) : Prop :=
  Y.card = k ∧ ∀ y ∈ Y, ∀ z, z ∉ Y → f z ≤ f y

/-- **Top-k choice among a finite set.** Let $f$ assign to each object a score in a linearly ordered
set, let $k \in \mathbb{N}$ and let $S$ be a finite set of objects. A set $B$ is a top-$k$ choice
among $S$ for $f$ when $B \subseteq S$, $B$ has $\min(k, |S|)$ elements, and $f(z) \le f(y)$ for
every $y \in B$ and every $z \in S \setminus B$. So $B$ consists of $k$ elements of $S$ of highest
score, or of all of $S$ when $|S| \le k$; ties may be resolved either way. -/
def IsTopKAmong (f : α → β) (k : ℕ) (S B : Finset α) : Prop :=
  B ⊆ S ∧ B.card = min k S.card ∧ ∀ y ∈ B, ∀ z ∈ S, z ∉ B → f z ≤ f y

namespace IsTopKAmong

variable {f : α → β} {k : ℕ} {S B : Finset α}

theorem card_le (h : IsTopKAmong f k S B) : B.card ≤ k :=
  h.2.1 ▸ min_le_left _ _

theorem empty : IsTopKAmong f k ∅ ∅ :=
  ⟨subset_rfl, by simp, by simp⟩

-- A top-`k` choice among the old choice and new elements `R` is a top-`k` choice among all elements
-- seen. This is the step that lets the threshold algorithm keep only its buffer.
theorem union [DecidableEq α] {R B' : Finset α} (hB : IsTopKAmong f k S B)
    (hB' : IsTopKAmong f k (B ∪ R) B') : IsTopKAmong f k (S ∪ R) B' := by
  obtain ⟨hBS, hBc, hBd⟩ := hB
  obtain ⟨hB'sub, hB'c, hB'd⟩ := hB'
  by_cases hSB : S ⊆ B
  · obtain rfl : B = S := subset_antisymm hBS hSB
    exact ⟨hB'sub, hB'c, hB'd⟩
  have hlt : B.card < S.card := Finset.card_lt_card ⟨hBS, hSB⟩
  have hBk : B.card = k := by omega
  have hBR : B.card ≤ (B ∪ R).card := Finset.card_le_card Finset.subset_union_left
  have hSR : S.card ≤ (S ∪ R).card := Finset.card_le_card Finset.subset_union_left
  have hB'k : B'.card = k := by omega
  refine ⟨hB'sub.trans (Finset.union_subset_union hBS subset_rfl), by omega, ?_⟩
  intro y hy z hz hzB'
  by_cases hzBR : z ∈ B ∪ R
  · exact hB'd y hy z hzBR hzB'
  have hzB : z ∉ B := fun h => hzBR (Finset.mem_union_left _ h)
  have hzS : z ∈ S := by
    rcases Finset.mem_union.1 hz with h | h
    · exact h
    · exact absurd (Finset.mem_union_right _ h) hzBR
  by_cases hyB : y ∈ B
  · exact hBd y hyB z hzS hzB
  -- `y` entered the buffer, so some `b ∈ B` left it, and `f z ≤ f b ≤ f y`.
  have hnot : ¬ B ⊆ B' := fun hsub =>
    hyB (Finset.eq_of_subset_of_card_le hsub (by omega) ▸ hy)
  obtain ⟨b, hbB, hbB'⟩ := Finset.not_subset.1 hnot
  exact (hBd b hbB z hzS hzB).trans (hB'd y hy b (Finset.mem_union_left _ hbB) hbB')

end IsTopKAmong

-- Every finite set has a top-`k` choice.
theorem exists_isTopKAmong (f : α → β) (k : ℕ) (S : Finset α) : ∃ B, IsTopKAmong f k S B := by
  classical
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨B, hBS, hBc, hBd⟩ := ih
    by_cases hne : (S \ B).Nonempty
    · obtain ⟨z, hz, hzmax⟩ := Finset.exists_max_image (S \ B) f hne
      rw [Finset.mem_sdiff] at hz
      have hlt : B.card < S.card := Finset.card_lt_card ⟨hBS, fun h => hz.2 (h hz.1)⟩
      refine ⟨insert z B, Finset.insert_subset hz.1 hBS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hz.2]
        omega
      · intro y hy w hw hwy
        rw [Finset.mem_insert, not_or] at hwy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hzmax w (Finset.mem_sdiff.2 ⟨hw, hwy.2⟩)
        · exact hBd y hy w hw hwy.2
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
      obtain rfl : B = S := subset_antisymm hBS hne
      exact ⟨B, subset_rfl, by omega, fun y _ z hz hzB => absurd hz hzB⟩

end TopK

/-- **Graded sorted lists.** A database of $N$ objects of a type $\alpha$ with $m$ attributes,
presented as $m$ sorted lists. The type $\alpha$ has exactly $N$ elements; when $m \ge 1$ this
also follows from the lists. Each object $x$ has a grade $x_i \in [0, 1]$ under each attribute
$i$. The list of attribute $i$ holds every object exactly once, as a bijection from the
positions $0, \ldots, N - 1$ to the objects, and its grades are nonincreasing along the
positions; objects with equal grades may appear in any order. Sorted access reads a list
position by position; random access gives the grade of any object under any attribute. -/
structure GradedLists (α : Type*) (N m : ℕ) where
  /-- The grade of each object under each attribute. -/
  grade : Fin m → α → ℝ
  /-- Every grade lies in `[0, 1]`. -/
  grade_mem_Icc : ∀ i x, grade i x ∈ Set.Icc (0 : ℝ) 1
  /-- The sorted list of each attribute: the object at each position. -/
  list : Fin m → Fin N ≃ α
  /-- Each list is in nonincreasing order of grade. -/
  antitone_grade : ∀ i, Antitone fun p => grade i (list i p)
  /-- There are exactly `N` objects, even when there is no list. -/
  nonempty_equiv_fin : Nonempty (Fin N ≃ α)

namespace GradedLists

variable {N m : ℕ} (D : GradedLists α N m)

/-- **Aggregate grade.** For graded sorted lists with $m$ attributes and an aggregation function
$t : \mathbb{R}^m \to \mathbb{R}$, the aggregate grade of an object $x$ with grades
$x_1, \ldots, x_m$ is $t(x_1, \ldots, x_m)$. -/
def aggregate (t : (Fin m → ℝ) → ℝ) (x : α) : ℝ :=
  t fun i => D.grade i x

/-- **Threshold value.** For graded sorted lists with $m$ attributes, an aggregation function
$t$ and a position $p$, the threshold after the lists have been read down to position $p$ is
$t(\underline{x}_1, \ldots, \underline{x}_m)$, where $\underline{x}_i$ is the grade of the object
at position $p$ of list $i$, the last grade read from that list. -/
def threshold (t : (Fin m → ℝ) → ℝ) (p : Fin N) : ℝ :=
  t fun i => D.grade i (D.list i p)

theorem grade_list_mem_Icc (x : Fin m → α) : (fun i => D.grade i (x i)) ∈ Set.Icc 0 1 :=
  ⟨fun i => (D.grade_mem_Icc i (x i)).1, fun i => (D.grade_mem_Icc i (x i)).2⟩

-- After the last position every object has aggregate grade at least the threshold.
theorem threshold_le_aggregate_of_last {t : (Fin m → ℝ) → ℝ} (ht : MonotoneOn t (Set.Icc 0 1))
    {p : Fin N} (hp : (p : ℕ) + 1 = N) (x : α) : D.threshold t p ≤ D.aggregate t x := by
  refine ht (D.grade_list_mem_Icc fun i => D.list i p) (D.grade_list_mem_Icc fun _ => x)
    fun i => ?_
  have hpi : (D.list i).symm x ≤ p :=
    Fin.le_iff_val_le_val.2 (by have := ((D.list i).symm x).isLt; omega)
  simpa using D.antitone_grade i hpi

variable [DecidableEq α]

/-- **Row of graded sorted lists.** For graded sorted lists of $N$ objects and $d \in \mathbb{N}$,
the objects at position $d$ (counting from $0$) of some list: those read by the $(d + 1)$st round
of sorted access in parallel. The lists have no position $d \ge N$, so the row is then empty. -/
def row (d : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin m × Fin N)).filter fun ip => (ip.2 : ℕ) = d).image
    fun ip => D.list ip.1 ip.2

/-- **Objects seen in the first rounds.** For graded sorted lists and $d \in \mathbb{N}$, the
objects at a position below $d$ of some list: those read by the first $d$ rounds of sorted
access in parallel. -/
def seen (d : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin m × Fin N)).filter fun ip => (ip.2 : ℕ) < d).image
    fun ip => D.list ip.1 ip.2

variable {D}

theorem mem_row {d : ℕ} {x : α} : x ∈ D.row d ↔ ∃ i, ((D.list i).symm x : ℕ) = d := by
  simp only [row, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨i, p, hp, rfl⟩
    exact ⟨i, by simpa using hp⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (D.list i).symm x, hi, by simp⟩

theorem mem_seen {d : ℕ} {x : α} : x ∈ D.seen d ↔ ∃ i, ((D.list i).symm x : ℕ) < d := by
  simp only [seen, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨i, p, hp, rfl⟩
    exact ⟨i, by simpa using hp⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (D.list i).symm x, hi, by simp⟩

variable (D) in
theorem seen_zero : D.seen 0 = ∅ := by
  ext x
  simp [mem_seen]

variable (D) in
theorem seen_succ (d : ℕ) : D.seen (d + 1) = D.seen d ∪ D.row d := by
  ext x
  simp only [Finset.mem_union, mem_seen, mem_row, ← exists_or]
  exact exists_congr fun i => by omega

-- An object not read in the first `p + 1` rounds has aggregate grade at most the threshold after
-- them.
theorem aggregate_le_threshold_of_notMem_seen {t : (Fin m → ℝ) → ℝ}
    (ht : MonotoneOn t (Set.Icc 0 1)) {p : Fin N} {x : α} (hx : x ∉ D.seen ((p : ℕ) + 1)) :
    D.aggregate t x ≤ D.threshold t p := by
  refine ht (D.grade_list_mem_Icc fun _ => x) (D.grade_list_mem_Icc fun i => D.list i p)
    fun i => ?_
  have hpi : p ≤ (D.list i).symm x := by
    rw [mem_seen, not_exists] at hx
    exact Fin.le_iff_val_le_val.2 (by have := hx i; omega)
  simpa using D.antitone_grade i hpi

variable (D) in
/-- **Run of the threshold algorithm.** For graded sorted lists, an aggregation function $t$ and
$k \in \mathbb{N}$, a run of the threshold algorithm is a sequence of buffers $B_0, B_1, \ldots$
of objects, $B_d$ being the buffer after $d$ rounds of sorted access in parallel. The buffer
$B_0$ is empty, and round $d + 1$ reads the objects at position $d$ of the lists, finds their
aggregate grades by random access, and keeps as $B_{d+1}$ a top-$k$ choice for the aggregate
grade among $B_d$ and the objects just read: $k$ of them of highest aggregate grade, or all of
them if there are fewer than $k$. Ties are resolved arbitrarily, so each choice of ties gives a
run. -/
structure ThresholdRun (t : (Fin m → ℝ) → ℝ) (k : ℕ) where
  /-- The buffer after each number of rounds. -/
  buf : ℕ → Finset α
  /-- The buffer is empty before the first round. -/
  buf_zero : buf 0 = ∅
  /-- Each round keeps a top-`k` choice among the old buffer and the objects it reads. -/
  buf_succ : ∀ d, IsTopKAmong (D.aggregate t) k (buf d ∪ D.row d) (buf (d + 1))

namespace ThresholdRun

variable {t : (Fin m → ℝ) → ℝ} {k : ℕ}

/-- Runs exist: ties can always be resolved, so statements about all runs are not vacuous. -/
instance : Nonempty (D.ThresholdRun t k) := by
  classical
  let buf : ℕ → Finset α := fun d => Nat.rec ∅
    (fun d B => Classical.choose (exists_isTopKAmong (D.aggregate t) k (B ∪ D.row d))) d
  exact ⟨⟨buf, rfl, fun d => Classical.choose_spec (exists_isTopKAmong _ _ _)⟩⟩

/-- **Stopping rule of the threshold algorithm.** For a run of the threshold algorithm with
buffers $B_0, B_1, \ldots$ and a position $p$, the stopping rule holds after round $p + 1$ when
the buffer $B_{p+1}$ holds at least $k$ objects whose aggregate grade is at least the threshold
$\tau = t(\underline{x}_1, \ldots, \underline{x}_m)$, where $\underline{x}_i$ is the grade at
position $p$ of list $i$. Fagin, Lotem and Naor state the rule for all objects seen: at least $k$
of the objects seen in the first $p + 1$ rounds have aggregate grade at least $\tau$. Since the
buffer $B_{p+1}$ is a top-$k$ choice among those objects, the two forms hold for the same rounds;
with the buffered form, every decision of the algorithm depends only on its buffer and the round.
The algorithm halts at the first round at which the stopping rule holds and returns its buffer;
the rule may go on holding after that round. -/
def StoppingRuleHolds (r : D.ThresholdRun t k) (p : Fin N) : Prop :=
  k ≤ ((r.buf ((p : ℕ) + 1)).filter fun x => D.threshold t p ≤ D.aggregate t x).card

-- After `d` rounds the buffer is a top-`k` choice among all objects read so far.
theorem isTopKAmong_seen (r : D.ThresholdRun t k) (d : ℕ) :
    IsTopKAmong (D.aggregate t) k (D.seen d) (r.buf d) := by
  induction d with
  | zero => rw [r.buf_zero, D.seen_zero]; exact IsTopKAmong.empty
  | succ d ih => rw [D.seen_succ]; exact ih.union (r.buf_succ d)

-- The buffer never holds more than `k` objects.
theorem card_buf_le (r : D.ThresholdRun t k) (d : ℕ) : (r.buf d).card ≤ k :=
  (r.isTopKAmong_seen d).card_le

-- The stopping rule in the source's form: at least `k` objects seen in the first `p + 1` rounds
-- have aggregate grade at least the threshold. It agrees with the buffered form, as the buffer is a
-- top-`k` choice among the objects seen.
theorem stoppingRuleHolds_iff_seen (r : D.ThresholdRun t k) (p : Fin N) :
    r.StoppingRuleHolds p ↔
      k ≤ ((D.seen ((p : ℕ) + 1)).filter fun x => D.threshold t p ≤ D.aggregate t x).card := by
  obtain ⟨hsub, hc, hdom⟩ := r.isTopKAmong_seen ((p : ℕ) + 1)
  unfold StoppingRuleHolds
  refine ⟨fun h => h.trans (Finset.card_le_card (Finset.filter_subset_filter _ hsub)), fun h => ?_⟩
  have hS := h.trans (Finset.card_filter_le (D.seen ((p : ℕ) + 1))
    fun x => D.threshold t p ≤ D.aggregate t x)
  have hB : (r.buf ((p : ℕ) + 1)).card = k := by omega
  by_cases hall : ∀ y ∈ r.buf ((p : ℕ) + 1), D.threshold t p ≤ D.aggregate t y
  · rw [Finset.filter_true_of_mem hall, hB]
  push Not at hall
  obtain ⟨y, hyB, hy⟩ := hall
  -- Every object seen with aggregate grade at least the threshold is buffered, and is not `y`.
  have hsubB : (D.seen ((p : ℕ) + 1)).filter (fun x => D.threshold t p ≤ D.aggregate t x) ⊆
      (r.buf ((p : ℕ) + 1)).erase y := by
    intro x hx
    rw [Finset.mem_filter] at hx
    refine Finset.mem_erase.2 ⟨fun hxy => absurd hx.2 (not_le.2 (hxy ▸ hy)), ?_⟩
    by_contra hxB
    exact absurd hx.2 (not_le.2 ((hdom y hyB x hx.1 hxB).trans_lt hy))
  have := Finset.card_le_card hsubB
  rw [Finset.card_erase_of_mem hyB] at this
  omega

-- The buffer is a top-`k` answer after every round at which the stopping rule holds.
theorem isTopK_of_stoppingRuleHolds (ht : MonotoneOn t (Set.Icc 0 1)) (r : D.ThresholdRun t k)
    {p : Fin N} (hp : r.StoppingRuleHolds p) : IsTopK (D.aggregate t) k (r.buf ((p : ℕ) + 1)) := by
  obtain ⟨-, -, hdom⟩ := r.isTopKAmong_seen ((p : ℕ) + 1)
  have hcard := r.card_buf_le ((p : ℕ) + 1)
  have hfilt := Finset.card_filter_le (r.buf ((p : ℕ) + 1))
    fun x => D.threshold t p ≤ D.aggregate t x
  unfold StoppingRuleHolds at hp
  have hall := Finset.filter_card_eq (p := fun x => D.threshold t p ≤ D.aggregate t x)
    (s := r.buf ((p : ℕ) + 1)) (by omega)
  refine ⟨by omega, fun y hy z hz => ?_⟩
  by_cases hzs : z ∈ D.seen ((p : ℕ) + 1)
  · exact hdom y hy z hzs hz
  · exact (aggregate_le_threshold_of_notMem_seen ht hzs).trans (hall y hy)

-- With at least one list and `1 ≤ k ≤ N`, the stopping rule holds after some round `p + 1 ≤ N`; at
-- the latest after round `N`.
theorem exists_stoppingRuleHolds (ht : MonotoneOn t (Set.Icc 0 1)) (hm : 0 < m) (hk : 0 < k)
    (hkN : k ≤ N) (r : D.ThresholdRun t k) : ∃ p, r.StoppingRuleHolds p := by
  have hN : 0 < N := hk.trans_le hkN
  let p : Fin N := ⟨N - 1, by omega⟩
  have hp : (p : ℕ) + 1 = N := by simp only [p]; omega
  refine ⟨p, ?_⟩
  obtain ⟨-, hc, -⟩ := r.isTopKAmong_seen ((p : ℕ) + 1)
  have hsub : Finset.univ.image (D.list ⟨0, hm⟩) ⊆ D.seen ((p : ℕ) + 1) := by
    intro x _
    rw [mem_seen, hp]
    exact ⟨⟨0, hm⟩, ((D.list ⟨0, hm⟩).symm x).isLt⟩
  have hNS : N ≤ (D.seen ((p : ℕ) + 1)).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (D.list _).injective, Finset.card_univ,
      Fintype.card_fin] at this
  have hbk : (r.buf ((p : ℕ) + 1)).card = k := by omega
  unfold StoppingRuleHolds
  rw [Finset.filter_true_of_mem fun x _ => D.threshold_le_aggregate_of_last ht hp x, hbk]

end ThresholdRun

end GradedLists

open GradedLists in
/-- **Correctness of the threshold algorithm for top-k aggregation.** Let there be graded sorted
lists of $N$ objects with $m \ge 1$ attributes and grades in $[0, 1]$, let $1 \le k \le N$, and
let the aggregation function $t$ be nondecreasing in each coordinate on $[0, 1]^m$. Then every
run of the threshold algorithm, whatever its resolution of ties, has these properties.
1. After each number $d$ of rounds of sorted access in parallel, its buffer is a top-$k$ choice
   for the aggregate grade among the objects seen in those rounds: $k$ of them of highest
   aggregate grade, or all of them if fewer than $k$ have been seen.
2. Its buffer never holds more than $k$ objects, however large $N$ is.
3. The stopping rule after a round (at least $k$ buffered objects have aggregate grade at least
   the threshold $\tau = t(\underline{x}_1, \ldots, \underline{x}_m)$ of the last grades read)
   holds exactly when at least $k$ of the objects seen so far have aggregate grade at least
   $\tau$, the form in which Fagin, Lotem and Naor state it.
4. The stopping rule holds after some round $p + 1 \le N$.
5. After every round at which the stopping rule holds, in particular the first, at which the
   algorithm halts, the buffer is a top-$k$ answer: it holds exactly $k$ objects, each of
   aggregate grade at least that of every object outside the buffer. -/
theorem thresholdAlgorithm_correct {N m k : ℕ} [DecidableEq α] (D : GradedLists α N m)
    {t : (Fin m → ℝ) → ℝ} (ht : MonotoneOn t (Set.Icc 0 1)) (hm : 0 < m) (hk : 0 < k)
    (hkN : k ≤ N) (r : D.ThresholdRun t k) :
    (∀ d, IsTopKAmong (D.aggregate t) k (D.seen d) (r.buf d)) ∧
      (∀ d, (r.buf d).card ≤ k) ∧
      (∀ p, r.StoppingRuleHolds p ↔
        k ≤ ((D.seen ((p : ℕ) + 1)).filter fun x => D.threshold t p ≤ D.aggregate t x).card) ∧
      (∃ p, r.StoppingRuleHolds p) ∧
      ∀ p, r.StoppingRuleHolds p → IsTopK (D.aggregate t) k (r.buf ((p : ℕ) + 1)) :=
  ⟨r.isTopKAmong_seen, r.card_buf_le, r.stoppingRuleHolds_iff_seen,
    r.exists_stoppingRuleHolds ht hm hk hkN, fun _ hp => r.isTopK_of_stoppingRuleHolds ht hp⟩

end Cslib.Databases
