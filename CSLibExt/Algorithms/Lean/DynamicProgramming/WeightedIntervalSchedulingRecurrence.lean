/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalScheduling
public import CSLibExt.Algorithms.Lean.Greedy.IntervalScheduling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Disjoint

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Monotone
import Mathlib.Data.List.Sort

/-!
# Weighted interval scheduling by dynamic programming

Intervals are indexed by the positive integers `1, …, n`. Interval `i` has start time `start i` and
finish time `finish i` in a linear order and a weight `weight i` in a linearly ordered commutative
additive monoid whose addition is monotone, such as `ℕ`, `ℤ` or `ℝ`; the weights need no sign
condition. Values at indices outside `1, …, n` are never used. Compatibility is
`Cslib.Algorithms.Lean.TimeM.IntervalCompatible`, the relation of the unweighted
interval-scheduling API: one interval finishes no later than the other starts. For intervals of
positive length this is disjointness of the closed-open intervals
(`intervalCompatible_iff_disjoint_Ico`).

For intervals of positive length ordered by finish time, `wisPred` is the index `p(j)` of the last
interval that finishes by the start of interval `j`, `wisValue` is the recurrence
`OPT(j) = max (OPT(j - 1)) (w(j) + OPT(p(j)))`, and `wisTrace` traces back which term attains each
maximum. `wisSchedule` is the algorithm on unsorted input: it sorts the indices by finish time with
CSLib's monadic merge sort, fills the table bottom-up while computing each `p(j)` by binary search
(`wisTable`, `predSearch`), and traces back (`wisTraceback`).

The cost model charges one unit for each comparison of two times, in the merge sort and in the
binary searches, and one unit for each comparison of two weights, one per table entry and one per
traceback step. Nothing else is charged: additions of weights, array and list operations, and
index arithmetic are free. The sorted order is stored in an array, as in the unweighted module, so
that reading the `j`-th interval of the order takes constant time.

The hypothesis `start i < finish i` is needed: for `[1, 1)` followed by `[0, 1)`, both of weight
`1`, the finish times are sorted and the two intervals are compatible, so the optimum is `2`, but
`wisValue` gives `1`.

Source: J. Kleinberg and É. Tardos, *Algorithm Design*, Pearson/Addison-Wesley, 2005, with
K. Wayne's lecture slides for its Sections 6.1–6.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- **Compatibility of intervals of positive length is disjointness.** Let activities $a$ and $b$
have start and finish times in a linear order with $s(a) < f(a)$ and $s(b) < f(b)$. Then $a$ and $b$
are compatible, that is $f(a) \le s(b)$ or $f(b) \le s(a)$, if and only if the closed-open
intervals $[s(a), f(a))$ and $[s(b), f(b))$ are disjoint. -/
theorem intervalCompatible_iff_disjoint_Ico {ι τ : Type*} [LinearOrder τ] {start finish : ι → τ}
    {a b : ι} (ha : start a < finish a) (hb : start b < finish b) :
    IntervalCompatible start finish a b ↔
      Disjoint (Set.Ico (start a) (finish a)) (Set.Ico (start b) (finish b)) := by
  rw [Set.Ico_disjoint_Ico, IntervalCompatible]
  constructor
  · rintro (h | h)
    · exact (min_le_left _ _).trans (h.trans (le_max_right _ _))
    · exact (min_le_right _ _).trans (h.trans (le_max_left _ _))
  · intro h
    rcases le_total (finish a) (finish b) with hab | hab
    · rw [min_eq_left hab] at h
      rcases le_total (start a) (start b) with hs | hs
      · rw [max_eq_right hs] at h
        exact Or.inl h
      · rw [max_eq_left hs] at h
        exact absurd h (not_le_of_gt ha)
    · rw [min_eq_right hab] at h
      rcases le_total (start a) (start b) with hs | hs
      · rw [max_eq_right hs] at h
        exact absurd h (not_le_of_gt hb)
      · rw [max_eq_left hs] at h
        exact Or.inr h

end Cslib.Algorithms.Lean.TimeM

namespace Cslib.Algorithms.Lean.WeightedIntervalScheduling

open Finset
open Cslib.Algorithms.Lean.TimeM (IntervalCompatible ret_bind ret_pure ret_tick time_bind time_pure
  time_tick)

variable {τ : Type*} {W : Type} [LinearOrder τ] [AddCommMonoid W] [LinearOrder W]

/-! ### The recurrence -/

/-- **Last interval finishing before an interval starts.** For intervals indexed by the positive
integers with start times $s$ and finish times $f$ in a linear order, $p(j)$ is the largest $i$
with $1 \le i < j$ and $f(i) \le s(j)$, or $0$ if there is none. -/
def wisPred (start finish : ℕ → τ) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun i => finish i ≤ start j) (j - 1)

theorem wisPred_succ_le (start finish : ℕ → τ) (j : ℕ) : wisPred start finish (j + 1) ≤ j :=
  Nat.findGreatest_le _

/-- **Weighted interval scheduling recurrence.** For intervals indexed by the positive integers with
start times $s$ and finish times $f$ in a linear order and weights $w$ in a commutative additive
monoid with a linear order, $\mathrm{OPT}(0) = 0$ and
$\mathrm{OPT}(j) = \max(\mathrm{OPT}(j - 1), w(j) + \mathrm{OPT}(p(j)))$ for $j \ge 1$, where $p(j)$
is the largest $i$ with $1 \le i < j$ and $f(i) \le s(j)$, or $0$ if there is none. -/
def wisValue (start finish : ℕ → τ) (weight : ℕ → W) : ℕ → W
  | 0 => 0
  | j + 1 => max (wisValue start finish weight j)
      (weight (j + 1) + wisValue start finish weight (wisPred start finish (j + 1)))
termination_by j => j
decreasing_by
  · omega
  · exact Nat.lt_succ_of_le (wisPred_succ_le start finish j)

theorem wisValue_zero (start finish : ℕ → τ) (weight : ℕ → W) :
    wisValue start finish weight 0 = 0 := by
  rw [wisValue]

theorem wisValue_succ (start finish : ℕ → τ) (weight : ℕ → W) (j : ℕ) :
    wisValue start finish weight (j + 1) = max (wisValue start finish weight j)
      (weight (j + 1) + wisValue start finish weight (wisPred start finish (j + 1))) := by
  rw [wisValue]

/-- **Traceback of the weighted interval scheduling recurrence.** For intervals indexed by the
positive integers with start times $s$, finish times $f$ and weights $w$, and with
$\mathrm{OPT}$ and $p$ as in the weighted interval scheduling recurrence, the traceback is
$T(0) = \emptyset$ and, for $j \ge 1$, $T(j) = \{j\} \cup T(p(j))$ if
$\mathrm{OPT}(j - 1) < w(j) + \mathrm{OPT}(p(j))$ and $T(j) = T(j - 1)$ otherwise. -/
def wisTrace (start finish : ℕ → τ) (weight : ℕ → W) : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 =>
    if wisValue start finish weight j <
        weight (j + 1) + wisValue start finish weight (wisPred start finish (j + 1)) then
      insert (j + 1) (wisTrace start finish weight (wisPred start finish (j + 1)))
    else
      wisTrace start finish weight j
termination_by j => j
decreasing_by
  · exact Nat.lt_succ_of_le (wisPred_succ_le start finish j)
  · omega

theorem wisTrace_zero (start finish : ℕ → τ) (weight : ℕ → W) :
    wisTrace start finish weight 0 = ∅ := by
  rw [wisTrace]

theorem wisTrace_succ (start finish : ℕ → τ) (weight : ℕ → W) (j : ℕ) :
    wisTrace start finish weight (j + 1) =
      if wisValue start finish weight j <
          weight (j + 1) + wisValue start finish weight (wisPred start finish (j + 1)) then
        insert (j + 1) (wisTrace start finish weight (wisPred start finish (j + 1)))
      else
        wisTrace start finish weight j := by
  rw [wisTrace]

/-- **Optimal schedule of weighted intervals.** For intervals indexed by the positive integers with
start times $s$ and finish times $f$ in a linear order and weights $w$ in a commutative additive
monoid with a linear order, a finite set $S$ of indices is an optimal schedule of the first $j$
intervals with value $v$ when $S \subseteq \{1, \dots, j\}$, any two distinct members of $S$ are
compatible, $\sum_{i \in S} w(i) = v$, and every subset $F$ of $\{1, \dots, j\}$ whose distinct
members are pairwise compatible has $\sum_{i \in F} w(i) \le v$. -/
def IsOptimalSchedule (start finish : ℕ → τ) (weight : ℕ → W) (j : ℕ) (S : Finset ℕ) (v : W) :
    Prop :=
  S ⊆ Finset.Icc 1 j ∧ (S : Set ℕ).Pairwise (IntervalCompatible start finish) ∧
    ∑ i ∈ S, weight i = v ∧
    ∀ F ⊆ Finset.Icc 1 j, (F : Set ℕ).Pairwise (IntervalCompatible start finish) →
      ∑ i ∈ F, weight i ≤ v

/-- **The value of an optimal schedule is the brute-force optimum.** For intervals indexed by the
positive integers with start times $s$ and finish times $f$ in a linear order and natural weights
$w$, if $S$ is an optimal schedule of the first $j$ intervals with value $v$, then $v$ is the
brute-force optimum over $\{1, \dots, j\}$: the supremum, over the subsets $F$ of
$\{1, \dots, j\}$ whose distinct members are pairwise compatible, of $\sum_{i \in F} w(i)$. -/
theorem IsOptimalSchedule.eq_wisOpt {start finish : ℕ → τ} {weight : ℕ → ℕ} {j : ℕ}
    {S : Finset ℕ} {v : ℕ} (h : IsOptimalSchedule start finish weight j S v) :
    v = wisOpt start finish weight (Finset.Icc 1 j) := by
  obtain ⟨hS, hc, hsum, hopt⟩ := h
  apply le_antisymm
  · rw [← hsum]
    apply Finset.le_sup (f := fun F => ∑ a ∈ F, weight a)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, ?_⟩
    intro a ha b hb hab
    exact hc ha hb hab
  · apply Finset.sup_le
    intro F hF
    obtain ⟨hFsub, hFc⟩ := Finset.mem_filter.mp hF
    exact hopt F (Finset.mem_powerset.mp hFsub) fun a ha b hb hab => hFc a ha b hb hab

section Optimality

variable [IsOrderedAddMonoid W] {start finish : ℕ → τ} {n : ℕ}

/-- In finish order, an earlier interval of positive length compatible with a later one finishes
by the start of the later one. -/
private theorem finish_le_start_of_compatible
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) (hmono : MonotoneOn finish (Set.Icc 1 n))
    {k j : ℕ} (hk : k ∈ Set.Icc 1 n) (hj : j ∈ Set.Icc 1 n) (hkj : k ≤ j)
    (h : IntervalCompatible start finish k j) : finish k ≤ start j := by
  rcases h with h | h
  · exact h
  · exact absurd (lt_of_lt_of_le (hpos k hk) ((hmono hk hj hkj).trans h)) (lt_irrefl _)

/-- Every interval up to `p(j)` finishes by the start of interval `j`. -/
private theorem finish_le_start_of_le_wisPred (hmono : MonotoneOn finish (Set.Icc 1 n))
    {k j : ℕ} (hj : j ≤ n) (hk : 1 ≤ k) (hkp : k ≤ wisPred start finish j) :
    finish k ≤ start j := by
  have hp0 : wisPred start finish j ≠ 0 := by omega
  have hP : finish (wisPred start finish j) ≤ start j := Nat.findGreatest_of_ne_zero rfl hp0
  have hpj : wisPred start finish j ≤ j - 1 := Nat.findGreatest_le _
  exact (hmono ⟨hk, by omega⟩ ⟨by omega, by omega⟩ hkp).trans hP

/-- The recurrence and its traceback are optimal for every prefix of intervals of positive length
ordered by finish time. -/
private theorem isOptimalSchedule_wisTrace (weight : ℕ → W)
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) (hmono : MonotoneOn finish (Set.Icc 1 n)) :
    ∀ j ≤ n, IsOptimalSchedule start finish weight j (wisTrace start finish weight j)
      (wisValue start finish weight j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjn
    rcases j with _ | j
    · refine ⟨by simp [wisTrace_zero], by simp [wisTrace_zero], by simp [wisTrace_zero,
        wisValue_zero], ?_⟩
      intro F hF _
      have : F = ∅ := by
        ext x
        simp only [Finset.notMem_empty, iff_false]
        intro hx
        have := Finset.mem_Icc.mp (hF hx)
        omega
      simp [this, wisValue_zero]
    · set p := wisPred start finish (j + 1) with hp
      have hpj : p ≤ j := wisPred_succ_le start finish j
      obtain ⟨hTj, hcj, hsj, hoj⟩ := ih j (by omega) (by omega)
      obtain ⟨hTp, hcp, hsp, hop⟩ := ih p (by omega) (by omega)
      rw [wisValue_succ, wisTrace_succ, ← hp]
      refine ⟨?_, ?_, ?_, ?_⟩
      · split_ifs
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · simp
          · have := Finset.mem_Icc.mp (hTp hx)
            simp only [Finset.mem_Icc]
            omega
        · exact hTj.trans (Finset.Icc_subset_Icc le_rfl (by omega))
      · split_ifs
        · rw [Finset.coe_insert, Set.pairwise_insert]
          refine ⟨hcp, fun k hk _ => ?_⟩
          have hk' := Finset.mem_Icc.mp (hTp hk)
          have hfs : finish k ≤ start (j + 1) :=
            finish_le_start_of_le_wisPred hmono hjn hk'.1 hk'.2
          exact ⟨Or.inr hfs, Or.inl hfs⟩
        · exact hcj
      · split_ifs with hlt
        · have hnot : j + 1 ∉ wisTrace start finish weight p := by
            intro h
            have := Finset.mem_Icc.mp (hTp h)
            omega
          rw [Finset.sum_insert hnot, hsp, max_eq_right hlt.le]
        · rw [hsj, max_eq_left (not_lt.mp hlt)]
      · intro F hF hcF
        by_cases hjF : j + 1 ∈ F
        · have hsub : F.erase (j + 1) ⊆ Finset.Icc 1 p := by
            intro k hk
            have hkF := Finset.mem_of_mem_erase hk
            have hkne := Finset.ne_of_mem_erase hk
            have hk' := Finset.mem_Icc.mp (hF hkF)
            have hfs : finish k ≤ start (j + 1) :=
              finish_le_start_of_compatible hpos hmono ⟨hk'.1, by omega⟩ ⟨by omega, hjn⟩
                (by omega) (hcF hkF hjF hkne)
            have hkp : k ≤ p := Nat.le_findGreatest (by omega) hfs
            exact Finset.mem_Icc.mpr ⟨hk'.1, hkp⟩
          have hle := hop (F.erase (j + 1)) hsub
            (hcF.mono (by simp only [Finset.coe_erase]; exact Set.sdiff_subset))
          calc ∑ i ∈ F, weight i = weight (j + 1) + ∑ i ∈ F.erase (j + 1), weight i :=
                (Finset.add_sum_erase F weight hjF).symm
            _ ≤ weight (j + 1) + wisValue start finish weight p := by gcongr
            _ ≤ _ := le_max_right _ _
        · have hsub : F ⊆ Finset.Icc 1 j := by
            intro k hk
            have hk' := Finset.mem_Icc.mp (hF hk)
            have hne : k ≠ j + 1 := fun h => hjF (h ▸ hk)
            exact Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩
          exact (hoj F hsub hcF).trans (le_max_left _ _)

end Optimality

/-! ### The algorithm -/

/- Binary search used by `wisTable`. It returns `lo` when `lo ≥ hi`; there is no `lo ≤ hi`
condition. Otherwise it compares `key m ≤ x` at `m = (lo + hi + 1) / 2`, charging one unit, and
continues on `[m, hi]` if this holds and on `[lo, m - 1]` otherwise; it never reads `key lo`. If
`lo ≤ hi`, the result lies in `[lo, hi]` whatever the keys, and when `key` is monotone on
`lo + 1, …, hi` it is the last `i` in that range with `key i ≤ x`, or `lo` if there is none
(`predSearch_spec`); on unsorted keys it need not be. -/
def predSearch (key : ℕ → τ) (x : τ) (lo hi : ℕ) : TimeM ℕ ℕ :=
  if h : lo < hi then
    if key ((lo + hi + 1) / 2) ≤ x then do
      TimeM.tick 1
      predSearch key x ((lo + hi + 1) / 2) hi
    else do
      TimeM.tick 1
      predSearch key x lo ((lo + hi + 1) / 2 - 1)
  else
    pure lo
termination_by hi - lo
decreasing_by all_goals omega

/- Bottom-up table of the recurrence, used by `wisSchedule`: the arrays `M = (M₀, …, Mⱼ)` and
`P = (P₀, …, Pⱼ)` with `M₀ = P₀ = 0` and, for `1 ≤ i ≤ j`,
`Pᵢ = predSearch finish (start i) 0 (i - 1)` and `Mᵢ = max Mᵢ₋₁ (weight i + M[Pᵢ])`. Each entry
charges the comparisons of its binary search and one unit for the comparison of weights.
`getD … 0` reads an index past the end as `0`; the indices read here are always in range. -/
def wisTable (start finish : ℕ → τ) (weight : ℕ → W) : ℕ → TimeM ℕ (Array W × Array ℕ)
  | 0 => pure (#[0], #[0])
  | j + 1 => do
    let t ← wisTable start finish weight j
    let p ← predSearch finish (start (j + 1)) 0 j
    TimeM.tick 1
    return (t.1.push (max (t.1.getD j 0) (weight (j + 1) + t.1.getD p 0)), t.2.push p)

/- Traceback through the table, used by `wisSchedule`. From `0` it returns `∅`; from `j ≥ 1`, with
`q = min Pⱼ (j - 1)` (the cap makes the recursion terminate on arbitrary arrays, and is never
reached on the arrays `wisTable` builds), it charges one unit for comparing `Mⱼ₋₁ < weight j + M[q]`
and returns `{j}` together with the traceback from `q` if this holds, and the traceback from
`j - 1` otherwise. `getD … 0` reads an index past the end as `0`. -/
def wisTraceback (weight : ℕ → W) (M : Array W) (P : Array ℕ) : ℕ → TimeM ℕ (Finset ℕ)
  | 0 => pure ∅
  | j + 1 =>
    if M.getD j 0 < weight (j + 1) + M.getD (min (P.getD (j + 1) 0) j) 0 then do
      TimeM.tick 1
      let S ← wisTraceback weight M P (min (P.getD (j + 1) 0) j)
      return insert (j + 1) S
    else do
      TimeM.tick 1
      wisTraceback weight M P j
termination_by j => j
decreasing_by all_goals omega

/-- **Weighted interval scheduling algorithm.** For intervals $1, \dots, n$ with start times $s$,
finish times $f$ and weights $w$, the algorithm sorts $1, \dots, n$ by finish time with merge sort
into the order $\sigma(1), \dots, \sigma(n)$ and stores that order in an array. For
$j = 1, \dots, n$ it finds $P_j$ by binary search: starting from $[lo, hi] = [0, j - 1]$, while
$lo < hi$ it compares $f(\sigma(m)) \le s(\sigma(j))$ at $m = \lfloor (lo + hi + 1)/2 \rfloor$ and
continues on $[m, hi]$ if this holds and on $[lo, m - 1]$ otherwise, and it takes $P_j = lo$. It
sets $M_0 = 0$ and $M_j = \max(M_{j-1}, w(\sigma(j)) + M_{P_j})$. It then traces back from $j = n$:
while $j \ge 1$, it takes $\sigma(j)$ and continues from $P_j$ if
$M_{j-1} < w(\sigma(j)) + M_{P_j}$, and continues from $j - 1$ otherwise. It returns $M_n$ and the
set of intervals taken. It charges one unit for each comparison of two finish times in the merge
sort, for each comparison $f(\sigma(m)) \le s(\sigma(j))$ in the binary searches, and for each
comparison of two weights in the table and the traceback; nothing else is charged. -/
def wisSchedule (start finish : ℕ → τ) (weight : ℕ → W) (n : ℕ) : TimeM ℕ (W × Finset ℕ) := do
  let order ← List.mergeSortM (List.range' 1 n)
    (fun a b => (⟨decide (finish a ≤ finish b), 1⟩ : TimeM ℕ Bool))
  let sorted := order.toArray
  let σ : ℕ → ℕ := fun i => sorted.getD (i - 1) 0
  let t ← wisTable (start ∘ σ) (finish ∘ σ) (weight ∘ σ) n
  let S ← wisTraceback (weight ∘ σ) t.1 t.2 n
  return (t.1.getD n 0, S.image σ)

/-! ### Correctness and cost of the algorithm -/

section Algorithm

private theorem predSearch_spec (key : ℕ → τ) (x : τ) (lo hi : ℕ) (hle : lo ≤ hi)
    (hmono : MonotoneOn key (Set.Icc (lo + 1) hi)) :
    lo ≤ (predSearch key x lo hi).ret ∧ (predSearch key x lo hi).ret ≤ hi ∧
      ((predSearch key x lo hi).ret ≠ lo → key (predSearch key x lo hi).ret ≤ x) ∧
      ∀ i, (predSearch key x lo hi).ret < i → i ≤ hi → ¬key i ≤ x := by
  fun_induction predSearch key x lo hi with
  | case1 lo hi h hc ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
      (hmono.mono (Set.Icc_subset_Icc (by omega) le_rfl))
    refine ⟨by simp only [ret_bind]; omega, by simpa only [ret_bind] using h2, ?_, ?_⟩
    · intro hne
      simp only [ret_bind] at hne ⊢
      by_cases hm : (predSearch key x ((lo + hi + 1) / 2) hi).ret = (lo + hi + 1) / 2
      · rw [hm]
        exact hc
      · exact h3 hm
    · simpa only [ret_bind] using h4
  | case2 lo hi h hc ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
      (hmono.mono (Set.Icc_subset_Icc le_rfl (by omega)))
    refine ⟨by simpa only [ret_bind] using h1, by simp only [ret_bind]; omega,
      by simpa only [ret_bind] using h3, ?_⟩
    intro i hri hih hki
    simp only [ret_bind] at hri
    by_cases him : i ≤ (lo + hi + 1) / 2 - 1
    · exact h4 i hri him hki
    · exact hc ((hmono ⟨by omega, by omega⟩ ⟨by omega, hih⟩ (by omega)).trans hki)
  | case3 lo hi h =>
    simp only [ret_pure]
    exact ⟨le_rfl, hle, fun h' => absurd rfl h', fun i h1 h2 => absurd h2 (by omega)⟩

private theorem predSearch_time (key : ℕ → τ) (x : τ) (lo hi : ℕ) :
    (predSearch key x lo hi).time ≤ Nat.clog 2 (hi + 1 - lo) := by
  fun_induction predSearch key x lo hi with
  | case1 lo hi h hc ih =>
    simp only [time_bind, time_tick]
    have hpos : 0 < Nat.clog 2 (hi + 1 - lo) := Nat.clog_pos one_lt_two (by omega)
    have hhalf := Cslib.Algorithms.Lean.TimeM.clog2_half_le (hi + 1 - lo)
    have hmono : Nat.clog 2 (hi + 1 - (lo + hi + 1) / 2) ≤ Nat.clog 2 ((hi + 1 - lo + 1) / 2) :=
      Nat.clog_mono_right 2 (by omega)
    omega
  | case2 lo hi h hc ih =>
    simp only [time_bind, time_tick]
    have hpos : 0 < Nat.clog 2 (hi + 1 - lo) := Nat.clog_pos one_lt_two (by omega)
    have hhalf := Cslib.Algorithms.Lean.TimeM.clog2_half_le (hi + 1 - lo)
    have hmono : Nat.clog 2 ((lo + hi + 1) / 2 - 1 + 1 - lo) ≤
        Nat.clog 2 ((hi + 1 - lo + 1) / 2) :=
      Nat.clog_mono_right 2 (by omega)
    omega
  | case3 lo hi h =>
    simp

/-- The binary search over `[0, j]` computes `p(j + 1)` when finish times are monotone on
`1, …, j`. -/
private theorem predSearch_eq_wisPred (start finish : ℕ → τ) (j : ℕ)
    (hmono : MonotoneOn finish (Set.Icc 1 j)) :
    (predSearch finish (start (j + 1)) 0 j).ret = wisPred start finish (j + 1) := by
  obtain ⟨-, h2, h3, h4⟩ := predSearch_spec finish (start (j + 1)) 0 j (Nat.zero_le _) hmono
  symm
  rw [wisPred, Nat.add_sub_cancel, Nat.findGreatest_eq_iff]
  exact ⟨h2, h3, fun i hi hij => h4 i hi hij⟩

private theorem getD_push_of_lt {α : Type} (a : Array α) (x d : α) {i : ℕ} (h : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h.ne, h]

private theorem getD_push_size {α : Type} (a : Array α) (x d : α) :
    (a.push x).getD a.size d = x := by
  simp [Array.getD_eq_getD_getElem?]

private theorem wisTable_spec (start finish : ℕ → τ) (weight : ℕ → W) {n : ℕ}
    (hmono : MonotoneOn finish (Set.Icc 1 n)) :
    ∀ j ≤ n, (wisTable start finish weight j).ret.1.size = j + 1 ∧
      (wisTable start finish weight j).ret.2.size = j + 1 ∧
      (∀ i ≤ j, (wisTable start finish weight j).ret.1.getD i 0 = wisValue start finish weight i) ∧
      ∀ i, 1 ≤ i → i ≤ j →
        (wisTable start finish weight j).ret.2.getD i 0 = wisPred start finish i := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨rfl, rfl, fun i hi => ?_, fun i h1 h2 => absurd h2 (by omega)⟩
    obtain rfl : i = 0 := by omega
    simp [wisTable, wisValue_zero]
  | succ j ih =>
    intro hjn
    obtain ⟨hs1, hs2, hM, hP⟩ := ih (by omega)
    have hp := predSearch_eq_wisPred start finish j (hmono.mono (Set.Icc_subset_Icc le_rfl
      (by omega)))
    simp only [wisTable, ret_bind, ret_pure, hp]
    refine ⟨by simp [hs1], by simp [hs2], fun i hi => ?_, fun i h1 h2 => ?_⟩
    · rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · rw [getD_push_of_lt _ _ _ (by omega), hM i (by omega)]
      · obtain rfl : i = j + 1 := by omega
        rw [← hs1, getD_push_size, hs1, wisValue_succ, hM j le_rfl,
          hM _ (wisPred_succ_le start finish j)]
    · rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · rw [getD_push_of_lt _ _ _ (by omega), hP i h1 (by omega)]
      · obtain rfl : i = j + 1 := by omega
        rw [← hs2, getD_push_size]

private theorem wisTable_time (start finish : ℕ → τ) (weight : ℕ → W) (j : ℕ) :
    (wisTable start finish weight j).time ≤ j * Nat.clog 2 j + j := by
  induction j with
  | zero => simp [wisTable]
  | succ j ih =>
    simp only [wisTable, time_bind, time_tick, time_pure]
    have hs := predSearch_time finish (start (j + 1)) 0 j
    have hc : Nat.clog 2 j ≤ Nat.clog 2 (j + 1) := Nat.clog_mono_right 2 (by omega)
    have hm : j * Nat.clog 2 j ≤ j * Nat.clog 2 (j + 1) := Nat.mul_le_mul_left j hc
    simp only [Nat.sub_zero] at hs
    have hsucc : (j + 1) * Nat.clog 2 (j + 1) = j * Nat.clog 2 (j + 1) + Nat.clog 2 (j + 1) :=
      Nat.succ_mul _ _
    omega

private theorem wisTraceback_ret (start finish : ℕ → τ) (weight : ℕ → W) (M : Array W)
    (P : Array ℕ) {n : ℕ} (hM : ∀ i ≤ n, M.getD i 0 = wisValue start finish weight i)
    (hP : ∀ i, 1 ≤ i → i ≤ n → P.getD i 0 = wisPred start finish i) :
    ∀ j ≤ n, (wisTraceback weight M P j).ret = wisTrace start finish weight j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjn
    rcases j with _ | j
    · rw [wisTraceback, wisTrace_zero]
      rfl
    · have hq : min (P.getD (j + 1) 0) j = wisPred start finish (j + 1) := by
        rw [hP (j + 1) (by omega) hjn]
        exact min_eq_left (wisPred_succ_le start finish j)
      have hpj := wisPred_succ_le start finish j
      rw [wisTraceback, wisTrace_succ, hq, hM j (by omega), hM _ (by omega)]
      split_ifs
      · simp only [ret_bind, ret_pure]
        rw [ih _ (by omega) (by omega)]
      · simp only [ret_bind]
        exact ih j (by omega) (by omega)

private theorem wisTraceback_time (weight : ℕ → W) (M : Array W) (P : Array ℕ) (j : ℕ) :
    (wisTraceback weight M P j).time ≤ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · rw [wisTraceback]
      rfl
    · rw [wisTraceback]
      split_ifs
      · simp only [time_bind, time_tick, time_pure]
        have := ih (min (P.getD (j + 1) 0) j) (by omega)
        omega
      · simp only [time_bind, time_tick]
        have := ih j (by omega)
        omega

/-- An optimal schedule of the reindexed intervals `σ 1, …, σ n` gives one of `1, …, n` when `σ`
permutes `1, …, n`. -/
private theorem isOptimalSchedule_image {start finish : ℕ → τ} {weight : ℕ → W} {n : ℕ}
    {σ : ℕ → ℕ} (hmaps : Set.MapsTo σ (Set.Icc 1 n) (Set.Icc 1 n))
    (hinj : Set.InjOn σ (Set.Icc 1 n)) (hsurj : Set.SurjOn σ (Set.Icc 1 n) (Set.Icc 1 n))
    {S : Finset ℕ} {v : W}
    (h : IsOptimalSchedule (start ∘ σ) (finish ∘ σ) (weight ∘ σ) n S v) :
    IsOptimalSchedule start finish weight n (S.image σ) v := by
  obtain ⟨hS, hc, hsum, hopt⟩ := h
  have hSinj : Set.InjOn σ (S : Set ℕ) := hinj.mono fun x hx => by
    simpa using hS hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have := hmaps (by simpa using hS hi)
    simpa using this
  · rw [Finset.coe_image, hSinj.pairwise_image]
    exact hc
  · rw [Finset.sum_image hSinj]
    exact hsum
  · intro F hF hcF
    set F' := (Finset.Icc 1 n).filter (fun i => σ i ∈ F) with hF'
    have hF'sub : F' ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
    have hF'inj : Set.InjOn σ (F' : Set ℕ) := hinj.mono fun x hx => by
      simpa using hF'sub hx
    have himage : F'.image σ = F := by
      ext x
      simp only [Finset.mem_image, hF', Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
      · intro hx
        obtain ⟨i, hi, rfl⟩ := hsurj (by simpa using hF hx)
        exact ⟨i, ⟨by simpa using hi, hx⟩, rfl⟩
    have hcF' : (F' : Set ℕ).Pairwise (IntervalCompatible (start ∘ σ) (finish ∘ σ)) := by
      intro i hi k hk hik
      exact hcF (by simpa [hF'] using (Finset.mem_filter.mp hi).2)
        (by simpa [hF'] using (Finset.mem_filter.mp hk).2)
        (fun h => hik (hF'inj hi hk h))
    calc ∑ i ∈ F, weight i = ∑ i ∈ F'.image σ, weight i := by rw [himage]
      _ = ∑ i ∈ F', weight (σ i) := Finset.sum_image hF'inj
      _ ≤ v := hopt F' hF'sub hcF'

end Algorithm

/-! ### The main theorem -/

/-- **Weighted interval scheduling by dynamic programming.** Let intervals $1, \dots, n$ have start
times $s$ and finish times $f$ in a linear order with $s(i) < f(i)$ for every $i$, and weights $w$
in a linearly ordered commutative additive monoid with monotone addition; intervals $i$ and $k$
are compatible when $f(i) \le s(k)$ or $f(k) \le s(i)$. Let $\mathrm{OPT}$ be the weighted
interval scheduling recurrence and $T$ its traceback.

1. If $f(1) \le \dots \le f(n)$, then for every $j \le n$ the set $T(j)$ is an optimal schedule of
   the first $j$ intervals with value $\mathrm{OPT}(j)$: it consists of pairwise compatible
   intervals among $1, \dots, j$ of total weight $\mathrm{OPT}(j)$, and every set of pairwise
   compatible intervals among $1, \dots, j$ has total weight at most $\mathrm{OPT}(j)$.
2. Whatever the order of the finish times, the algorithm that sorts the intervals by finish time
   with merge sort, fills the table of the recurrence while computing each $p(j)$ by binary
   search, and traces back returns an optimal schedule of the $n$ intervals together with its
   value.
3. The algorithm is charged at most $2n\lceil \log_2 n \rceil + 2n$ units, where
   $n\lceil \log_2 n \rceil$ is read as $0$ when $n = 0$. It is charged one unit for each
   comparison of two finish times in the merge sort, for each comparison of a finish time with a
   start time in the binary searches, and for each comparison of two weights in the table and the
   traceback; nothing else is charged. -/
theorem isOptimalSchedule_wisTrace_and_wisSchedule [IsOrderedAddMonoid W]
    (start finish : ℕ → τ) (weight : ℕ → W) (n : ℕ)
    (hpos : ∀ i ∈ Set.Icc 1 n, start i < finish i) :
    (MonotoneOn finish (Set.Icc 1 n) → ∀ j ≤ n,
      IsOptimalSchedule start finish weight j (wisTrace start finish weight j)
        (wisValue start finish weight j)) ∧
    IsOptimalSchedule start finish weight n (wisSchedule start finish weight n).ret.2
      (wisSchedule start finish weight n).ret.1 ∧
    (wisSchedule start finish weight n).time ≤ 2 * n * Nat.clog 2 n + 2 * n := by
  refine ⟨fun hmono => isOptimalSchedule_wisTrace weight hpos hmono, ?_, ?_⟩
  · set order := List.mergeSort (List.range' 1 n) (fun a b => decide (finish a ≤ finish b))
      with horder
    have hret : (List.mergeSortM (List.range' 1 n)
        (fun a b => (⟨decide (finish a ≤ finish b), 1⟩ : TimeM ℕ Bool))).ret = order := by
      rw [Cslib.Algorithms.Lean.TimeM.ret_mergeSortM]
    have hperm : order.Perm (List.range' 1 n) := List.mergeSort_perm _ _
    have hlen : order.length = n := by simpa using hperm.length_eq
    have hnodup : order.Nodup := hperm.nodup_iff.mpr (List.nodup_range' (s := 1) (n := n))
    have hmem : ∀ x, x ∈ order ↔ x ∈ Set.Icc 1 n := by
      intro x
      rw [hperm.mem_iff, List.mem_range'_1, Set.mem_Icc]
      omega
    have hsorted : order.Pairwise (fun a b => finish a ≤ finish b) := by
      have hs := List.pairwise_mergeSort (le := fun a b => decide (finish a ≤ finish b))
        (fun a b c hab hbc => by
          simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        (fun a b => by
          simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (finish a) (finish b))
        (List.range' 1 n)
      simpa [horder] using hs
    set σ : ℕ → ℕ := fun i => order.toArray.getD (i - 1) 0 with hσ
    have hσget : ∀ i (hi : i ∈ Set.Icc 1 n), σ i = order[i - 1]'(by
        rw [hlen]; exact lt_of_lt_of_le (Nat.sub_lt hi.1 one_pos) hi.2) := by
      intro i hi
      simp only [hσ, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
      rw [List.getElem?_eq_getElem]
      rfl
    have hmaps : Set.MapsTo σ (Set.Icc 1 n) (Set.Icc 1 n) := by
      intro i hi
      rw [hσget i hi, ← hmem]
      exact List.getElem_mem _
    have hinj : Set.InjOn σ (Set.Icc 1 n) := by
      intro i hi k hk h
      rw [hσget i hi, hσget k hk, hnodup.getElem_inj_iff] at h
      have := hi.1
      have := hk.1
      omega
    have hsurj : Set.SurjOn σ (Set.Icc 1 n) (Set.Icc 1 n) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ((hmem x).mpr hx)
      have hk1 : k + 1 ∈ Set.Icc 1 n := ⟨by omega, by omega⟩
      exact ⟨k + 1, hk1, by rw [hσget _ hk1]; rfl⟩
    have hmono : MonotoneOn (finish ∘ σ) (Set.Icc 1 n) := by
      intro i hi k hk hik
      simp only [Function.comp_apply, hσget i hi, hσget k hk]
      rcases Nat.lt_or_ge (i - 1) (k - 1) with hlt | hge
      · exact List.pairwise_iff_getElem.mp hsorted _ _ _ _ hlt
      · obtain rfl : i = k := by
          have := hi.1
          have := hk.1
          omega
        exact le_rfl
    have hpos' : ∀ i ∈ Set.Icc 1 n, (start ∘ σ) i < (finish ∘ σ) i :=
      fun i hi => hpos _ (hmaps hi)
    obtain ⟨-, -, hM, hP⟩ := wisTable_spec (start ∘ σ) (finish ∘ σ) (weight ∘ σ) hmono n le_rfl
    have htr := wisTraceback_ret (start ∘ σ) (finish ∘ σ) (weight ∘ σ) _ _ hM hP n le_rfl
    have hopt := isOptimalSchedule_wisTrace (weight ∘ σ) hpos' hmono n le_rfl
    simp only [wisSchedule, ret_bind, ret_pure, hret]
    rw [htr, hM n le_rfl]
    exact isOptimalSchedule_image hmaps hinj hsurj hopt
  · simp only [wisSchedule, time_bind, time_pure, Nat.add_zero]
    have h1 := Cslib.Algorithms.Lean.TimeM.time_mergeSortM_le (List.range' 1 n)
      (fun a b => decide (finish a ≤ finish b))
    have h1' := Cslib.Algorithms.Lean.TimeM.timeMergeSortRec_le n
    simp only [List.length_range'] at h1
    have hT : Cslib.Algorithms.Lean.TimeM.T n = n * Nat.clog 2 n := rfl
    have hassoc : 2 * n * Nat.clog 2 n = 2 * (n * Nat.clog 2 n) := Nat.mul_assoc _ _ _
    refine le_trans (Nat.add_le_add h1 (Nat.add_le_add (wisTable_time _ _ _ n)
      (wisTraceback_time _ _ _ n))) ?_
    omega

end Cslib.Algorithms.Lean.WeightedIntervalScheduling
