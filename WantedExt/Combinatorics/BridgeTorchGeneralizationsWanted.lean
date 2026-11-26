/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalizations of the bridge and torch problem: auxiliary statements

Statements from Thang Pang Ern and Gerard Sayson, "Some Generalizations of the
Bridge and Torch Problem", *Journal of Integer Sequences* 29 (2026),
Article 26.5.6 (<https://cs.uwaterloo.ca/journals/JIS/VOL29/Ern/ern6.html>).

The schedule model is the one of the paper (Theorem 1 proof, Section 2): the
people are `1, …, n`, person `i` has crossing time `i`, crossings alternate
between forward moves (left to right) and returns (right to left) starting with
a forward move, every crossing carries between `1` and `c` people who are on
the torch's side, a crossing costs the largest crossing time among its people,
and a schedule ends when everyone is on the right bank with the torch.
`bridgeTime c n` is the optimal total time (`T(n) = bridgeTime 2 n`,
`T₃(n) = bridgeTime 3 n`). The model and the capacity-2 and capacity-3 records
were checked against the arXiv version (arXiv:2608.05190v1) of the paper; the
admissible bags of Section 3.2, Definition 13, and the star model of Section 4, Definition 25,
are taken from the journal version (JIS TeX source `ern6.tex`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Combinatorics.BridgeTorchParityInterpolation
public import MathlibExt.Combinatorics.BridgeTorchReturnInequality
public import MathlibExt.Combinatorics.BridgeTorchStar
public import MathlibExt.Combinatorics.BridgeTorchThreeInitialValues
public import MathlibExt.Combinatorics.BridgeTorchThreeUpperBound
public import MathlibExt.Combinatorics.BridgeTorchTwo
public import MathlibExt.Combinatorics.BridgeTorchWeights

set_option autoImplicit false

namespace MetaMathlibExt

namespace BridgeTorchGeneralizations

@[expose] public section

open Finset

/-- **Forward crossings.** The forward crossings of a list of crossings are its entries at the
even positions $0, 2, 4, \dots$ (counting from $0$), in their original order. For a schedule
these are its forward moves, from left to right.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 7. -/
def forwardCrossings {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: forwardCrossings l

/-- **Return crossings.** For a list $\sigma = (A_0, A_1, \dots, A_{\ell - 1})$ whose entries may
come from any type, the returns of $\sigma$ are its entries at odd positions, $A_1, A_3, A_5, \dots$
in order, with positions counted from $0$. For the list of crossings of a bridge schedule these
are the crossings from right to left.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 7. -/
def returnCrossings {α : Type*} (σ : List α) : List α :=
  forwardCrossings σ.tail

/-- **Right bank after a sequence of crossings.** Let $n$ be a natural number and let
$\tau = (A_1, \dots, A_k)$ be a finite sequence of finite sets of natural numbers. The right bank
after $\tau$ is the set of those $p \in \{1, \dots, n\}$ for which the number of indices $i$ with
$p \in A_i$ is odd.

When $\tau$ is a prefix of a schedule for the people $1, \dots, n$, these are the people who have
crossed an odd number of times, so they stand on the right bank.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 9. -/
def rightBank (n : ℕ) (τ : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun p => Odd (τ.countP fun A => decide (p ∈ A))

/-- **A four-person schedule of total time 11.** For the people $1, 2, 3, 4$ on a bridge of
capacity $2$, the crossings $\{1,2\}$ forward, $\{1\}$ back, $\{1,3\}$ forward, $\{1\}$ back,
$\{1,4\}$ forward, in this order, form a schedule, and its total time is $11$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
table after the proof of Theorem 1. -/
theorem isBridgeSchedule_two_four :
    IsBridgeSchedule 2 4 [{1, 2}, {1}, {1, 3}, {1}, {1, 4}] ∧
      scheduleCost [{1, 2}, {1}, {1, 3}, {1}, {1, 4}] = 11 := by
  unfold IsBridgeSchedule
  decide

/-- **One crossing of three people under capacities two and three.** For the people $1, 2, 3$,
the single forward crossing $\{1, 2, 3\}$ is not a schedule on a bridge of capacity $2$, but it
is a schedule on a bridge of capacity $3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 3. -/
theorem isBridgeSchedule_capacity_three :
    ¬ IsBridgeSchedule 2 3 [{1, 2, 3}] ∧ IsBridgeSchedule 3 3 [{1, 2, 3}] := by
  unfold IsBridgeSchedule
  decide

/-- **Forward moves, returns and right bank of a four-person schedule.** For the schedule whose
crossings are, in order, $\{1,2\}$, $\{1\}$, $\{1,3\}$, $\{1\}$, $\{1,4\}$, the forward crossings
are $\{1,2\}, \{1,3\}, \{1,4\}$ and the returns are $\{1\}, \{1\}$. For the people $1, 2, 3, 4$,
the right bank after the crossings $\{1,2\}$, $\{1\}$ (the first two of the schedule) is $\{2\}$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
table after the proof of Theorem 1. -/
theorem forwardCrossings_returnCrossings_rightBank_example :
    forwardCrossings ([{1, 2}, {1}, {1, 3}, {1}, {1, 4}] : List (Finset ℕ)) =
        [{1, 2}, {1, 3}, {1, 4}] ∧
      returnCrossings ([{1, 2}, {1}, {1, 3}, {1}, {1, 4}] : List (Finset ℕ)) = [{1}, {1}] ∧
      rightBank 4 [{1, 2}, {1}] = {2} := by
  decide

/-- **Fewest crossings of the fastest person in an optimal schedule.** For bridge capacity $2$
and $n \ge 1$ people $1, \dots, n$ (person $i$ has crossing time $i$), the least number $a(n)$
of crossings that include person $1$, taken over all optimal schedules (complete schedules
whose total time equals the optimal crossing time $T(n)$), is $a(n) = 2\lceil n/2 \rceil - 1$.
Crossings in both directions are counted.

This reads the paper's $a(n)$ as a minimum over optimal schedules (the paper discusses the
non-uniqueness of optimal schedules); over all schedules the minimum would be $1$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 6 (`jis-2026-26.5.6-prop-6`). -/
public theorem_wanted bridgeTime_two_least_trips_of_fastest (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {a | ∃ σ, IsBridgeSchedule 2 n σ ∧ scheduleCost σ = bridgeTime 2 n ∧
        σ.countP (fun A => decide (1 ∈ A)) = a} (2 * ((n + 1) / 2) - 1)

/-- **Lower bound for capacity-two schedules.** Let $n \ge 3$ and let $T(n)$ be the optimal
crossing time of the $n$ people $1, \dots, n$ (person $i$ crossing in time $i$) on a bridge of
capacity $2$. Let $\sigma$ be a bridge schedule of capacity $2$ for these people in which person
$1$ takes part in exactly $a$ forward moves, exactly $m$ returns carry two people and exactly $s$
forward moves carry one person. Then the total cost of $\sigma$ is at least
$T(n) + \lceil n/2 \rceil - a + 4m + 3s$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 7 (`jis-2026-26.5.6-lem-7`). -/
public theorem_wanted scheduleCost_two_lower_bound (n : ℕ) (hn : 3 ≤ n) (σ : List (Finset ℕ))
    (hσ : IsBridgeSchedule 2 n σ) :
    (bridgeTime 2 n : ℤ) + ((n + 1) / 2 : ℕ) -
        ((forwardCrossings σ).countP fun A => decide (1 ∈ A) : ℕ) +
        4 * ((returnCrossings σ).countP fun A => decide (A.card = 2) : ℕ) +
        3 * ((forwardCrossings σ).countP fun A => decide (A.card = 1) : ℕ) ≤
      scheduleCost σ

/-- **Optimal capacity-3 schedules with fastest single returns.** Let $n \ge 1$ and consider the
people $1, \dots, n$, person $i$ having crossing time $i$, on a bridge of capacity $3$ with one
torch. Then some schedule has total time equal to the optimal crossing time $T_3(n)$ and the
following property: every return (a crossing at an odd position, counting from $0$) carries a
single person $p$, and $p \le q$ for every person $q$ on the right bank just before that return.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 9 (`jis-2026-26.5.6-lem-9`). -/
public theorem_wanted exists_optimal_schedule_three_fastest_returns (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ, IsBridgeSchedule 3 n σ ∧ scheduleCost σ = bridgeTime 3 n ∧
      ∀ (i : ℕ) (hi : i < σ.length), Odd i →
        ∃ p, σ[i] = {p} ∧ ∀ q ∈ rightBank n (σ.take i), p ≤ q

/-- **Lower bound for capacity-three schedules.** Let $n \ge 7$. Every bridge schedule of
capacity $3$ for the $n$ people $1, \dots, n$ (person $i$ crossing in time $i$) has total cost at
least $V(n) = n^2/6 + 2n - 11/2$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 17 (`jis-2026-26.5.6-prop-17`). -/
public theorem_wanted scheduleCost_three_lower_bound (n : ℕ) (hn : 7 ≤ n)
    (σ : List (Finset ℕ)) (hσ : IsBridgeSchedule 3 n σ) :
    (n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2 ≤ scheduleCost σ

/-- **Closed form for capacity three.** Let $T_3(n)$ be the optimal crossing time of $n$ people
with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For every
$n \ge 7$,
$$T_3(n) = \frac{n^2}{6} + 2n - \frac{181}{36} + \frac{(-1)^n}{4} - \frac{2}{9}\cos(2n\pi/3).$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 20 (`jis-2026-26.5.6-thm-20`). -/
public theorem_wanted bridgeTime_three_closed_form (n : ℕ) (hn : 7 ≤ n) :
    (bridgeTime 3 n : ℝ) = (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
      2 / 9 * Real.cos (2 * n * Real.pi / 3)

/-- **Six-step recurrence for capacity three.** Let $T_3(n)$ be the optimal crossing time of
$n$ people with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For
every $n \ge 13$, $T_3(n) = T_3(n - 6) + 2n + 6$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Corollary 21 (`jis-2026-26.5.6-cor-21`). -/
public theorem_wanted bridgeTime_three_recurrence (n : ℕ) (hn : 13 ≤ n) :
    bridgeTime 3 n = bridgeTime 3 (n - 6) + 2 * n + 6


/-- **Admissible bags.** Let $n$ be a natural number. A finite multiset $F$ of finite sets of
natural numbers is an admissible bag for $n$ people (bridge capacity $3$) when (i) every $T \in F$
is a nonempty subset of $\{1, \dots, n\}$ with $|T| \le 3$, (ii) every $i \in \{1, \dots, n\}$
lies in some $T \in F$, and (iii) $\sum_{T \in F} (|T| - 1) = n - 1$, where the sum counts each
member of $F$ with its multiplicity and $n - 1$ is read as $0$ when $n = 0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition 13 (admissible bag), Section 3.2 (journal version). -/
def IsAdmissibleBag (n : ℕ) (F : Multiset (Finset ℕ)) : Prop :=
  (∀ T ∈ F, T.Nonempty ∧ T ⊆ Icc 1 n ∧ T.card ≤ 3) ∧
    (∀ i ∈ Icc 1 n, ∃ T ∈ F, i ∈ T) ∧ (F.map fun T => T.card - 1).sum = n - 1

/-- **Weight of a bag.** For a natural number $n$ and a bag $F$, that is, a finite multiset of
finite sets of natural numbers, the weight of $F$ for $n$ people is the real number
$w(F) = \sum_{T \in F} \left(\max T + \sum_{i \in T} i\right) - \frac{n(n+1)}{2}$, where each
set counts with its multiplicity in $F$ and $\max \emptyset = 0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition 13 (admissible bag), Section 3.2 (journal version). -/
noncomputable def bagWeight (n : ℕ) (F : Multiset (Finset ℕ)) : ℝ :=
  (((F.map fun T => T.sup id + ∑ i ∈ T, i).sum : ℕ) : ℝ) - n * (n + 1) / 2

/-- **A one-trip admissible bag for three people.** The multiset whose only member is the set
$\{1, 2, 3\}$ is an admissible bag for $3$ people, and its weight for $3$ people is $3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (admissible bag), characteristic example. -/
theorem isAdmissibleBag_three_and_bagWeight :
    IsAdmissibleBag 3 {{1, 2, 3}} ∧ bagWeight 3 {{1, 2, 3}} = 3 := by
  refine ⟨⟨?_, ?_, by decide⟩, ?_⟩
  · intro T hT
    rw [Multiset.mem_singleton] at hT
    subst hT
    exact ⟨by decide, by decide, by decide⟩
  · intro i hi
    exact ⟨{1, 2, 3}, Multiset.mem_singleton_self _, by
      simp only [mem_Icc] at hi
      simp only [mem_insert, mem_singleton]
      omega⟩
  · simp only [bagWeight, Multiset.map_singleton, Multiset.sum_singleton]
    norm_num [Finset.sup_insert, Finset.sum_insert]

/-- **Schedules with single-person returns give admissible bags.** Let $n$ be a natural number
and let $\sigma$ be a schedule for the people $1, \dots, n$ on a bridge of capacity $3$ in which
every return carries exactly one person. Let $F(\sigma)$ be the multiset of the forward crossings
of $\sigma$. Then $F(\sigma)$ is an admissible bag for $n$ people, and the total time of $\sigma$
equals the weight $w(F(\sigma))$ of this bag for $n$ people.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 14 (`jis-2026-26.5.6-prop-14`), first assertion. -/
public theorem_wanted isAdmissibleBag_forwardCrossings_of_single_returns (n : ℕ)
    (σ : List (Finset ℕ)) (hσ : IsBridgeSchedule 3 n σ)
    (hret : ∀ A ∈ returnCrossings σ, A.card = 1) :
    IsAdmissibleBag n (forwardCrossings σ : Multiset (Finset ℕ)) ∧
      (scheduleCost σ : ℝ) = bagWeight n (forwardCrossings σ : Multiset (Finset ℕ))

/-- **Some admissible bag weighs at most the capacity-3 optimal time.** For every natural number
$n$, some admissible bag $F$ for $n$ people has weight $w(F)$ at most the capacity-3 optimal
crossing time $T_3(n)$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 14 (`jis-2026-26.5.6-prop-14`), consequence. -/
public theorem_wanted exists_isAdmissibleBag_bagWeight_le_bridgeTime_three (n : ℕ) :
    ∃ F, IsAdmissibleBag n F ∧ bagWeight n F ≤ bridgeTime 3 n

/-- **Lower bound for the weight of an admissible bag.** For every natural number $n \ge 7$
and every admissible bag $F$ for $n$ people, the weight of $F$ is at least
$\frac{n^2}{6} + 2n - \frac{11}{2}$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Corollary 18 (`jis-2026-26.5.6-cor-18`). -/
public theorem_wanted bagWeight_ge_of_isAdmissibleBag (n : ℕ) (hn : 7 ≤ n)
    (F : Multiset (Finset ℕ)) (hF : IsAdmissibleBag n F) :
    (n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2 ≤ bagWeight n F

end

end BridgeTorchGeneralizations

end MetaMathlibExt
