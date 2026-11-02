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

The schedule model is the one of the paper (Theorem 1 proof, Section 3): the
people are `1, …, n`, person `i` has crossing time `i`, crossings alternate
between forward moves (left to right) and returns (right to left) starting with
a forward move, every crossing carries between `1` and `c` people who are on
the torch's side, a crossing costs the largest crossing time among its people,
and a schedule ends when everyone is on the right bank with the torch.
`bridgeTime c n` is the optimal total time (`T(n) = bridgeTime 2 n`,
`T₃(n) = bridgeTime 3 n`). The model and the capacity-2 and capacity-3 records
were checked against the arXiv version (arXiv:2608.05190v1) of the paper; the
admissible bags of Section 3.3 and the star model of Section 5 are taken from
the journal version (JIS TeX source `ern6.tex`), which is the only version that
states them.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace MetaMathlibExt

namespace BridgeTorchGeneralizations

@[expose] public section

open Finset

/-- **Weights of the capacity-3 lower bound.** The rational weights $y_i$ are
$y_1 = y_2 = y_3 = 0$, $y_4 = 2$, $y_5 = 4$, $y_6 = 5$, and $y_i = (4i - 8)/3$ for $i \ge 7$.
The value $y_0$ is unused and set to $0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
def bridgeWeight : ℕ → ℚ
  | 0 | 1 | 2 | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 5
  | i + 7 => (4 * ((i + 7 : ℕ) : ℚ) - 8) / 3

/-- **First seven weights of the capacity-3 lower bound.** The weights $y_1, \dots, y_7$ of the
capacity-3 lower bound are $0, 0, 0, 2, 4, 5, 20/3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_small :
    bridgeWeight 1 = 0 ∧ bridgeWeight 2 = 0 ∧ bridgeWeight 3 = 0 ∧ bridgeWeight 4 = 2 ∧
      bridgeWeight 5 = 4 ∧ bridgeWeight 6 = 5 ∧ bridgeWeight 7 = 20 / 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [bridgeWeight]
  norm_num

/-- **Weights of the capacity-3 lower bound from $7$ on.** For every natural number $i \ge 7$,
the weight $y_i$ of the capacity-3 lower bound equals $(4i - 8)/3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_of_seven_le (i : ℕ) (hi : 7 ≤ i) :
    bridgeWeight i = (4 * (i : ℚ) - 8) / 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rfl

/-- **Valid crossing sequences from a state of the bridge and torch problem.** Let $c$ be a
natural number and let $P$ and $L$ be finite sets of natural numbers, the people and the left
bank. Whether a finite sequence $A_1, \dots, A_k$ of finite sets of natural numbers (the
crossings) is valid from the left bank $L$ with the torch on a given side is defined by recursion
on $k$. The empty sequence is valid exactly when $L = \emptyset$ and the torch is on the right.
With the torch on the left, the sequence is valid when $A_1$ is a nonempty subset of $L$ with at
most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank $L \setminus A_1$ with the
torch on the right. With the torch on the right, it is valid when $A_1$ is a nonempty subset of
$P \setminus L$ with at most $c$ elements and $A_2, \dots, A_k$ is valid from the left bank
$L \cup A_1$ with the torch on the left.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 (states and moves) and Section 3 (capacity `c`). -/
def bridgeScheduleFrom (c : ℕ) (P : Finset ℕ) : Finset ℕ → Bool → List (Finset ℕ) → Bool
  | L, torchLeft, [] => decide (L = ∅) && !torchLeft
  | L, true, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ L) && bridgeScheduleFrom c P (L \ A) false σ
  | L, false, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ P \ L) && bridgeScheduleFrom c P (L ∪ A) true σ

/-- **Bridge schedules.** Let $c$ and $n$ be natural numbers. A finite sequence $\sigma$ of finite
sets of natural numbers (the crossings) is a schedule for the people $1, \dots, n$ on a bridge of
capacity $c$ with one torch when the following holds. Start with all of $1, \dots, n$ and the
torch on the left bank. The crossings at even positions (counting from $0$) are forward moves:
each is a nonempty set of at most $c$ people then on the left bank, who cross with the torch to
the right bank. The crossings at odd positions are returns: each is a nonempty set of at most $c$
people then on the right bank, who cross with the torch back to the left bank. After the last
crossing the left bank is empty and the torch is on the right bank.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 and Section 3. -/
def IsBridgeSchedule (c n : ℕ) (σ : List (Finset ℕ)) : Prop :=
  bridgeScheduleFrom c (Finset.Icc 1 n) (Finset.Icc 1 n) true σ = true

/-- **Total time of a schedule.** For a finite sequence $\sigma = (A_1, \dots, A_k)$ of finite sets
of natural numbers (the crossings), the total time of $\sigma$ is $\sum_{i=1}^{k} \max A_i$, where
$\max \emptyset = 0$. Since person $p$ has crossing time $p$, each crossing costs the largest
crossing time among the people in it.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1. -/
def scheduleCost (σ : List (Finset ℕ)) : ℕ :=
  (σ.map fun A => A.sup id).sum

/-- **Optimal crossing time of the bridge and torch problem.** For a bridge of capacity $c$ and
$n$ people $1, \dots, n$, where person $i$ has crossing time $i$, the optimal crossing time is
the least total time of a complete schedule with one torch; the total time of a schedule is the
sum, over its crossings, of the largest crossing time among the people in that crossing. It is
written $T(n)$ for $c = 2$ and $T_3(n)$ for $c = 3$. If no complete schedule exists (for
example when $n = 0$), the value is $0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 and Theorem 12. -/
noncomputable def bridgeTime (c n : ℕ) : ℕ :=
  sInf {t | ∃ σ, IsBridgeSchedule c n σ ∧ scheduleCost σ = t}

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

/-- **Every schedule bounds the optimal time.** For all natural numbers $c$ and $n$ and every
complete schedule $\sigma$ for the people $1, \dots, n$ on a bridge of capacity $c$ with one
torch, the optimal crossing time of these $n$ people on this bridge is at most the total time
of $\sigma$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (definition of `T(n)`). -/
theorem bridgeTime_le_scheduleCost {c n : ℕ} {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule c n σ) : bridgeTime c n ≤ scheduleCost σ :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

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

/-- **Parity interpolation.** Let $f, g, a : \mathbb{N} \to \mathbb{R}$ be sequences with
$a_{2m} = f(m)$ and $a_{2m+1} = g(m)$ for every $m \in \mathbb{N}$. Then for every
$n \in \mathbb{N}$,

$$a_n = \frac{1 + (-1)^n}{2} f(\lfloor n/2 \rfloor) + \frac{1 - (-1)^n}{2} g(\lfloor n/2 \rfloor).$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 2 (`jis-2026-26.5.6-lem-2`). -/
public theorem_wanted parity_interpolation (f g a : ℕ → ℝ)
    (heven : ∀ m, a (2 * m) = f m) (hodd : ∀ m, a (2 * m + 1) = g m) (n : ℕ) :
    a n = (1 + (-1 : ℝ) ^ n) / 2 * f (n / 2) + (1 - (-1 : ℝ) ^ n) / 2 * g (n / 2)

/-- **Local inequality for the capacity-3 weights.** Let $y_i$ be the weights of the capacity-3
lower bound. For every nonempty set $T$ of positive integers with $|T| \le 3$,
$$\sum_{i \in T} y_i + \frac{9}{2}(|T| - 1) \le \max T + \sum_{i \in T} i.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15 (`jis-2026-26.5.6-lem-15`). -/
public theorem_wanted bridgeWeight_local_inequality (T : Finset ℕ) (hT : T.Nonempty)
    (hT3 : T.card ≤ 3) (hpos : 0 ∉ T) :
    (∑ i ∈ T, bridgeWeight i) + 9 / 2 * ((T.card : ℚ) - 1) ≤
      ((T.max' hT : ℕ) : ℚ) + ∑ i ∈ T, (i : ℚ)

/-- **Return inequality for the capacity-3 weights.** Let $y_i$ be the weights of the capacity-3
lower bound. For every nonempty set $R$ of positive integers with $|R| \le 3$,
$$\frac{9}{2}(|R| - 1) + \max R + \sum_{i \in R} (y_i - i) \ge 0.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 16 (`jis-2026-26.5.6-lem-16`). -/
public theorem_wanted bridgeWeight_return_inequality (R : Finset ℕ) (hR : R.Nonempty)
    (hR3 : R.card ≤ 3) (hpos : 0 ∉ R) :
    0 ≤ 9 / 2 * ((R.card : ℚ) - 1) + ((R.max' hR : ℕ) : ℚ) +
      ∑ i ∈ R, (bridgeWeight i - (i : ℚ))

/-- **The capacity-3 closed form is an integer close to the lower bound.** For every integer
$n \ge 7$, let $U(n) = n^2/6 + 2n - 181/36 + (-1)^n/4 - (2/9)\cos(2n\pi/3)$ and
$V(n) = n^2/6 + 2n - 11/2$. Then $U(n)$ is an integer and $0 \le U(n) - V(n) < 1$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 19 (`jis-2026-26.5.6-lem-19`), with `U` from Theorem 12 and `V` from
Proposition 17. -/
public theorem_wanted closedForm_U_integral_and_near_V (n : ℕ) (hn : 7 ≤ n) :
    (∃ z : ℤ, (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
        2 / 9 * Real.cos (2 * n * Real.pi / 3) = z) ∧
      0 ≤ ((n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
          2 / 9 * Real.cos (2 * n * Real.pi / 3)) - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) ∧
      ((n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
          2 / 9 * Real.cos (2 * n * Real.pi / 3)) - ((n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2) < 1


/-- **Closed form for capacity two.** Let $T(n)$ be the optimal crossing time of $n$ people with
crossing times $1, \dots, n$ on a bridge of capacity $2$ with one torch. For every $n \ge 2$,
$$T(n) = \frac{n^2}{4} + 3n - 5 + \frac{(-1)^n - 1}{8}.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (`jis-2026-26.5.6-thm-1`). -/
public theorem_wanted bridgeTime_two_closed_form (n : ℕ) (hn : 2 ≤ n) :
    (bridgeTime 2 n : ℝ) = (n : ℝ) ^ 2 / 4 + 3 * n - 5 + ((-1 : ℝ) ^ n - 1) / 8

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

/-- **Initial values for capacity three.** Let $T_3(n)$ be the optimal crossing time of $n$
people with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. Then
$T_3(1) = 1$, $T_3(2) = 2$, $T_3(3) = 3$, $T_3(4) = 7$, $T_3(5) = 9$ and $T_3(6) = 14$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 8 (`jis-2026-26.5.6-prop-8`). -/
public theorem_wanted bridgeTime_three_initial_values :
    bridgeTime 3 1 = 1 ∧ bridgeTime 3 2 = 2 ∧ bridgeTime 3 3 = 3 ∧ bridgeTime 3 4 = 7 ∧
      bridgeTime 3 5 = 9 ∧ bridgeTime 3 6 = 14

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

/-- **Six-step upper bound for capacity three.** Let $T_3(n)$ be the optimal crossing time of
$n$ people with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For
every $k \ge 9$, $T_3(k) \le T_3(k - 6) + 2k + 6$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 11 (`jis-2026-26.5.6-prop-11`). -/
public theorem_wanted bridgeTime_three_le_sub_six (k : ℕ) (hk : 9 ≤ k) :
    bridgeTime 3 k ≤ bridgeTime 3 (k - 6) + 2 * k + 6

/-- **Upper bound for capacity three.** Let $T_3(n)$ be the optimal crossing time of $n$ people
with crossing times $1, \dots, n$ on a bridge of capacity $3$ with one torch. For every
$n \ge 7$,
$$T_3(n) \le \frac{n^2}{6} + 2n - \frac{181}{36} + \frac{(-1)^n}{4} - \frac{2}{9}\cos(2n\pi/3).$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 12 (`jis-2026-26.5.6-thm-12`). -/
public theorem_wanted bridgeTime_three_le_closed_form (n : ℕ) (hn : 7 ≤ n) :
    (bridgeTime 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
      2 / 9 * Real.cos (2 * n * Real.pi / 3)

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
Definition (admissible bag), Section 3 (journal version). -/
def IsAdmissibleBag (n : ℕ) (F : Multiset (Finset ℕ)) : Prop :=
  (∀ T ∈ F, T.Nonempty ∧ T ⊆ Icc 1 n ∧ T.card ≤ 3) ∧
    (∀ i ∈ Icc 1 n, ∃ T ∈ F, i ∈ T) ∧ (F.map fun T => T.card - 1).sum = n - 1

/-- **Weight of a bag.** For a natural number $n$ and a bag $F$, that is, a finite multiset of
finite sets of natural numbers, the weight of $F$ for $n$ people is the real number
$w(F) = \sum_{T \in F} \left(\max T + \sum_{i \in T} i\right) - \frac{n(n+1)}{2}$, where each
set counts with its multiplicity in $F$ and $\max \emptyset = 0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (admissible bag), Section 3 (journal version). -/
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

/-- **Movement in the star model.** Consider the star graph $\mathcal{S}(k)$ with center $o$ and
leaves $u_0, \dots, u_{k-1}$, and $n$ persons $0, \dots, n-1$, where person $p$ has crossing time
$p + 1$. A movement consists of a set $P$ of persons, a leaf $u_j$ and a direction: the persons in
$P$ carry one torch along the edge $\{o, u_j\}$, outward from $o$ to $u_j$ or inward from $u_j$ to
$o$. No condition is imposed on $P$ here (it may even be empty); which movements may be made
together is part of the definition of a legal step.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), Section 5 (journal version). -/
structure StarMove (n k : ℕ) where
  /-- The persons crossing together. -/
  persons : Finset (Fin n)
  /-- The leaf of the edge traversed. -/
  leaf : Fin k
  /-- Whether the movement goes from the center to the leaf. -/
  outward : Bool
  deriving DecidableEq

/-- **Start vertex of a star movement.** Let $\mathcal{S}(k)$ be the star graph with center $o$
and $k$ leaves. A movement in the star model on $\mathcal{S}(k)$ along the edge $\{o, u\}$ between
the center $o$ and a leaf $u$ starts at $o$ if it goes outward (from the center to the leaf) and
at $u$ otherwise.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def StarMove.src {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then none else some m.leaf

/-- **End vertex of a star movement.** In the star model on the star graph with center $o$ and
leaves $u_0, \dots, u_{k-1}$, a torch-movement along the edge $\{o, u_\ell\}$ ends at the leaf
$u_\ell$ if it goes outward from $o$, and at the center $o$ otherwise.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def StarMove.dst {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then some m.leaf else none

/-- **Legal parallel steps in the star model.** Let $\mathcal{S}(k)$ be the star graph with a
center and $k$ leaves. Consider a configuration of the star model on $\mathcal{S}(k)$ with $n$
persons, given by the vertex $\mathrm{pos}(p)$ of each person $p$ and the number $\mathrm{tor}(v)$
of torches at each vertex $v$. A parallel step, a list of star movements, is legal from this
configuration when every movement carries one or two persons, all standing at the movement's
start vertex; the movements of the step carry pairwise disjoint sets of persons and traverse
pairwise distinct edges; and for every vertex $v$, at most $\mathrm{tor}(v)$ movements of the
step start at $v$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def IsStarStep {n k : ℕ} (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (step : List (StarMove n k)) : Prop :=
  (∀ m ∈ step, 1 ≤ m.persons.card ∧ m.persons.card ≤ 2 ∧ ∀ p ∈ m.persons, pos p = m.src) ∧
    (step.map StarMove.leaf).Nodup ∧ step.Pairwise (fun a b => Disjoint a.persons b.persons) ∧
    ∀ v, (step.filter fun m => m.src = v).length ≤ tor v

instance {n k : ℕ} (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (step : List (StarMove n k)) : Decidable (IsStarStep pos tor step) := by
  unfold IsStarStep; infer_instance

/-- **Positions after a step in the star model.** Given the vertex $\mathrm{pos}(p)$ of each person
$p$ and a step $S$, a finite list of movements, the position of $p$ after $S$ is the end vertex of
the first movement of $S$ whose persons include $p$ (its leaf if the movement is outward, the
center if it is inward), and $\mathrm{pos}(p)$ if no movement of $S$ includes $p$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepPos {n k : ℕ} (pos : Fin n → Option (Fin k)) (step : List (StarMove n k)) :
    Fin n → Option (Fin k) :=
  fun p => match step.find? (fun m => decide (p ∈ m.persons)) with
    | some m => m.dst
    | none => pos p

/-- **Torch counts after a step in the star model.** Given the number $\mathrm{tor}(v)$ of torches
at each vertex $v$ of the star graph and a step $S$, a finite list of movements, the number of
torches at $v$ after $S$ is $\max(\mathrm{tor}(v) - a, 0) + b$, where $a$ is the number of
movements of $S$ that start at $v$ and $b$ is the number of movements of $S$ that end at $v$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepTorch {n k : ℕ} (tor : Option (Fin k) → ℕ) (step : List (StarMove n k)) :
    Option (Fin k) → ℕ :=
  fun v => tor v - (step.filter fun m => m.src = v).length +
    (step.filter fun m => m.dst = v).length

/-- **Duration of a step in the star model.** A step is a finite list of movements carried out in
parallel. Its duration is the largest crossing time $p + 1$ of a person $p$ moving in one of its
movements, and $0$ if no person moves.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepDuration {n k : ℕ} (step : List (StarMove n k)) : ℕ :=
  (step.map fun m => m.persons.sup fun p => (p : ℕ) + 1).foldr max 0

/-- **Legal runs in the star model.** A configuration of the star model assigns to each person $p$
a vertex $\mathrm{pos}(p)$ of the star graph $\mathcal{S}(k)$ and to each vertex $v$ a number
$\mathrm{tor}(v)$ of torches. A finite sequence $\sigma = (S_1, \dots, S_\ell)$ of steps, each a
finite list of movements, is a legal run from the configuration $(\mathrm{pos}, \mathrm{tor})$
when each step $S_i$ is legal from the configuration reached after $S_1, \dots, S_{i-1}$ (a step
updates the positions of the persons and the torch counts) and every person is at a leaf in the
configuration reached after all of $\sigma$. In particular, the empty sequence is a legal run
exactly when every person already stands at a leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starRunFrom {n k : ℕ} :
    (Fin n → Option (Fin k)) → (Option (Fin k) → ℕ) → List (List (StarMove n k)) → Bool
  | pos, _, [] => decide (∀ p, (pos p).isSome)
  | pos, tor, step :: σ =>
      decide (IsStarStep pos tor step) && starRunFrom (starStepPos pos step) (starStepTorch tor step) σ

/-- **Star schedules.** Consider the star model on the star graph $\mathcal{S}(k)$, which has a
center and $k$ leaves, with $n$ persons and $t$ torches. A finite list $\sigma$ of parallel steps
(each a list of star movements) is a star schedule when the following holds. Start from the
configuration with every person and all $t$ torches at the center and no torch at any leaf, and
apply the steps of $\sigma$ in order, where a step moves the persons of each of its movements to
the movement's end vertex and moves one torch from the start vertex to the end vertex of each
movement. Every step must be legal from the configuration it is applied to, and in the final
configuration every person is at some leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def IsStarSchedule (n k t : ℕ) (σ : List (List (StarMove n k))) : Prop :=
  starRunFrom (fun _ => none) (fun v => if v = none then t else 0) σ = true

/-- **Optimal time in the star model.** For $n$ persons, $k$ edges and $t$ torches, $T(n, k, t)$
is the smallest total duration of a star schedule, where the total duration of a schedule is the
sum of the durations of its steps. If no star schedule exists (for example when $n \ge 1$ and
$k = 0$ or $t = 0$), then $T(n, k, t) = 0$ by convention.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
noncomputable def starTime (n k t : ℕ) : ℕ :=
  sInf {d | ∃ σ, IsStarSchedule n k t σ ∧ (σ.map starStepDuration).sum = d}

/-- **Every star schedule bounds the optimal time.** Let $T(n, k, t)$ be the optimal time of
the star model with $n$ persons, $k$ edges and $t$ torches. For every star schedule $\sigma$ with
$n$ persons, $k$ edges and $t$ torches, $T(n, k, t)$ is at most the total duration of $\sigma$,
the sum of the durations of its steps.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), definition of `T(n, k, t)`. -/
theorem starTime_le {n k t : ℕ} {σ : List (List (StarMove n k))}
    (hσ : IsStarSchedule n k t σ) : starTime n k t ≤ (σ.map starStepDuration).sum :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

/-- **Two persons crossing a one-edge star.** In the star model with $2$ persons (crossing times
$1$ and $2$), a star graph with $1$ edge and $1$ torch, the sequence of one step consisting of a
single movement that carries both persons and the torch from the center to the leaf is a star
schedule, and its total duration is $2$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), characteristic example. -/
theorem isStarSchedule_two_one_one :
    IsStarSchedule 2 1 1 [[⟨Finset.univ, 0, true⟩]] ∧
      ([[(⟨Finset.univ, 0, true⟩ : StarMove 2 1)]].map starStepDuration).sum = 2 := by
  unfold IsStarSchedule
  constructor <;> decide

/-- **Example: no return from a leaf without a torch.** In the star model on the star graph
with a center and a single leaf, with one person, suppose the person stands at the leaf, the only
torch is at the center and no torch is at the leaf. Then the parallel step consisting of the
single movement that carries the person from the leaf back to the center is not legal.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), characteristic example. -/
theorem not_isStarStep_return_without_torch :
    ¬ IsStarStep (fun _ : Fin 1 => (some 0 : Option (Fin 1)))
      (fun v => if v = none then 1 else 0) [⟨Finset.univ, 0, false⟩] := by
  decide

/-- **Bridge and torch on star graphs.** Consider the star model with $n \ge 2$ persons of crossing
times $1, \dots, n$, $k \ge 1$ edges and $t \ge 1$ torches, let $T(n, k, t)$ be its optimal time,
and let $m = \min(k, t)$ and $s = \lceil n/(2m) \rceil$. Let $T(n)$ be the optimal crossing time
of $n$ persons with crossing times $1, \dots, n$ on a bridge of capacity $2$ with one torch. Then
$$sn - ms(s-1) \le T(n, k, t) \le T(n),$$
and the left inequality is an equality whenever $t \ge \lceil n/2 \rceil$. Moreover, for all
natural numbers $q$ and $r$ with $n = 2mq + r$ and $r < 2m$,
$$sn - ms(s-1) = \frac{n^2}{4m} + \frac{n}{2} + \frac{r(2m-r)}{4m},$$
and this is at least $n^2/(4m) + n/2$.

For $n \ge 2$ the closed form $T(n) = n^2/4 + 3n - 5 + ((-1)^n - 1)/8$ is Theorem 1 of the same
paper.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 26 (`jis-2026-26.5.6-thm-26`). -/
public theorem_wanted starTime_bounds (n k t : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    let m := min k t
    let s := ⌈(n : ℚ) / (2 * m)⌉₊
    ((s * n : ℕ) : ℝ) - m * s * (s - 1) ≤ starTime n k t ∧
      starTime n k t ≤ bridgeTime 2 n ∧
      ((n + 1) / 2 ≤ t → (starTime n k t : ℝ) = (s * n : ℕ) - m * s * (s - 1)) ∧
      ∀ q r : ℕ, n = 2 * m * q + r → r < 2 * m →
        ((s * n : ℕ) : ℝ) - m * s * (s - 1) = (n : ℝ) ^ 2 / (4 * m) + n / 2 +
            r * (2 * m - r) / (4 * m) ∧
          (n : ℝ) ^ 2 / (4 * m) + n / 2 ≤ ((s * n : ℕ) : ℝ) - m * s * (s - 1)

end

end BridgeTorchGeneralizations

end MetaMathlibExt
