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

/-- The weights `yᵢ` of the capacity-3 lower bound: `y₁ = y₂ = y₃ = 0`,
`y₄ = 2`, `y₅ = 4`, `y₆ = 5`, and `yᵢ = (4i - 8)/3` for `i ≥ 7` (the value at
`i = 0` is unused and set to `0`).

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
def bridgeWeight : ℕ → ℚ
  | 0 | 1 | 2 | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 5
  | i + 7 => (4 * ((i + 7 : ℕ) : ℚ) - 8) / 3

/-- The weights `y₁, …, y₇` are `0, 0, 0, 2, 4, 5, 20/3`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_small :
    bridgeWeight 1 = 0 ∧ bridgeWeight 2 = 0 ∧ bridgeWeight 3 = 0 ∧ bridgeWeight 4 = 2 ∧
      bridgeWeight 5 = 4 ∧ bridgeWeight 6 = 5 ∧ bridgeWeight 7 = 20 / 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [bridgeWeight]
  norm_num

/-- For `i ≥ 7`, `yᵢ = (4i - 8)/3`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_of_seven_le (i : ℕ) (hi : 7 ≤ i) :
    bridgeWeight i = (4 * (i : ℚ) - 8) / 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rfl

/-- Validity of a list of crossings for the bridge and torch problem with bridge
capacity `c` and set of people `P`, starting from the state with left bank `L`
and the torch on the left (`torchLeft = true`) or on the right
(`torchLeft = false`). Each crossing is the set of people who cross; a crossing
from the torch's side carries between `1` and `c` people standing on that side,
and the list must end in the terminal state (empty left bank, torch on the
right).

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 (states and moves) and Section 3 (capacity `c`). -/
def bridgeScheduleFrom (c : ℕ) (P : Finset ℕ) : Finset ℕ → Bool → List (Finset ℕ) → Bool
  | L, torchLeft, [] => decide (L = ∅) && !torchLeft
  | L, true, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ L) && bridgeScheduleFrom c P (L \ A) false σ
  | L, false, A :: σ =>
      decide (A.Nonempty ∧ A.card ≤ c ∧ A ⊆ P \ L) && bridgeScheduleFrom c P (L ∪ A) true σ

/-- `σ` is a complete schedule for the people `{1, …, n}` (person `i` has
crossing time `i`) on a bridge of capacity `c` with one torch: its crossings
alternate forward moves and returns, starting from everyone and the torch on
the left, and end with everyone and the torch on the right.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1 and Section 3. -/
def IsBridgeSchedule (c n : ℕ) (σ : List (Finset ℕ)) : Prop :=
  bridgeScheduleFrom c (Finset.Icc 1 n) (Finset.Icc 1 n) true σ = true

/-- The total time of a schedule: each crossing costs the largest crossing time
(label) of the people in it.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
proof of Theorem 1. -/
def scheduleCost (σ : List (Finset ℕ)) : ℕ :=
  (σ.map fun A => A.sup id).sum

/-- The optimal crossing time of `n` people with crossing times `1, …, n` on a
bridge of capacity `c` with one torch (`T(n)` for `c = 2`, `T₃(n)` for
`c = 3`).

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 and Theorem 12. -/
noncomputable def bridgeTime (c n : ℕ) : ℕ :=
  sInf {t | ∃ σ, IsBridgeSchedule c n σ ∧ scheduleCost σ = t}

/-- The forward moves (left to right) of a schedule: its crossings at even
positions `0, 2, 4, …`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 7. -/
def forwardCrossings {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: forwardCrossings l

/-- The returns (right to left) of a schedule: its crossings at odd positions
`1, 3, 5, …`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 7. -/
def returnCrossings {α : Type*} (σ : List α) : List α :=
  forwardCrossings σ.tail

/-- The right bank after the crossings `τ` (a prefix of a schedule for the
people `{1, …, n}`): the people who have crossed an odd number of times.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 9. -/
def rightBank (n : ℕ) (τ : List (Finset ℕ)) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun p => Odd (τ.countP fun A => decide (p ∈ A))

/-- Any schedule bounds the optimal crossing time from above.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (definition of `T(n)`). -/
theorem bridgeTime_le_scheduleCost {c n : ℕ} {σ : List (Finset ℕ)}
    (hσ : IsBridgeSchedule c n σ) : bridgeTime c n ≤ scheduleCost σ :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

/-- The schedule `{1,2} → R`, `1 → L`, `{1,3} → R`, `1 → L`, `{1,4} → R` of the
paper's table for `n = 4` and capacity `2` is valid and costs `11`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
table after the proof of Theorem 1. -/
theorem isBridgeSchedule_two_four :
    IsBridgeSchedule 2 4 [{1, 2}, {1}, {1, 3}, {1}, {1, 4}] ∧
      scheduleCost [{1, 2}, {1}, {1, 3}, {1}, {1, 4}] = 11 := by
  unfold IsBridgeSchedule
  decide

/-- Crossing with `3 > c` people is invalid: `{1,2,3} → R` is not a schedule for
capacity `2`, but it is one for capacity `3`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 3. -/
theorem isBridgeSchedule_capacity_three :
    ¬ IsBridgeSchedule 2 3 [{1, 2, 3}] ∧ IsBridgeSchedule 3 3 [{1, 2, 3}] := by
  unfold IsBridgeSchedule
  decide

/-- Forward moves, returns and the right bank of the paper's `n = 4` schedule:
the forward moves are `{1,2}, {1,3}, {1,4}`, the returns are `{1}, {1}`, and
after `{1,2} → R`, `1 → L` the right bank is `{2}`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
table after the proof of Theorem 1. -/
theorem forwardCrossings_returnCrossings_rightBank_example :
    forwardCrossings ([{1, 2}, {1}, {1, 3}, {1}, {1, 4}] : List (Finset ℕ)) =
        [{1, 2}, {1, 3}, {1, 4}] ∧
      returnCrossings ([{1, 2}, {1}, {1, 3}, {1}, {1, 4}] : List (Finset ℕ)) = [{1}, {1}] ∧
      rightBank 4 [{1, 2}, {1}] = {2} := by
  decide

/-- A sequence given by `f` on even indices and `g` on odd indices satisfies
`aₙ = ((1 + (-1)ⁿ)/2) f(⌊n/2⌋) + ((1 - (-1)ⁿ)/2) g(⌊n/2⌋)`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 2 (`jis-2026-26.5.6-lem-2`). -/
public theorem_wanted parity_interpolation (f g a : ℕ → ℝ)
    (heven : ∀ m, a (2 * m) = f m) (hodd : ∀ m, a (2 * m + 1) = g m) (n : ℕ) :
    a n = (1 + (-1 : ℝ) ^ n) / 2 * f (n / 2) + (1 - (-1 : ℝ) ^ n) / 2 * g (n / 2)

/-- Local inequality: for every non-empty set `T` of positive integers with
`|T| ≤ 3`, `∑_{i ∈ T} yᵢ + (9/2)(|T| - 1) ≤ max T + ∑_{i ∈ T} i`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15 (`jis-2026-26.5.6-lem-15`). -/
public theorem_wanted bridgeWeight_local_inequality (T : Finset ℕ) (hT : T.Nonempty)
    (hT3 : T.card ≤ 3) (hpos : 0 ∉ T) :
    (∑ i ∈ T, bridgeWeight i) + 9 / 2 * ((T.card : ℚ) - 1) ≤
      ((T.max' hT : ℕ) : ℚ) + ∑ i ∈ T, (i : ℚ)

/-- Return inequality: for every non-empty set `R` of positive integers with
`|R| ≤ 3`, `(9/2)(|R| - 1) + max R + ∑_{i ∈ R} (yᵢ - i) ≥ 0`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 16 (`jis-2026-26.5.6-lem-16`). -/
public theorem_wanted bridgeWeight_return_inequality (R : Finset ℕ) (hR : R.Nonempty)
    (hR3 : R.card ≤ 3) (hpos : 0 ∉ R) :
    0 ≤ 9 / 2 * ((R.card : ℚ) - 1) + ((R.max' hR : ℕ) : ℚ) +
      ∑ i ∈ R, (bridgeWeight i - (i : ℚ))

/-- For `n ≥ 7`, `U(n) = n²/6 + 2n - 181/36 + (-1)ⁿ/4 - (2/9) cos(2nπ/3)` is an
integer and `0 ≤ U(n) - V(n) < 1`, where `V(n) = n²/6 + 2n - 11/2`.

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


/-- The optimal crossing time for capacity `2`: for `n ≥ 2`,
`T(n) = n²/4 + 3n - 5 + ((-1)ⁿ - 1)/8`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 1 (`jis-2026-26.5.6-thm-1`). -/
public theorem_wanted bridgeTime_two_closed_form (n : ℕ) (hn : 2 ≤ n) :
    (bridgeTime 2 n : ℝ) = (n : ℝ) ^ 2 / 4 + 3 * n - 5 + ((-1 : ℝ) ^ n - 1) / 8

/-- For capacity `2` and `n ≥ 1`, the least number of crossings that person `1`
takes part in, over all optimal schedules, is `a(n) = 2⌈n/2⌉ - 1`. Here `a(n)`
is read as a minimum over optimal schedules (the paper's discussion of the
non-uniqueness of optimal schedules); over all schedules the minimum would
be `1`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 6 (`jis-2026-26.5.6-prop-6`). -/
public theorem_wanted bridgeTime_two_least_trips_of_fastest (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {a | ∃ σ, IsBridgeSchedule 2 n σ ∧ scheduleCost σ = bridgeTime 2 n ∧
        σ.countP (fun A => decide (1 ∈ A)) = a} (2 * ((n + 1) / 2) - 1)

/-- For `n ≥ 3`, every capacity-`2` schedule `σ` in which person `1` takes part
in `a` forward moves, `m` returns carry two people and `s` forward moves carry
one person costs at least `T(n) + ⌈n/2⌉ - a + 4m + 3s`.

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

/-- Initial values of the capacity-`3` optimal time:
`T₃(1), …, T₃(6) = 1, 2, 3, 7, 9, 14`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 8 (`jis-2026-26.5.6-prop-8`). -/
public theorem_wanted bridgeTime_three_initial_values :
    bridgeTime 3 1 = 1 ∧ bridgeTime 3 2 = 2 ∧ bridgeTime 3 3 = 3 ∧ bridgeTime 3 4 = 7 ∧
      bridgeTime 3 5 = 9 ∧ bridgeTime 3 6 = 14

/-- For capacity `3` and `n ≥ 1` there is an optimal schedule in which every
return is made by a single person who is the fastest person then on the right
bank.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 9 (`jis-2026-26.5.6-lem-9`). -/
public theorem_wanted exists_optimal_schedule_three_fastest_returns (n : ℕ) (hn : 1 ≤ n) :
    ∃ σ, IsBridgeSchedule 3 n σ ∧ scheduleCost σ = bridgeTime 3 n ∧
      ∀ (i : ℕ) (hi : i < σ.length), Odd i →
        ∃ p, σ[i] = {p} ∧ ∀ q ∈ rightBank n (σ.take i), p ≤ q

/-- For `k ≥ 9`, `T₃(k) ≤ T₃(k - 6) + 2k + 6`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 11 (`jis-2026-26.5.6-prop-11`). -/
public theorem_wanted bridgeTime_three_le_sub_six (k : ℕ) (hk : 9 ≤ k) :
    bridgeTime 3 k ≤ bridgeTime 3 (k - 6) + 2 * k + 6

/-- For `n ≥ 7`, `T₃(n) ≤ U(n) = n²/6 + 2n - 181/36 + (-1)ⁿ/4 - (2/9) cos(2nπ/3)`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 12 (`jis-2026-26.5.6-thm-12`). -/
public theorem_wanted bridgeTime_three_le_closed_form (n : ℕ) (hn : 7 ≤ n) :
    (bridgeTime 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
      2 / 9 * Real.cos (2 * n * Real.pi / 3)

/-- For `n ≥ 7`, every capacity-`3` schedule costs at least
`V(n) = n²/6 + 2n - 11/2`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 17 (`jis-2026-26.5.6-prop-17`). -/
public theorem_wanted scheduleCost_three_lower_bound (n : ℕ) (hn : 7 ≤ n)
    (σ : List (Finset ℕ)) (hσ : IsBridgeSchedule 3 n σ) :
    (n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2 ≤ scheduleCost σ

/-- The optimal crossing time for capacity `3`: for `n ≥ 7`,
`T₃(n) = n²/6 + 2n - 181/36 + (-1)ⁿ/4 - (2/9) cos(2nπ/3)`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 20 (`jis-2026-26.5.6-thm-20`). -/
public theorem_wanted bridgeTime_three_closed_form (n : ℕ) (hn : 7 ≤ n) :
    (bridgeTime 3 n : ℝ) = (n : ℝ) ^ 2 / 6 + 2 * n - 181 / 36 + (-1 : ℝ) ^ n / 4 -
      2 / 9 * Real.cos (2 * n * Real.pi / 3)

/-- For `n ≥ 13`, `T₃(n) = T₃(n - 6) + 2n + 6`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Corollary 21 (`jis-2026-26.5.6-cor-21`). -/
public theorem_wanted bridgeTime_three_recurrence (n : ℕ) (hn : 13 ≤ n) :
    bridgeTime 3 n = bridgeTime 3 (n - 6) + 2 * n + 6


/-- An admissible bag for `n` people (capacity `3`): a finite multiset `F` of nonempty subsets
of `{1, …, n}` such that (i) `|T| ≤ 3` for every `T ∈ F`, (ii) every `i ∈ {1, …, n}` lies in
some `T ∈ F`, and (iii) `∑_{T ∈ F} (|T| - 1) = n - 1`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (admissible bag), Section 3 (journal version). -/
def IsAdmissibleBag (n : ℕ) (F : Multiset (Finset ℕ)) : Prop :=
  (∀ T ∈ F, T.Nonempty ∧ T ⊆ Icc 1 n ∧ T.card ≤ 3) ∧
    (∀ i ∈ Icc 1 n, ∃ T ∈ F, i ∈ T) ∧ (F.map fun T => T.card - 1).sum = n - 1

/-- The weight `w(F) = ∑_{T ∈ F} (max T + ∑_{i ∈ T} i) - n(n+1)/2` of a bag `F` for `n` people.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (admissible bag), Section 3 (journal version). -/
noncomputable def bagWeight (n : ℕ) (F : Multiset (Finset ℕ)) : ℝ :=
  (((F.map fun T => T.sup id + ∑ i ∈ T, i).sum : ℕ) : ℝ) - n * (n + 1) / 2

/-- The one-trip bag `{{1, 2, 3}}` is admissible for three people and has weight `3 = T₃(3)`.

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

/-- A schedule for capacity `3` whose returns each carry exactly one person has an admissible
bag of forward trips `F(σ)`, and its total cost is `w(F(σ))`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 14 (`jis-2026-26.5.6-prop-14`), first assertion. -/
public theorem_wanted isAdmissibleBag_forwardCrossings_of_single_returns (n : ℕ)
    (σ : List (Finset ℕ)) (hσ : IsBridgeSchedule 3 n σ)
    (hret : ∀ A ∈ returnCrossings σ, A.card = 1) :
    IsAdmissibleBag n (forwardCrossings σ : Multiset (Finset ℕ)) ∧
      (scheduleCost σ : ℝ) = bagWeight n (forwardCrossings σ : Multiset (Finset ℕ))

/-- `T₃(n) ≥ B₃(n)`: some admissible bag has weight at most `T₃(n)`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Proposition 14 (`jis-2026-26.5.6-prop-14`), consequence. -/
public theorem_wanted exists_isAdmissibleBag_bagWeight_le_bridgeTime_three (n : ℕ) :
    ∃ F, IsAdmissibleBag n F ∧ bagWeight n F ≤ bridgeTime 3 n

/-- `B₃(n) ≥ V(n)`: for `n ≥ 7` every admissible bag has weight at least
`V(n) = n²/6 + 2n - 11/2`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Corollary 18 (`jis-2026-26.5.6-cor-18`). -/
public theorem_wanted bagWeight_ge_of_isAdmissibleBag (n : ℕ) (hn : 7 ≤ n)
    (F : Multiset (Finset ℕ)) (hF : IsAdmissibleBag n F) :
    (n : ℝ) ^ 2 / 6 + 2 * n - 11 / 2 ≤ bagWeight n F

/-- A torch-movement in the star model on the star graph `𝒮(k)` with center `o` and leaves
`u₀, …, u_{k-1}`: the persons `persons` (person `p : Fin n` has crossing time `p + 1`) carry one
torch along the edge `{o, u_leaf}`, from `o` to `u_leaf` if `outward` and back otherwise.
Vertices are `Option (Fin k)`, with `none` the center.

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

/-- The vertex a movement starts from.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def StarMove.src {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then none else some m.leaf

/-- The vertex a movement ends at.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def StarMove.dst {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then some m.leaf else none

/-- A parallel step `step` is legal from the configuration (`pos` = vertex of each person,
`tor` = number of torches at each vertex): every movement carries one or two persons all at its
start vertex, the movements use pairwise disjoint persons and pairwise distinct edges, and at
each vertex at most as many movements start as there are torches there.

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

/-- The positions of the persons after a step.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepPos {n k : ℕ} (pos : Fin n → Option (Fin k)) (step : List (StarMove n k)) :
    Fin n → Option (Fin k) :=
  fun p => match step.find? (fun m => decide (p ∈ m.persons)) with
    | some m => m.dst
    | none => pos p

/-- The torch counts after a step: each movement moves one torch from its start to its end.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepTorch {n k : ℕ} (tor : Option (Fin k) → ℕ) (step : List (StarMove n k)) :
    Option (Fin k) → ℕ :=
  fun v => tor v - (step.filter fun m => m.src = v).length +
    (step.filter fun m => m.dst = v).length

/-- The duration of a step: the largest crossing time among all persons moving in it.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starStepDuration {n k : ℕ} (step : List (StarMove n k)) : ℕ :=
  (step.map fun m => m.persons.sup fun p => (p : ℕ) + 1).foldr max 0

/-- `σ` is a legal sequence of parallel steps from the configuration (`pos`, `tor`) that ends
with every person at a leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def starRunFrom {n k : ℕ} :
    (Fin n → Option (Fin k)) → (Option (Fin k) → ℕ) → List (List (StarMove n k)) → Bool
  | pos, _, [] => decide (∀ p, (pos p).isSome)
  | pos, tor, step :: σ =>
      decide (IsStarStep pos tor step) && starRunFrom (starStepPos pos step) (starStepTorch tor step) σ

/-- `σ` solves the star model with `n` persons, `k` edges and `t` torches: starting with all
persons and all `t` torches at the center, it reaches a configuration with every person at a
leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
def IsStarSchedule (n k t : ℕ) (σ : List (List (StarMove n k))) : Prop :=
  starRunFrom (fun _ => none) (fun v => if v = none then t else 0) σ = true

/-- The minimum total duration `T(n, k, t)` of the star model.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model). -/
noncomputable def starTime (n k t : ℕ) : ℕ :=
  sInf {d | ∃ σ, IsStarSchedule n k t σ ∧ (σ.map starStepDuration).sum = d}

/-- Any star schedule bounds `T(n, k, t)` from above.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), definition of `T(n, k, t)`. -/
theorem starTime_le {n k t : ℕ} {σ : List (List (StarMove n k))}
    (hσ : IsStarSchedule n k t σ) : starTime n k t ≤ (σ.map starStepDuration).sum :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

/-- Two persons and one torch on `𝒮(1)`: the single step moving both persons to the leaf is a
star schedule of duration `2`.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), characteristic example. -/
theorem isStarSchedule_two_one_one :
    IsStarSchedule 2 1 1 [[⟨Finset.univ, 0, true⟩]] ∧
      ([[(⟨Finset.univ, 0, true⟩ : StarMove 2 1)]].map starStepDuration).sum = 2 := by
  unfold IsStarSchedule
  constructor <;> decide

/-- A step that sends a person from a leaf with no torch is not legal: one person at the center
with the only torch cannot return from the leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Definition (the star model), characteristic example. -/
theorem not_isStarStep_return_without_torch :
    ¬ IsStarStep (fun _ : Fin 1 => (some 0 : Option (Fin 1)))
      (fun v => if v = none then 1 else 0) [⟨Finset.univ, 0, false⟩] := by
  decide

/-- Bridge and torch on star graphs. In the star model with `n ≥ 2` persons of crossing times
`1, …, n`, `k ≥ 1` edges and `t ≥ 1` torches, let `m = min(k, t)` and `s = ⌈n/(2m)⌉`. Then
`sn - ms(s-1) ≤ T(n, k, t) ≤ T(n)`, with equality on the left whenever `t ≥ ⌈n/2⌉`; and for
`n = 2mq + r` with `0 ≤ r < 2m`, `sn - ms(s-1) = n²/(4m) + n/2 + r(2m-r)/(4m) ≥ n²/(4m) + n/2`.

`T(n)` is the one-bridge capacity-`2` time `bridgeTime 2 n`; its closed form
`n²/4 + 3n - 5 + ((-1)ⁿ - 1)/8` is Theorem 1 (`bridgeTime_two_closed_form`) and is not
restated.

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
