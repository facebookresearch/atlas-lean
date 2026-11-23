/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr

/-!
# The weighted majority algorithm: mistake bound

Prediction with expert advice (Littlestone and Warmuth, *The weighted majority algorithm*,
Information and Computation 108, 1994): in each round `n` experts give binary advice, the
algorithm predicts the weighted majority (`predict`), the outcome is revealed, and every wrong
expert has its weight multiplied by a penalty factor `β ∈ [0, 1]` (`update`). Starting from unit
weights, the algorithm's mistakes `M` are bounded against every expert's mistakes `m`. Weights
live in any linearly ordered field (exact rationals for computation, reals for analysis).

Main results:

* `total_update_of_mistake`: a mistake leaves at most a `(1 + β)/2` fraction of the total weight;
  `total_update_le`: no round increases it; `total_weights_mul_le`: hence
  `total_final * 2 ^ M ≤ (1 + β) ^ M * total_initial`.
* `weights_apply`: expert `i`'s final weight is `β ^ m_i`.
* `mistake_bound_general`: `β ^ m_i * 2 ^ M ≤ n (1 + β) ^ M` for every expert `i` and
  `β ∈ [0, 1]`. For `0 < β < 1` (where both logarithms below are positive) taking logarithms gives
  `M ≤ (m_i log (1/β) + log n) / log (2 / (1 + β))`. At `β = 1` the multiplicative form only says
  `1 ≤ n`; at `β = 0` it gives the halving algorithm's `2 ^ M ≤ n` against an expert with no
  mistakes and nothing against the others.
* `mistake_bound`, `mistake_bound_nat`: the classical penalty `β = 1/2` over `ℚ`:
  `(4/3) ^ M ≤ n 2 ^ m_i`, and in integers `4 ^ M ≤ n 3 ^ M 2 ^ m_i`, so
  `M ≤ (m_i + log₂ n) / log₂ (4/3)`.
* `weights_append`, `mistakes_append`: a run splits at any round.

## Relation to `FormalizedTextbooks`

`FormalizedTextbooks/IntroductionToOnlineConvexOptimization/OnlineLearning/Hedge.lean` derives
Hazan's Lemma 1.1, `weighted_majority_bound` (penalty `1 - ε` with `0 < ε < 1/2`,
`M ≤ 2 (1 + ε) m_i + 2 log N / ε`), from `mistake_bound_general` with `β = 1 - ε` over `ℝ`, by
running this algorithm on rounds built from the textbook's mistake indicators.

## Cost model

The cost is the number of mistakes; weights are elements of an ordered field (exact rationals in
the executed tests).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.WeightedMajority

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- **Round of prediction with expert advice.** A round with $n$ experts is a pair $(a, y)$, where
$a$ assigns to each expert $i \in \{0, \dots, n - 1\}$ its binary advice (true or false) and the
binary value $y$ is the true outcome. -/
abbrev Round (n : ℕ) := (Fin n → Bool) × Bool

/-- **Weight on an answer.** Given weights $w_0, \dots, w_{n-1}$ in a field $K$, advice
$a \in \{\mathrm{true}, \mathrm{false}\}^n$ and an answer $b \in \{\mathrm{true}, \mathrm{false}\}$,
the weight on $b$ is $\sum_{i : a_i = b} w_i$, the total weight of the experts advising $b$. -/
def weightOn (w : Fin n → K) (advice : Fin n → Bool) (b : Bool) : K :=
  ∑ i ∈ univ.filter (fun i => advice i = b), w i

/-- **Weighted majority vote.** Let $K$ be a field with a linear order. Given weights in $K$ on
$n$ experts and a binary advice (true or false) from each expert, the weighted majority vote is
true when the total weight of the experts advising false is at most the total weight of the
experts advising true, and false otherwise. In particular ties go to true. -/
def predict (w : Fin n → K) (advice : Fin n → Bool) : Bool :=
  decide (weightOn w advice false ≤ weightOn w advice true)

/-- **Weighted majority update.** Given a penalty factor $\beta$ and weights $w_0, \dots, w_{n-1}$
in a field $K$, and a round with advice $a \in \{\mathrm{true}, \mathrm{false}\}^n$ and outcome
$y$, the updated weight of expert $i$ is $w_i$ if $a_i = y$ and $\beta w_i$ otherwise: after the
outcome is revealed, every expert that was wrong has its weight multiplied by $\beta$. -/
def update (β : K) (w : Fin n → K) (r : Round n) : Fin n → K :=
  fun i => if r.1 i = r.2 then w i else β * w i

/-- **Weights after a run.** For a penalty factor $\beta$ in a field $K$, the weights after a
sequence of rounds $r_1, \dots, r_k$ starting from weights $w$ in $K$ are obtained by applying the
weighted majority update with penalty $\beta$ for $r_1$, then for $r_2$, and so on up to $r_k$;
for the empty sequence they are $w$. -/
def weights (β : K) : List (Round n) → (Fin n → K) → Fin n → K
  | [], w => w
  | r :: rs, w => weights β rs (update β w r)

/-- **Mistakes of the weighted majority algorithm.** Let $K$ be a field with a linear order, let
$\beta \in K$ be a penalty and let $w$ be initial weights in $K$ on $n$ experts. The weighted
majority algorithm processes a list of rounds in order: in each round it predicts the weighted
majority vote of the experts' advice under the current weights, and then multiplies the weight of
every expert whose advice differed from the true outcome by $\beta$. Its number of mistakes is the
number of rounds in which its prediction differs from the true outcome. -/
def mistakes (β : K) : List (Round n) → (Fin n → K) → ℕ
  | [], _ => 0
  | r :: rs, w => (if predict w r.1 = r.2 then 0 else 1) + mistakes β rs (update β w r)

/-- **Mistakes of an expert.** Given a list of rounds with $n$ experts and an expert $i$, the
number of mistakes of $i$ is the number of rounds in the list in which the advice of expert $i$
differs from the true outcome. -/
def expertMistakes (i : Fin n) (rs : List (Round n)) : ℕ := (rs.filter fun r => r.1 i ≠ r.2).length

/-- **Total weight.** The total weight of weights $w_0, \dots, w_{n-1}$ in a field $K$ is
$\sum_{i < n} w_i$. -/
def total (w : Fin n → K) : K := ∑ i, w i

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem total_eq_weightOn (w : Fin n → K) (advice : Fin n → Bool) :
    total w = weightOn w advice true + weightOn w advice false := by
  simpa only [total, weightOn, Bool.not_eq_true] using
    (sum_filter_add_sum_filter_not (univ : Finset (Fin n))
      (fun i => advice i = true) w).symm

/-- **Total weight after an update.** Let $\beta$ be an element of a linearly ordered field $K$,
let $w_0, \dots, w_{n-1} \in K$ be weights on $n$ experts, and let $r$ be a round with advice
$a \in \{\mathrm{true}, \mathrm{false}\}^n$ and outcome $y$. If $w'$ are the weights after the
update with penalty $\beta$ on $r$, then
$\sum_{i < n} w'_i = \sum_{i < n} w_i - (1 - \beta) \sum_{i : a_i = \lnot y} w_i$: the experts
that advised wrongly keep a $\beta$ fraction of their weight. -/
theorem total_update (β : K) (w : Fin n → K) (r : Round n) :
    total (update β w r) = total w - (1 - β) * weightOn w r.1 (!r.2) := by
  have hsplit := total_eq_weightOn w r.1
  unfold total update weightOn at *
  rw [← sum_filter_add_sum_filter_not univ (fun i => r.1 i = r.2)]
  have h1 : ∑ i ∈ univ.filter (fun i => r.1 i = r.2),
      (if r.1 i = r.2 then w i else β * w i) = ∑ i ∈ univ.filter (fun i => r.1 i = r.2), w i :=
    sum_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
  have h2 : ∑ i ∈ univ.filter (fun i => ¬ r.1 i = r.2),
      (if r.1 i = r.2 then w i else β * w i) =
      ∑ i ∈ univ.filter (fun i => ¬ r.1 i = r.2), β * w i :=
    sum_congr rfl fun i hi => by simp [(mem_filter.1 hi).2]
  have hwrong : univ.filter (fun i => ¬ r.1 i = r.2) = univ.filter (fun i => r.1 i = !r.2) := by
    ext i; cases r.2 <;> cases r.1 i <;> simp
  rw [h1, h2, ← mul_sum, hwrong]
  have hall := sum_filter_add_sum_filter_not univ (fun i => r.1 i = r.2) w
  rw [hwrong] at hall
  cases hr : r.2 <;> simp only [hr, Bool.not_false, Bool.not_true] at hall hsplit ⊢ <;>
    linear_combination hall

/-- **A mistake costs weight.** Let $K$ be a linearly ordered field, let $\beta \in K$ with
$\beta \le 1$, let $w$ be weights in $K$ on $n$ experts, and let $r$ be a round on which the
weighted majority vote under $w$ differs from the true outcome. If $W$ is the total weight of $w$
and $W'$ is the total weight after updating $w$ on $r$ with penalty $\beta$, then
$2 W' \le (1 + \beta) W$.

At least half of the weight was on the wrong side, and that side keeps only a $\beta$ fraction of
its weight. -/
theorem total_update_of_mistake {β : K} (hβ1 : β ≤ 1) {w : Fin n → K} {r : Round n}
    (h : predict w r.1 ≠ r.2) : 2 * total (update β w r) ≤ (1 + β) * total w := by
  rw [total_update, total_eq_weightOn w r.1]
  have h1β : 0 ≤ 1 - β := sub_nonneg.2 hβ1
  cases hr : r.2
  · have h' : weightOn w r.1 false ≤ weightOn w r.1 true := by
      have := h; rw [hr] at this; simpa [predict] using this
    simp only [Bool.not_false]
    nlinarith
  · have h' : weightOn w r.1 true < weightOn w r.1 false := by
      have := h; rw [hr] at this; simpa [predict] using this
    simp only [Bool.not_true]
    nlinarith

theorem weightOn_nonneg {w : Fin n → K} (hw : ∀ i, 0 ≤ w i) (advice : Fin n → Bool) (b : Bool) :
    0 ≤ weightOn w advice b := sum_nonneg fun i _ => hw i

/-- **An update never increases the total weight.** Let $K$ be a linearly ordered field, let
$\beta \in K$ with $\beta \le 1$, and let $w$ be nonnegative weights in $K$ on $n$ experts. For
every round $r$, the total weight after updating $w$ on $r$ with penalty $\beta$ is at most the
total weight of $w$. -/
theorem total_update_le {β : K} (hβ1 : β ≤ 1) {w : Fin n → K} (hw : ∀ i, 0 ≤ w i)
    (r : Round n) : total (update β w r) ≤ total w := by
  rw [total_update]
  have := weightOn_nonneg hw r.1 (!r.2)
  have h1β : 0 ≤ 1 - β := sub_nonneg.2 hβ1
  nlinarith

theorem update_nonneg {β : K} (hβ0 : 0 ≤ β) {w : Fin n → K} (hw : ∀ i, 0 ≤ w i) (r : Round n)
    (i : Fin n) : 0 ≤ update β w r i := by
  unfold update
  split_ifs
  · exact hw i
  · exact mul_nonneg hβ0 (hw i)

/-- **Total weight bound in terms of mistakes.** Let $0 \le \beta \le 1$ in a linearly ordered
field $K$, let $w$ be nonnegative weights in $K$ on $n$ experts, and let $\rho$ be a sequence of
rounds. Let $M$ be the number of mistakes the weighted majority algorithm with penalty $\beta$
makes on $\rho$ starting from $w$, and let $W$ and $W'$ be the total weights before and after
$\rho$. Then $W' \cdot 2^M \le (1 + \beta)^M \cdot W$. -/
theorem total_weights_mul_le {β : K} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∀ (rs : List (Round n)) (w : Fin n → K), (∀ i, 0 ≤ w i) →
    total (weights β rs w) * 2 ^ mistakes β rs w ≤ (1 + β) ^ mistakes β rs w * total w
  | [], w, _ => by simp [weights, mistakes]
  | r :: rs, w, hw => by
      have ih := total_weights_mul_le hβ0 hβ1 rs (update β w r) (update_nonneg hβ0 hw r)
      have hpow : 0 ≤ (1 + β) ^ mistakes β rs (update β w r) := pow_nonneg (by linarith) _
      simp only [weights, mistakes]
      by_cases hm : predict w r.1 = r.2
      · simp only [hm, ↓reduceIte, Nat.zero_add]
        exact ih.trans (mul_le_mul_of_nonneg_left (total_update_le hβ1 hw r) hpow)
      · simp only [hm, ↓reduceIte]
        have hstep := total_update_of_mistake hβ1 hm
        rw [Nat.add_comm, pow_succ, pow_succ]
        calc total (weights β rs (update β w r)) * (2 ^ mistakes β rs (update β w r) * 2)
            = total (weights β rs (update β w r)) * 2 ^ mistakes β rs (update β w r) * 2 := by
              ring
          _ ≤ (1 + β) ^ mistakes β rs (update β w r) * total (update β w r) * 2 := by linarith
          _ = (1 + β) ^ mistakes β rs (update β w r) * (2 * total (update β w r)) := by ring
          _ ≤ (1 + β) ^ mistakes β rs (update β w r) * ((1 + β) * total w) :=
              mul_le_mul_of_nonneg_left hstep hpow
          _ = (1 + β) ^ mistakes β rs (update β w r) * (1 + β) * total w := by ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Final weight of an expert.** For a penalty factor $\beta$ in a field $K$, initial weights
$w_0, \dots, w_{n-1} \in K$ and a sequence of rounds, the weight of expert $i$ after these rounds
is $w_i \beta^{m_i}$, where $m_i$ is the number of rounds in which the advice of expert $i$
differs from the outcome. -/
theorem weights_apply (β : K) : ∀ (rs : List (Round n)) (w : Fin n → K) (i : Fin n),
    weights β rs w i = w i * β ^ expertMistakes i rs
  | [], w, i => by simp [weights, expertMistakes]
  | r :: rs, w, i => by
      rw [weights, weights_apply β rs (update β w r) i]
      unfold update expertMistakes
      by_cases h : r.1 i = r.2
      · simp [h]
      · simp only [h, ↓reduceIte, List.filter_cons, ne_eq, not_false_eq_true, decide_true,
          List.length_cons, pow_succ]
        ring

theorem weights_nonneg {β : K} (hβ0 : 0 ≤ β) : ∀ (rs : List (Round n)) {w : Fin n → K},
    (∀ i, 0 ≤ w i) → ∀ i, 0 ≤ weights β rs w i
  | [], _, hw => hw
  | r :: rs, _, hw => weights_nonneg hβ0 rs (update_nonneg hβ0 hw r)

/-- **Littlestone–Warmuth mistake bound.** Let $K$ be a linearly ordered field and let
$\beta \in K$ with $0 \le \beta \le 1$. Run the weighted majority algorithm with penalty $\beta$
on a list of rounds with $n$ experts, starting from weight $1$ on every expert, and let $M$ be its
number of mistakes. Then every expert $i$, with $m$ mistakes on these rounds, satisfies
$\beta^m 2^M \le n (1 + \beta)^M$. -/
theorem mistake_bound_general {β : K} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (rs : List (Round n))
    (i : Fin n) :
    β ^ expertMistakes i rs * 2 ^ mistakes β rs (fun _ => 1) ≤
      n * (1 + β) ^ mistakes β rs (fun _ => 1) := by
  have h1 := total_weights_mul_le hβ0 hβ1 rs (fun _ => 1) fun _ => zero_le_one
  have hi : weights β rs (fun _ => 1) i ≤ total (weights β rs fun _ => 1) :=
    single_le_sum (fun j _ => weights_nonneg hβ0 rs (fun _ => zero_le_one) j) (mem_univ i)
  rw [weights_apply, one_mul] at hi
  have htot : total (fun _ : Fin n => (1 : K)) = n := by simp [total]
  rw [htot] at h1
  have h2 : (0 : K) ≤ 2 ^ mistakes β rs (fun _ => 1) := by positivity
  calc β ^ expertMistakes i rs * 2 ^ mistakes β rs (fun _ => 1)
      ≤ total (weights β rs fun _ => 1) * 2 ^ mistakes β rs (fun _ => 1) :=
        mul_le_mul_of_nonneg_right hi h2
    _ ≤ (1 + β) ^ mistakes β rs (fun _ => 1) * n := h1
    _ = n * (1 + β) ^ mistakes β rs (fun _ => 1) := mul_comm _ _

/-- **Mistake bound for the penalty $1/2$.** Run the weighted majority algorithm with rational
weights and penalty $1/2$ on a list of rounds with $n$ experts, starting from weight $1$ on every
expert, and let $M$ be its number of mistakes. Then every expert $i$, with $m$ mistakes on these
rounds, satisfies $(4/3)^M \le n \cdot 2^m$. -/
theorem mistake_bound (rs : List (Round n)) (i : Fin n) :
    (4 / 3 : ℚ) ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) ≤ n * 2 ^ expertMistakes i rs := by
  have h := mistake_bound_general (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num) rs i
  set M := mistakes (1 / 2 : ℚ) rs (fun _ => 1)
  set m := expertMistakes i rs
  have h32 : (0 : ℚ) < (1 + 1 / 2) ^ M := by positivity
  have h2m : (0 : ℚ) < 2 ^ m := by positivity
  have e1 : (4 / 3 : ℚ) ^ M * (1 + 1 / 2) ^ M = 2 ^ M := by rw [← mul_pow]; norm_num
  have e2 : (1 / 2 : ℚ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  have key : (4 / 3 : ℚ) ^ M * (1 + 1 / 2) ^ M ≤ n * 2 ^ m * (1 + 1 / 2) ^ M := by
    have h' : (1 / 2 : ℚ) ^ m * 2 ^ M * 2 ^ m ≤ n * (1 + 1 / 2) ^ M * 2 ^ m :=
      mul_le_mul_of_nonneg_right h h2m.le
    rw [e1]
    calc (2 : ℚ) ^ M = (1 / 2 : ℚ) ^ m * 2 ^ M * 2 ^ m := by
          rw [mul_comm ((1 / 2 : ℚ) ^ m), mul_assoc, e2, mul_one]
      _ ≤ n * (1 + 1 / 2) ^ M * 2 ^ m := h'
      _ = n * 2 ^ m * (1 + 1 / 2) ^ M := by ring
  exact le_of_mul_le_mul_right key h32

/-- **Mistake bound for the penalty $1/2$ in integers.** Run the weighted majority algorithm
with rational weights and penalty $1/2$ on a list of rounds with $n$ experts, starting from
weight $1$ on every expert, and let $M$ be its number of mistakes. Then every expert $i$, with
$m$ mistakes on these rounds, satisfies $4^M \le n \cdot 3^M \cdot 2^m$ in the natural numbers.

Taking logarithms, $M \le (m + \log_2 n) / \log_2 (4/3) \approx 2.41 (m + \log_2 n)$. -/
theorem mistake_bound_nat (rs : List (Round n)) (i : Fin n) :
    4 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) ≤
      n * 3 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) * 2 ^ expertMistakes i rs := by
  have h := mistake_bound rs i
  have h3 : (0 : ℚ) < 3 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) := by positivity
  rw [div_pow, div_le_iff₀ h3] at h
  exact_mod_cast (show ((4 : ℚ) ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1)) ≤
    n * 3 ^ mistakes (1 / 2 : ℚ) rs (fun _ => 1) * 2 ^ expertMistakes i rs by linarith)

/-! ## Splitting a run -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Weights over a concatenated run.** For a penalty factor $\beta$ in a field $K$, initial
weights $w$ in $K$ and sequences of rounds $\rho$ and $\rho'$, the weights after running $\rho$
followed by $\rho'$ from $w$ equal the weights after running $\rho'$ from the weights obtained by
running $\rho$ from $w$. -/
theorem weights_append (β : K) : ∀ (rs rs' : List (Round n)) (w : Fin n → K),
    weights β (rs ++ rs') w = weights β rs' (weights β rs w)
  | [], _, _ => rfl
  | r :: rs, rs', w => weights_append β rs rs' (update β w r)

omit [IsStrictOrderedRing K] in
/-- **Mistakes split over concatenated runs.** Let $K$ be a field with a linear order, let
$\beta \in K$ be a penalty, let $w$ be weights in $K$ on $n$ experts, and let $R$ and $R'$ be
lists of rounds. The number of mistakes of the weighted majority algorithm with penalty $\beta$
on $R$ followed by $R'$, starting from $w$, equals its number of mistakes on $R$ starting from
$w$ plus its number of mistakes on $R'$ starting from the weights reached after $R$. -/
theorem mistakes_append (β : K) : ∀ (rs rs' : List (Round n)) (w : Fin n → K),
    mistakes β (rs ++ rs') w = mistakes β rs w + mistakes β rs' (weights β rs w)
  | [], _, _ => by simp [mistakes, weights]
  | r :: rs, rs', w => by
      simp only [List.cons_append, mistakes, weights, mistakes_append β rs rs' (update β w r)]
      omega

end Cslib.MachineLearning.WeightedMajority
