/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Halving
public import Cslib.MachineLearning.PACLearning.VersionSpace
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Online binary classification: mistakes and regret

In online binary classification (Shalev-Shwartz and Ben-David, Sections 21.1 and 21.2), each round
proceeds as follows: the environment reveals an instance `x_t ∈ X`, the learner outputs a
prediction, and then the label `y_t ∈ {0, 1}` is revealed. Labels are Booleans (`false` for `0`,
`true` for `1`), and a sequence of examples is a list `S = [(x_1, y_1), …, (x_T, y_T)]`. A learner
is a map from the earlier examples and the current instance to its prediction: in the round
`t : Fin S.length`, counted from `0`, it sees the list `S.take t` of the `t` earlier examples and
the instance `S[t].1`. The same map serves every round and every sequence.

* `mistakes A S`: a deterministic learner `A` predicts labels `ŷ_t` and makes
  `∑_t 1[ŷ_t ≠ y_t]` mistakes. A hypothesis `h : X → Bool` is the learner that predicts `h x_t`,
  whose mistakes are CSLib's `PACLearning.empiricalMiscount` (`mistakes_const`), and the halving
  algorithm is the learner `Halving.halvingPredict C` (`halvingMistakes_eq_mistakes`).
* `expectedMistakes A S`: a randomized learner `A` outputs `p_t ∈ [0, 1]` and then predicts `1`
  with probability `p_t`; its expected number of mistakes is `∑_t |p_t - y_t|`.
  `integral_mistakes_eq_expectedMistakes`: if the predictions are independent, `ŷ_t` following
  the Bernoulli distribution of parameter `p_t`, the expected number of mistakes is
  `expectedMistakes A S`. `expectedMistakes_le` and `expectedMistakes_lt`: it is at most the
  number `∑_t 1[p_t ≠ y_t]` of rounds with `p_t ≠ y_t`, and smaller as soon as some `p_t` lies
  strictly between `0` and `1`. `expectedMistakes_ofBool`: for a deterministic learner it is the
  number of mistakes.
* `regret A H S`: `∑_t |p_t - y_t| - min_{h ∈ H} ∑_t |h(x_t) - y_t|`. The minimum is attained when
  `H` is nonempty, and is replaced by `0` for the empty class, a separate convention. For a nonempty
  class it is the largest of the differences
  `∑_t |p_t - y_t| - ∑_t |h(x_t) - y_t|`, `h ∈ H` (`sub_mistakes_le_regret`, `exists_regret_eq`).
  A sequence is realizable by `H` when it is CSLib's `PACLearning.Realizable H (fun t => S[t])`
  (`realizable_iff`); the regret on it is the expected number of mistakes
  (`regret_of_realizable`).

## Environments

A deterministic learner's predictions are functions of the earlier examples, so an adaptive
environment, which chooses `x_t` and `y_t` after seeing the earlier predictions, produces a single
sequence `S` against it: a statement about every sequence covers such environments. The
expectation over a randomized learner's predictions is taken on a fixed sequence, as an oblivious
environment chooses it in advance. This loses nothing against an environment that also sees the
learner's earlier random predictions, but not that of the current round (Shalev-Shwartz and
Ben-David, Section 21.2). As the environment does not see the current round's random prediction,
each round still costs `|p_t - y_t|` in expectation given the past. As `p_t` depends only on the
earlier examples, the resulting `∑_t |p_t - y_t| - min_{h ∈ H} ∑_t |h(x_t) - y_t|` is the regret
on the sequence the environment produced. So the expected regret is at most the supremum of the
regret over fixed sequences of the same length.

## References

* S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
  Cambridge University Press, 2014, Sections 21.1 and 21.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.OnlineClassification

open Finset MeasureTheory ProbabilityTheory unitInterval

variable {X : Type*}

/-- **Mistakes of a deterministic online learner.** In online binary classification over rounds
$t = 1, \dots, T$, the environment reveals an instance $x_t \in X$, the learner predicts a label
$\hat y_t \in \{0, 1\}$, and then the true label $y_t \in \{0, 1\}$ is revealed. A deterministic
online learner $A$ predicts $\hat y_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t)$ from the
earlier examples and the current instance. Its number of mistakes on the sequence
$S = ((x_1, y_1), \dots, (x_T, y_T))$ is $\sum_{t=1}^T \mathbf{1}[\hat y_t \ne y_t]$. A hypothesis
$h : X \to \{0, 1\}$ is the learner that predicts $h(x_t)$ and ignores the earlier examples.

Labels are Booleans, false standing for $0$ and true for $1$. -/
def mistakes (A : List (X × Bool) → X → Bool) (S : List (X × Bool)) : ℕ :=
  ∑ t : Fin S.length, if A (S.take t) S[t].1 = S[t].2 then 0 else 1

/-- **Expected number of mistakes of a randomized online learner.** In online binary
classification over rounds $t = 1, \dots, T$, the environment reveals an instance $x_t \in X$, the
learner outputs a prediction, and then the label $y_t \in \{0, 1\}$ is revealed. A randomized
online learner $A$ outputs $p_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t) \in [0, 1]$,
computed from the earlier examples and the current instance, and then predicts $1$ with
probability $p_t$. Its expected number of mistakes on the sequence
$S = ((x_1, y_1), \dots, (x_T, y_T))$ is
$\sum_{t=1}^T \lvert p_t - y_t \rvert$, the absolute loss of the predictions $p_t$. Reading this
sum as an expectation is justified by `integral_mistakes_eq_expectedMistakes`: when the
predictions $\hat y_t$ are independent and each equals $1$ with probability $p_t$, the expected
number of rounds with $\hat y_t \ne y_t$ is this sum.

Labels are Booleans, false standing for $0$ and true for $1$. -/
noncomputable def expectedMistakes (A : List (X × Bool) → X → I) (S : List (X × Bool)) : ℝ :=
  ∑ t : Fin S.length, |(A (S.take t) S[t].1 : ℝ) - S[t].2.toNat|

/-- **Regret in online binary classification.** In online binary classification over rounds
$t = 1, \dots, T$, the environment reveals an instance $x_t \in X$, the learner outputs a
prediction, and then the label $y_t \in \{0, 1\}$ is revealed. A randomized online learner $A$
outputs $p_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t) \in [0, 1]$, computed from the
earlier examples and the current instance, and then predicts $1$ with probability $p_t$; its
expected number of mistakes on the sequence $S = ((x_1, y_1), \dots, (x_T, y_T))$ is
$\sum_{t=1}^T \lvert p_t - y_t \rvert$. The regret of $A$ against a class $H$ of hypotheses
$h : X \to \{0, 1\}$ on $S$ is

$$\sum_{t=1}^T \lvert p_t - y_t \rvert - \min_{h \in H} \sum_{t=1}^T \lvert h(x_t) - y_t \rvert,$$

where $\sum_t \lvert h(x_t) - y_t \rvert = \sum_t \mathbf{1}[h(x_t) \ne y_t]$ is the number of
mistakes of $h$ on $S$. When $H$ is nonempty the minimum is attained, as these numbers are natural
numbers; for the empty class it is replaced by $0$, a separate convention.

Labels are Booleans, false standing for $0$ and true for $1$. -/
noncomputable def regret (A : List (X × Bool) → X → I) (H : Set (X → Bool))
    (S : List (X × Bool)) : ℝ :=
  expectedMistakes A S - (sInf ((fun h => mistakes (fun _ => h) S) '' H) : ℕ)

/-! ### Mistakes of deterministic learners -/

@[simp]
theorem mistakes_nil (A : List (X × Bool) → X → Bool) : mistakes A [] = 0 := by
  simp [mistakes]

/- After the first round, a learner goes on as the learner that is given the first example
before the others. -/
theorem mistakes_cons (A : List (X × Bool) → X → Bool) (e : X × Bool) (S : List (X × Bool)) :
    mistakes A (e :: S) =
      (if A [] e.1 = e.2 then 0 else 1) + mistakes (fun s => A (e :: s)) S := by
  unfold mistakes
  exact Fin.sum_univ_succ (fun t : Fin (S.length + 1) =>
    if A ((e :: S).take t) (e :: S)[t].1 = (e :: S)[t].2 then 0 else 1)

/- The mistakes of a hypothesis, the learner that ignores the earlier examples, are its
empirical miscount on the sequence. -/
theorem mistakes_const (h : X → Bool) (S : List (X × Bool)) :
    mistakes (fun _ => h) S = PACLearning.empiricalMiscount h (fun t : Fin S.length => S[t]) := by
  simp [mistakes, PACLearning.empiricalMiscount, Finset.card_filter, ite_not]

theorem mistakes_const_eq_zero_iff (h : X → Bool) (S : List (X × Bool)) :
    mistakes (fun _ => h) S = 0 ↔ ∀ e ∈ S, h e.1 = e.2 := by
  simp only [mistakes, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    ite_eq_left_iff, one_ne_zero, imp_false, not_not, List.forall_mem_iff_getElem]
  exact ⟨fun hS i hi => hS ⟨i, hi⟩, fun hS t => hS t t.isLt⟩

/- The halving algorithm, started from the examples `seen`, is the learner that predicts the
majority vote of the version space after `seen` and the earlier examples. -/
theorem halvingMistakes_eq_mistakes_append (C : Finset (X → Bool)) (seen S : List (X × Bool)) :
    Halving.halvingMistakes C seen S =
      mistakes (fun s => Halving.halvingPredict C (seen ++ s)) S := by
  induction S generalizing seen with
  | nil => simp [Halving.halvingMistakes]
  | cons e S ih =>
    obtain ⟨x, b⟩ := e
    rw [Halving.halvingMistakes, mistakes_cons, ih, List.append_nil]
    simp only [List.append_assoc, List.singleton_append]

/- The mistakes of the halving algorithm are those of the learner `halvingPredict C`. -/
theorem halvingMistakes_eq_mistakes (C : Finset (X → Bool)) (S : List (X × Bool)) :
    Halving.halvingMistakes C [] S = mistakes (Halving.halvingPredict C) S := by
  simp [halvingMistakes_eq_mistakes_append]

/-! ### Expected mistakes of randomized learners -/

@[simp]
theorem expectedMistakes_nil (A : List (X × Bool) → X → I) : expectedMistakes A [] = 0 := by
  simp [expectedMistakes]

/- A prediction drawn from the Bernoulli distribution of parameter `p` errs on the label `y`
with probability `|p - y|`. -/
theorem integral_bernoulliMeasure_ne (p : I) (y : Bool) :
    ∫ b, (if b = y then 0 else 1 : ℝ) ∂Ber(true, false, p) = |(p : ℝ) - y.toNat| := by
  rw [integral_bernoulliMeasure]
  cases y
  · simp [abs_of_nonneg p.2.1]
  · simp [abs_of_nonpos (sub_nonpos.2 p.2.2)]

/-- **Expected mistakes of independent Bernoulli predictions.** Let $A$ be a randomized online
learner, which in round $t$ outputs
$p_t = A((x_1, y_1), \dots, (x_{t-1}, y_{t-1}); x_t) \in [0, 1]$ from the earlier examples and the
current instance, and let $S = ((x_1, y_1), \dots, (x_T, y_T))$ be a sequence with labels
$y_t \in \{0, 1\}$, fixed in advance. If the predictions
$\hat y_1, \dots, \hat y_T$ are independent and each $\hat y_t$ equals $1$ with probability $p_t$
and $0$ otherwise, then the expected number of mistakes is

$$\mathbb{E}\Big[\sum_{t=1}^T \mathbf{1}[\hat y_t \ne y_t]\Big]
= \sum_{t=1}^T \lvert p_t - y_t \rvert.$$

Labels and predictions are Booleans, false standing for $0$ and true for $1$, and the predictions
have the product of the Bernoulli distributions of parameters $p_1, \dots, p_T$ as their law. -/
theorem integral_mistakes_eq_expectedMistakes (A : List (X × Bool) → X → I)
    (S : List (X × Bool)) :
    ∫ ŷ, (∑ t : Fin S.length, if ŷ t = S[t].2 then (0 : ℝ) else 1)
        ∂Measure.pi (fun t : Fin S.length => Ber(true, false, A (S.take t) S[t].1)) =
      expectedMistakes A S := by
  rw [integral_finsetSum _ fun t _ => Integrable.of_finite]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact (integral_comp_eval (μ := fun t : Fin S.length => Ber(true, false, A (S.take t) S[t].1))
    (i := t) (f := fun b : Bool => if b = S[t].2 then (0 : ℝ) else 1)
    (measurable_of_finite _).aestronglyMeasurable).trans (integral_bernoulliMeasure_ne _ _)

/- Over a round, `|p - y|` is at most the indicator of `p ≠ y`. -/
theorem abs_sub_toNat_le (p : I) (y : Bool) :
    |(p : ℝ) - y.toNat| ≤ if (p : ℝ) = y.toNat then 0 else 1 := by
  have h0 : (0 : ℝ) ≤ p := p.2.1
  have h1 : (p : ℝ) ≤ 1 := p.2.2
  split_ifs with h
  · simp [h]
  · rw [abs_le]
    cases y <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one] <;>
      constructor <;> linarith

/- Over a round, `|p - y| < 1` when `p` lies strictly between `0` and `1`. -/
theorem abs_sub_toNat_lt_one (p : I) (y : Bool) (hp : (p : ℝ) ∈ Set.Ioo 0 1) :
    |(p : ℝ) - y.toNat| < 1 := by
  obtain ⟨h0, h1⟩ := hp
  rw [abs_lt]
  cases y <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one] <;>
    constructor <;> linarith

/- The expected number of mistakes is at most the number of rounds with `p_t ≠ y_t`. -/
theorem expectedMistakes_le (A : List (X × Bool) → X → I) (S : List (X × Bool)) :
    expectedMistakes A S ≤
      ∑ t : Fin S.length, if (A (S.take t) S[t].1 : ℝ) = S[t].2.toNat then 0 else 1 :=
  Finset.sum_le_sum fun _ _ => abs_sub_toNat_le _ _

/- The expected number of mistakes is less than the number of rounds with `p_t ≠ y_t` as soon as
some `p_t` lies strictly between `0` and `1`: the latter is not the expected number of
mistakes. -/
theorem expectedMistakes_lt (A : List (X × Bool) → X → I) (S : List (X × Bool))
    (h : ∃ t : Fin S.length, (A (S.take t) S[t].1 : ℝ) ∈ Set.Ioo 0 1) :
    expectedMistakes A S <
      ∑ t : Fin S.length, if (A (S.take t) S[t].1 : ℝ) = S[t].2.toNat then 0 else 1 := by
  obtain ⟨t, ht⟩ := h
  refine Finset.sum_lt_sum (fun _ _ => abs_sub_toNat_le _ _) ⟨t, Finset.mem_univ _, ?_⟩
  have hne : (A (S.take t) S[t].1 : ℝ) ≠ S[t].2.toNat := by
    cases S[t].2
    · simpa only [Bool.toNat_false, Nat.cast_zero] using ht.1.ne'
    · simpa only [Bool.toNat_true, Nat.cast_one] using ht.2.ne
  calc _ < (1 : ℝ) := abs_sub_toNat_lt_one _ _ ht
    _ = _ := by simp only [hne, ↓reduceIte]

/- A deterministic learner, viewed as a randomized learner that predicts its label with
probability `1`, has its number of mistakes as expected number of mistakes. -/
theorem expectedMistakes_ofBool (A : List (X × Bool) → X → Bool) (S : List (X × Bool)) :
    expectedMistakes (fun s x => if A s x then 1 else 0) S = mistakes A S := by
  simp only [expectedMistakes, mistakes, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases A (S.take t) S[t].1 <;> cases S[t].2 <;> simp

/-! ### Regret -/

/- The regret is at least the difference between the expected number of mistakes and the
mistakes of any hypothesis of the class. -/
theorem sub_mistakes_le_regret (A : List (X × Bool) → X → I) {H : Set (X → Bool)}
    (S : List (X × Bool)) {h : X → Bool} (hh : h ∈ H) :
    expectedMistakes A S - mistakes (fun _ => h) S ≤ regret A H S := by
  unfold regret
  gcongr
  exact Nat.sInf_le ⟨h, hh, rfl⟩

/- For a nonempty class, the minimum in the regret is attained. -/
theorem exists_regret_eq (A : List (X × Bool) → X → I) {H : Set (X → Bool)}
    (S : List (X × Bool)) (hH : H.Nonempty) :
    ∃ h ∈ H, regret A H S = expectedMistakes A S - mistakes (fun _ => h) S := by
  obtain ⟨h, hh, he⟩ := Nat.sInf_mem (hH.image fun h => mistakes (fun _ => h) S)
  exact ⟨h, hh, by rw [regret, ← he]⟩

/- A sequence is realizable by `H`, in CSLib's sense, exactly when some hypothesis of `H` labels
each of its examples correctly. -/
theorem realizable_iff (H : Set (X → Bool)) (S : List (X × Bool)) :
    PACLearning.Realizable H (fun t : Fin S.length => S[t]) ↔ ∃ h ∈ H, ∀ e ∈ S, h e.1 = e.2 := by
  simp only [PACLearning.Realizable, List.forall_mem_iff_getElem]
  exact exists_congr fun h => and_congr_right fun _ =>
    ⟨fun hS i hi => (hS ⟨i, hi⟩).symm, fun hS t => (hS t t.isLt).symm⟩

/- On a sequence realizable by `H`, the regret is the expected number of mistakes. -/
theorem regret_of_realizable (A : List (X × Bool) → X → I) {H : Set (X → Bool)}
    {S : List (X × Bool)} (hS : PACLearning.Realizable H (fun t : Fin S.length => S[t])) :
    regret A H S = expectedMistakes A S := by
  obtain ⟨h, hh, hcons⟩ := (realizable_iff H S).1 hS
  have h0 : sInf ((fun h => mistakes (fun _ => h) S) '' H) = 0 :=
    Nat.sInf_eq_zero.2 (Or.inl ⟨h, hh, (mistakes_const_eq_zero_iff h S).2 hcons⟩)
  simp [regret, h0]

end Cslib.MachineLearning.OnlineClassification
