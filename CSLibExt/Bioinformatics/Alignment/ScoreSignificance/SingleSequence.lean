/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Motifs.PWM
public import CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray

/-!
# Maximal segment score of a single iid score sequence

Scores `X₀, X₁, …` are iid: letters are drawn independently from a law `q` on a finite alphabet
`β` and scored by `f : β → ℝ`, as in Karlin and Altschul (1990). With partial sums
`S_k = X₀ + ⋯ + X_{k-1}` (`S₀ = 0`), the maximal segment score is
`Mₙ = max_{0 ≤ i ≤ j ≤ n} (S_j - S_i)`, the best total score of a contiguous run (empty run
allowed). This file treats one sequence; ungapped alignment of two sequences, and the extreme
value law `P(M ≥ log n / θ + x) ≈ 1 - exp(-K e^{-θ x})`, are separate results.

## Main results

* Pathwise. `maxSegScore` is the largest run sum (`sum_le_maxSegScore_of_infix`,
  `exists_infix_sum_eq_maxSegScore`) and agrees with Kadane's maximum subarray
  (`maxSegScore_eq_max_zero`). The Lindley walk `W_{k+1} = max 0 (W_k + X_k)` satisfies
  `lindley_eq_walkMax_reverse` (`Wₙ` is the walk maximum of the reversed scores),
  `maxSegScore_concat` (`M_{n+1} = max Mₙ W_{n+1}`) and `maxSegScore_eq_max_lindley`
  (`Mₙ = max_{k ≤ n} W_k`). `maxSegScore_eq_zero_of_nonpos`: no positive score gives `Mₙ = 0`.
* Ladder epochs. `IsFirstLadder` marks the first strict ascending ladder epoch `τ₊` and height
  `H = S_{τ₊}`. `walkMax_append_of_isFirstLadder`: the walk maximum is `H` plus the maximum of the
  walk after `τ₊`; `eq_of_isFirstLadder_take` and `exists_isFirstLadder_take`: `τ₊` is unique
  and exists when the maximum is positive.
* Renewal structure. `scoreExpect_firstLadder_regeneration`: after the first ladder epoch the
  walk is a fresh iid walk independent of `(τ₊, H)`; `scoreProb_two_ladders`: the first two
  (epoch gap, height) pairs are iid. `scoreProb_le_walkMax_eq_sum`: the defective renewal
  equation `P(max_{j ≤ n} S_j ≥ t) = ∑_{k ≤ n} E[P_{n-k}(max ≥ t - H); τ₊ = k]`, so the tail of
  the maximum is governed by the ladder-height law. `scoreProb_le_lindley`: `Wₙ` has the law of
  `max_{k ≤ n} S_k`.
* Exponential tail at the Cramér root. `existsUnique_scoreMGF_eq_one`: for `E[X] < 0` and a
  positive score there is a unique `θ > 0` with `E[e^{θX}] = 1`.
  `scoreProb_le_walkMax_le`: `P(max_{k ≤ n} S_k ≥ t) ≤ e^{-θ t}` uniformly in `n` (finite-horizon
  Cramér–Lundberg); `scoreProb_le_maxSegScore_le`: `P(Mₙ ≥ t) ≤ n e^{-θ t}`;
  `sum_scoreExpect_firstLadder_exp_le_one`: `∑_{k ≤ n} E[e^{θ H}; τ₊ = k] ≤ 1`.
* Boundary cases. `scoreProb_maxSegScore_pos_eq_zero`: if `P(X > 0) = 0` then `Mₙ = 0` almost
  surely. `tendsto_scoreProb_le_maxSegScore` and
  `tendsto_scoreProb_le_maxSegScore_of_mean_nonneg`: if `P(X > 0) > 0` (in particular if
  `E[X] ≥ 0` and `X ≢ 0`) then `P(Mₙ ≥ t) → 1` for every `t`.
  `tendsto_scoreProb_le_walkMax_of_mean_pos`: if `E[X] > 0` even the walk maximum diverges.

## Implementation notes

The probability space is the finite product: `scoreExpect q f n F` is
`∑_{w : Fin n → β} bgLik q w · F [f w₀, …, f w_{n-1}]`, with the sequence likelihood `bgLik` of
`Cslib.Bioinformatics.Motifs.PWM`. Independence of disjoint blocks is `scoreExpect_append`. The
root is `Cslib.Bioinformatics.Motifs.PWM.existsUnique_pairMGF_eq_one` applied to the score
`s a b = f a` (`scoreMGF_eq_pairMGF`). Run-sum specifications reuse `List.IsInfix` and Kadane's
`Cslib.Algorithms.Lean.TimeM.IsMaxSubarraySum`, which allows only nonempty runs.

Not covered: the case `E[X] = 0` of `tendsto_scoreProb_le_walkMax_of_mean_pos` (oscillation of a
mean-zero walk); the infinite-horizon limits `P(sup_n S_n ≥ t) ~ C e^{-θ t}`, which need the key
renewal theorem; the extreme value law of `Mₙ` and its constant `K`.

## Cost model

`walkMax`, `maxSegScore` and `lindley` are structural recursions or folds that do one addition and
at most two comparisons per score, so `O(n)` operations for `n` scores. The probability layer is
a classical sum over `|β|ⁿ` words, used for statements only.

## References

* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular
  sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
* D. V. Lindley, *The theory of queues with a single server*, Proc. Cambridge Philos. Soc. 48
  (1952), 277–289.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley (1971), Chapter XII (ladder variables and the renewal equation).
* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003) (Lindley process,
  ladder heights, Cramér–Lundberg bound).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

open Real Finset

/-! ## Pathwise layer: walk maximum, maximal segment score, Lindley process -/

/-- The **maximum of the score walk** `max_{0 ≤ k ≤ n} S_k` of a score list `x₀, …, x_{n-1}`,
where `S_k = x₀ + ⋯ + x_{k-1}` and `S₀ = 0`: the largest sum of a (possibly empty) prefix
(`sum_le_walkMax_of_prefix`, `exists_prefix_sum_eq_walkMax`). Computed by the first-step
recursion `walkMax (a :: l) = max 0 (a + walkMax l)`. -/
def walkMax : List ℝ → ℝ
  | [] => 0
  | a :: l => max 0 (a + walkMax l)

/-- The **maximal segment score** `Mₙ = max_{0 ≤ i ≤ j ≤ n} (S_j - S_i)` of a score list: the
largest sum of a (possibly empty) contiguous run (`sum_le_maxSegScore_of_infix`,
`exists_infix_sum_eq_maxSegScore`). The best run either starts at the head, and is then a prefix,
or lies in the tail. -/
def maxSegScore : List ℝ → ℝ
  | [] => 0
  | a :: l => max (maxSegScore l) (walkMax (a :: l))

/-- The **Lindley (reflected) walk** `W₀ = 0`, `W_{k+1} = max 0 (W_k + x_k)`, run over the whole
list. `lindley_eq_walkMax_reverse`: `Wₙ = max_{i ≤ n} (Sₙ - S_i)`, the walk maximum of the
reversed list. -/
def lindley (l : List ℝ) : ℝ := l.foldl (fun w a => max 0 (w + a)) 0

@[simp] theorem walkMax_nil : walkMax [] = 0 := rfl

theorem walkMax_cons (a : ℝ) (l : List ℝ) : walkMax (a :: l) = max 0 (a + walkMax l) := rfl

@[simp] theorem maxSegScore_nil : maxSegScore [] = 0 := rfl

theorem maxSegScore_cons (a : ℝ) (l : List ℝ) :
    maxSegScore (a :: l) = max (maxSegScore l) (walkMax (a :: l)) := rfl

theorem walkMax_nonneg (l : List ℝ) : 0 ≤ walkMax l := by
  cases l with
  | nil => rfl
  | cons a l => exact le_max_left _ _

/-- Every prefix sum is at most the walk maximum. -/
theorem sum_le_walkMax_of_prefix {s l : List ℝ} (h : s <+: l) : s.sum ≤ walkMax l := by
  induction l generalizing s with
  | nil => rw [List.prefix_nil.1 h]; rfl
  | cons a l ih =>
      rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, ht⟩
      · exact walkMax_nonneg _
      · rw [List.sum_cons, walkMax_cons]
        exact le_max_of_le_right (by linarith [ih ht])

/-- Some prefix attains the walk maximum. -/
theorem exists_prefix_sum_eq_walkMax (l : List ℝ) : ∃ s, s <+: l ∧ s.sum = walkMax l := by
  induction l with
  | nil => exact ⟨[], List.prefix_rfl, rfl⟩
  | cons a l ih =>
      obtain ⟨s, hs, hsum⟩ := ih
      rcases le_total 0 (a + walkMax l) with h | h
      · exact ⟨a :: s, List.prefix_cons_iff.2 (Or.inr ⟨s, rfl, hs⟩), by
          rw [List.sum_cons, hsum, walkMax_cons, max_eq_right h]⟩
      · exact ⟨[], List.nil_prefix, by rw [walkMax_cons, max_eq_left h]; rfl⟩

theorem sum_le_walkMax (l : List ℝ) : l.sum ≤ walkMax l :=
  sum_le_walkMax_of_prefix List.prefix_rfl

theorem walkMax_le_maxSegScore (l : List ℝ) : walkMax l ≤ maxSegScore l := by
  cases l with
  | nil => rfl
  | cons a l => exact le_max_right _ _

theorem maxSegScore_nonneg (l : List ℝ) : 0 ≤ maxSegScore l :=
  (walkMax_nonneg l).trans (walkMax_le_maxSegScore l)

/-- Every contiguous run sums to at most the maximal segment score. -/
theorem sum_le_maxSegScore_of_infix {s l : List ℝ} (h : s <:+: l) : s.sum ≤ maxSegScore l := by
  induction l generalizing s with
  | nil => rw [List.eq_nil_of_infix_nil h]; rfl
  | cons a l ih =>
      rw [maxSegScore_cons]
      rcases List.infix_cons_iff.1 h with h | h
      · exact le_max_of_le_right (sum_le_walkMax_of_prefix h)
      · exact le_max_of_le_left (ih h)

/-- Some contiguous run attains the maximal segment score. -/
theorem exists_infix_sum_eq_maxSegScore (l : List ℝ) :
    ∃ s, s <:+: l ∧ s.sum = maxSegScore l := by
  induction l with
  | nil => exact ⟨[], List.infix_rfl, rfl⟩
  | cons a l ih =>
      rw [maxSegScore_cons]
      rcases le_total (maxSegScore l) (walkMax (a :: l)) with h | h
      · obtain ⟨s, hs, hsum⟩ := exists_prefix_sum_eq_walkMax (a :: l)
        exact ⟨s, hs.isInfix, by rw [hsum, max_eq_right h]⟩
      · obtain ⟨s, hs, hsum⟩ := ih
        exact ⟨s, hs.trans (List.suffix_cons a l).isInfix, by rw [hsum, max_eq_left h]⟩

/-- `maxSegScore` is the largest sum of a contiguous run: it is characterized by the two
properties above. -/
theorem maxSegScore_eq_of_forall {l : List ℝ} {m : ℝ} (hle : ∀ s, s <:+: l → s.sum ≤ m)
    (hex : ∃ s, s <:+: l ∧ s.sum = m) : maxSegScore l = m := by
  obtain ⟨s, hs, rfl⟩ := hex
  obtain ⟨s', hs', hs'sum⟩ := exists_infix_sum_eq_maxSegScore l
  exact le_antisymm (hs'sum ▸ hle s' hs') (sum_le_maxSegScore_of_infix hs)

/-- **Agreement with Kadane's maximum subarray** (`Cslib.Algorithms.Lean.TimeM.IsMaxSubarraySum`,
nonempty runs): the maximal segment score, which also allows the empty run, is `max 0 m`. -/
theorem maxSegScore_eq_max_zero {l : List ℝ} {m : ℝ}
    (h : Cslib.Algorithms.Lean.TimeM.IsMaxSubarraySum l m) : maxSegScore l = max 0 m := by
  obtain ⟨⟨s, hs, -, rfl⟩, hle⟩ := h
  refine maxSegScore_eq_of_forall (fun t ht => ?_) ?_
  · by_cases ht0 : t = []
    · subst ht0; exact le_max_left _ _
    · exact le_max_of_le_right (hle t ht ht0)
  · rcases le_total 0 s.sum with h0 | h0
    · exact ⟨s, hs, (max_eq_right h0).symm⟩
    · exact ⟨[], List.nil_infix, (max_eq_left h0).symm⟩

/-- **No positive scores**: if every score is `≤ 0`, the maximal segment score is `0`. -/
theorem maxSegScore_eq_zero_of_nonpos {l : List ℝ} (h : ∀ x ∈ l, x ≤ 0) : maxSegScore l = 0 :=
  maxSegScore_eq_of_forall (fun s hs => by
      simpa using List.sum_le_length_nsmul s 0 fun x hx => h x (hs.subset hx))
    ⟨[], List.nil_infix, rfl⟩

/-- The maximal segment score is monotone along contiguous runs. -/
theorem maxSegScore_mono {s l : List ℝ} (h : s <:+: l) : maxSegScore s ≤ maxSegScore l := by
  obtain ⟨t, ht, htsum⟩ := exists_infix_sum_eq_maxSegScore s
  exact htsum ▸ sum_le_maxSegScore_of_infix (ht.trans h)

/-- Splitting the walk at the end of `u`: the walk maximum of `u ++ v` is the larger of the walk
maximum of `u` and `S_{|u|}` plus the walk maximum of `v`. -/
theorem walkMax_append (u v : List ℝ) :
    walkMax (u ++ v) = max (walkMax u) (u.sum + walkMax v) := by
  induction u with
  | nil => simp [max_eq_right (walkMax_nonneg v)]
  | cons a u ih =>
      rw [List.cons_append, walkMax_cons, ih, walkMax_cons, List.sum_cons, ← max_add_add_left,
        max_assoc, add_assoc]

theorem lindley_concat (l : List ℝ) (a : ℝ) : lindley (l ++ [a]) = max 0 (lindley l + a) := by
  simp [lindley, List.foldl_append]

/-- **Lindley duality**: the reflected walk after `n` steps, `Wₙ = max_{i ≤ n} (Sₙ - S_i)`, is the
walk maximum of the time-reversed scores. -/
theorem lindley_eq_walkMax_reverse (l : List ℝ) : lindley l = walkMax l.reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
      rw [lindley_concat, ih, List.reverse_append, List.reverse_singleton, List.singleton_append,
        walkMax_cons, add_comm]

theorem maxSegScore_reverse (l : List ℝ) : maxSegScore l.reverse = maxSegScore l := by
  refine maxSegScore_eq_of_forall (fun s hs => ?_) ?_
  · rw [← List.sum_reverse]
    have hs' : s.reverse <:+: l := by simpa using List.reverse_infix.2 hs
    exact sum_le_maxSegScore_of_infix hs'
  · obtain ⟨s, hs, hsum⟩ := exists_infix_sum_eq_maxSegScore l
    exact ⟨s.reverse, List.reverse_infix.2 hs, by rw [List.sum_reverse, hsum]⟩

/-- **The Kadane / Lindley recursion**: appending a score, the maximal segment score is the larger
of the old one and the new value of the reflected walk. So `Mₙ = max_{k ≤ n} W_k`. -/
theorem maxSegScore_concat (l : List ℝ) (a : ℝ) :
    maxSegScore (l ++ [a]) = max (maxSegScore l) (lindley (l ++ [a])) := by
  rw [← maxSegScore_reverse, lindley_eq_walkMax_reverse, List.reverse_append,
    List.reverse_singleton, List.singleton_append, maxSegScore_cons, maxSegScore_reverse]

theorem lindley_le_maxSegScore (l : List ℝ) : lindley l ≤ maxSegScore l := by
  rw [lindley_eq_walkMax_reverse, ← maxSegScore_reverse l]
  exact walkMax_le_maxSegScore _

/-- **`Mₙ` is the maximum of the reflected walk**: every `W_k`, `k ≤ n`, is at most `Mₙ`, and some
`W_k` equals it. -/
theorem maxSegScore_eq_max_lindley (l : List ℝ) :
    (∀ p, p <+: l → lindley p ≤ maxSegScore l) ∧ ∃ p, p <+: l ∧ lindley p = maxSegScore l := by
  refine ⟨fun p hp => (lindley_le_maxSegScore p).trans (maxSegScore_mono hp.isInfix), ?_⟩
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], List.prefix_rfl, rfl⟩
  | append_singleton l a ih =>
      obtain ⟨p, hp, hpeq⟩ := ih
      rw [maxSegScore_concat]
      rcases le_total (maxSegScore l) (lindley (l ++ [a])) with h | h
      · exact ⟨l ++ [a], List.prefix_rfl, (max_eq_right h).symm⟩
      · exact ⟨p, hp.trans (List.prefix_append _ _), by rw [hpeq, max_eq_left h]⟩

/-! ## Ladder epochs -/

/-- `u` ends at the **first strict ascending ladder epoch** of the walk: `S_{|u|} = u.sum > 0`
while `S_j ≤ 0` for every `j < |u|`. The ladder epoch is `τ₊ = |u|` and the ladder height is
`H = u.sum`. -/
def IsFirstLadder (u : List ℝ) : Prop := 0 < u.sum ∧ ∀ j < u.length, (u.take j).sum ≤ 0

/-- Up to its first ladder epoch the walk maximum is the ladder height. -/
theorem walkMax_of_isFirstLadder {u : List ℝ} (h : IsFirstLadder u) : walkMax u = u.sum := by
  obtain ⟨s, hs, hsum⟩ := exists_prefix_sum_eq_walkMax u
  refine le_antisymm ?_ (sum_le_walkMax u)
  rw [← hsum]
  rcases (hs.length_le).lt_or_eq with hlt | heq
  · rw [List.prefix_iff_eq_take.1 hs]
    exact (h.2 _ hlt).trans h.1.le
  · rw [hs.eq_of_length heq]

/-- **Ladder decomposition of the walk maximum**: after the first ladder epoch the maximum is the
ladder height plus the maximum of the remaining walk. Iterating, the walk maximum is the sum of
the ladder heights. -/
theorem walkMax_append_of_isFirstLadder {u : List ℝ} (h : IsFirstLadder u) (v : List ℝ) :
    walkMax (u ++ v) = u.sum + walkMax v := by
  rw [walkMax_append, walkMax_of_isFirstLadder h,
    max_eq_right (le_add_of_nonneg_right (walkMax_nonneg v))]

/-- Without a ladder epoch the walk never goes above `0`. -/
theorem walkMax_eq_zero_of_forall {l : List ℝ} (h : ∀ j ≤ l.length, (l.take j).sum ≤ 0) :
    walkMax l = 0 := by
  obtain ⟨s, hs, hsum⟩ := exists_prefix_sum_eq_walkMax l
  refine le_antisymm ?_ (walkMax_nonneg l)
  rw [← hsum, List.prefix_iff_eq_take.1 hs]
  exact h _ hs.length_le

/-- The first ladder epoch is unique. -/
theorem eq_of_isFirstLadder_take {l : List ℝ} {j k : ℕ} (hj : IsFirstLadder (l.take j))
    (hk : IsFirstLadder (l.take k)) (hjl : j ≤ l.length) (hkl : k ≤ l.length) : j = k := by
  have key : ∀ {a b : ℕ}, IsFirstLadder (l.take a) → IsFirstLadder (l.take b) → b ≤ l.length →
      ¬ a < b := fun {a b} ha hb hbl hab => by
    have := hb.2 a (by rw [List.length_take]; omega)
    rw [List.take_take, min_eq_left hab.le] at this
    exact absurd ha.1 (not_lt.2 this)
  rcases lt_trichotomy j k with h | h | h
  · exact absurd h (key hj hk hkl)
  · exact h
  · exact absurd h (key hk hj hjl)

/-- A positive walk maximum has a first ladder epoch. -/
theorem exists_isFirstLadder_take {l : List ℝ} (h : 0 < walkMax l) :
    ∃ k ≤ l.length, IsFirstLadder (l.take k) := by
  classical
  have hex : ∃ j, j ≤ l.length ∧ 0 < (l.take j).sum := by
    by_contra hne
    push Not at hne
    exact absurd (walkMax_eq_zero_of_forall hne) h.ne'
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
  have hjk : j < Nat.find hex := by
    rw [List.length_take] at hj; exact lt_of_lt_of_le hj (min_le_left _ _)
  rw [List.take_take, min_eq_left hjk.le]
  have := Nat.find_min hex hjk
  push Not at this
  exact this (hjk.le.trans (Nat.find_spec hex).1)

/-! ## The iid score sequence -/

open Cslib.Bioinformatics.Motifs.PWM Cslib.MachineLearning.LatentVariable.ExpectationMaximization

variable {β : Type*} [Fintype β]

/-- **Expectation over an iid score sequence of length `n`.** Letters `w₀, …, w_{n-1}` are drawn
independently from the law `q` on the finite alphabet `β` (sequence likelihood `bgLik q w`, from
`Cslib.Bioinformatics.Motifs.PWM`) and scored by `f`; `scoreExpect q f n F` is the expectation of
the functional `F` of the score list `[f w₀, …, f w_{n-1}]`. -/
noncomputable def scoreExpect (q f : β → ℝ) (n : ℕ) (F : List ℝ → ℝ) : ℝ :=
  ∑ w : Fin n → β, bgLik q w * F (List.ofFn fun i => f (w i))

open Classical in
/-- The probability that the score list of an iid sequence of length `n` satisfies `P`. -/
noncomputable def scoreProb (q f : β → ℝ) (n : ℕ) (P : List ℝ → Prop) : ℝ :=
  scoreExpect q f n fun l => if P l then 1 else 0

/-- The **moment generating function** `E[e^{θX}] = ∑_b q_b e^{θ f(b)}` of one score. -/
noncomputable def scoreMGF (q f : β → ℝ) (θ : ℝ) : ℝ := ∑ b, q b * exp (θ * f b)

section Expect

variable (q f : β → ℝ)

theorem scoreExpect_zero (F : List ℝ → ℝ) : scoreExpect q f 0 F = F [] := by
  simp [scoreExpect, bgLik]

/-- First-step decomposition: condition on the first letter. -/
theorem scoreExpect_succ (n : ℕ) (F : List ℝ → ℝ) :
    scoreExpect q f (n + 1) F = ∑ a, q a * scoreExpect q f n fun l => F (f a :: l) := by
  unfold scoreExpect
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => β).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  simp [Fin.consEquiv, bgLik, Fin.prod_univ_succ, List.ofFn_succ, mul_assoc]

theorem scoreExpect_congr {n : ℕ} {F G : List ℝ → ℝ} (h : ∀ l, l.length = n → F l = G l) :
    scoreExpect q f n F = scoreExpect q f n G :=
  sum_congr rfl fun _ _ => by rw [h _ (List.length_ofFn)]

theorem scoreExpect_add (n : ℕ) (F G : List ℝ → ℝ) :
    scoreExpect q f n (fun l => F l + G l) = scoreExpect q f n F + scoreExpect q f n G := by
  simp only [scoreExpect, mul_add, sum_add_distrib]

theorem scoreExpect_const_mul (n : ℕ) (c : ℝ) (F : List ℝ → ℝ) :
    scoreExpect q f n (fun l => c * F l) = c * scoreExpect q f n F := by
  simp only [scoreExpect, mul_sum]
  exact sum_congr rfl fun w _ => by ring

theorem scoreExpect_mul_const (n : ℕ) (c : ℝ) (F : List ℝ → ℝ) :
    scoreExpect q f n (fun l => F l * c) = scoreExpect q f n F * c := by
  simp only [scoreExpect, sum_mul]
  exact sum_congr rfl fun w _ => by ring

theorem scoreExpect_sum {ι : Type*} (s : Finset ι) (n : ℕ) (F : ι → List ℝ → ℝ) :
    scoreExpect q f n (fun l => ∑ i ∈ s, F i l) = ∑ i ∈ s, scoreExpect q f n (F i) := by
  simp only [scoreExpect, mul_sum]
  exact sum_comm

variable {q} in
theorem scoreExpect_mono (hq : ∀ b, 0 ≤ q b) {n : ℕ} {F G : List ℝ → ℝ}
    (h : ∀ l, l.length = n → F l ≤ G l) : scoreExpect q f n F ≤ scoreExpect q f n G :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (h _ List.length_ofFn)
    (prod_nonneg fun _ _ => hq _)

variable {q} in
theorem scoreExpect_const (hq : IsDist q) (n : ℕ) (c : ℝ) :
    scoreExpect q f n (fun _ => c) = c := by
  induction n with
  | zero => exact scoreExpect_zero q f _
  | succ n ih => rw [scoreExpect_succ]; simp only [ih, ← sum_mul, hq.2, one_mul]

/-- **Independence of disjoint blocks** (Fubini for iid words): a word of length `k + m` is a word
of length `k` followed by an independent word of length `m`. -/
theorem scoreExpect_append (k m : ℕ) (F : List ℝ → ℝ) :
    scoreExpect q f (k + m) F =
      scoreExpect q f k fun u => scoreExpect q f m fun v => F (u ++ v) := by
  induction k generalizing F with
  | zero => rw [Nat.zero_add, scoreExpect_zero]; rfl
  | succ k ih =>
      rw [Nat.add_right_comm, scoreExpect_succ, scoreExpect_succ]
      exact sum_congr rfl fun a _ => by rw [ih]; rfl

/-- Splitting a word at position `k`: the first `k` scores and the rest are independent. -/
theorem scoreExpect_take_drop {k n : ℕ} (hk : k ≤ n) (Φ : List ℝ → List ℝ → ℝ) :
    scoreExpect q f n (fun l => Φ (l.take k) (l.drop k)) =
      scoreExpect q f k fun u => scoreExpect q f (n - k) fun v => Φ u v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [scoreExpect_append, Nat.add_sub_cancel_left]
  refine scoreExpect_congr q f fun u hu => scoreExpect_congr q f fun v _ => ?_
  rw [List.take_left' hu, List.drop_left' hu]

end Expect

section Prob

variable {q : β → ℝ} (f : β → ℝ)

theorem scoreProb_succ (n : ℕ) (P : List ℝ → Prop) :
    scoreProb q f (n + 1) P = ∑ a, q a * scoreProb q f n fun l => P (f a :: l) :=
  scoreExpect_succ q f n _

theorem scoreProb_congr {n : ℕ} {P Q : List ℝ → Prop} (h : ∀ l, l.length = n → (P l ↔ Q l)) :
    scoreProb q f n P = scoreProb q f n Q :=
  scoreExpect_congr q f fun l hl => by classical exact if_congr (h l hl) rfl rfl

theorem scoreProb_mono (hq : ∀ b, 0 ≤ q b) {n : ℕ} {P Q : List ℝ → Prop}
    (h : ∀ l, l.length = n → P l → Q l) : scoreProb q f n P ≤ scoreProb q f n Q :=
  scoreExpect_mono f hq fun l hl => by
    by_cases hP : P l
    · simp only [hP, h l hl hP, ↓reduceIte, le_refl]
    · simp only [hP, ↓reduceIte]; split_ifs <;> norm_num

theorem scoreProb_nonneg (hq : ∀ b, 0 ≤ q b) (n : ℕ) (P : List ℝ → Prop) :
    0 ≤ scoreProb q f n P := by
  exact sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => hq _)
    (by dsimp only; split_ifs <;> norm_num)

theorem scoreProb_add_not (hq : IsDist q) (n : ℕ) (P : List ℝ → Prop) :
    scoreProb q f n P + scoreProb q f n (fun l => ¬ P l) = 1 := by
  unfold scoreProb
  rw [← scoreExpect_add]
  conv_rhs => rw [← scoreExpect_const f hq n 1]
  exact scoreExpect_congr q f fun l _ => by by_cases h : P l <;> simp [h]

theorem scoreProb_le_one (hq : IsDist q) (n : ℕ) (P : List ℝ → Prop) :
    scoreProb q f n P ≤ 1 := by
  linarith [scoreProb_add_not f hq n P, scoreProb_nonneg f hq.1 n (fun l => ¬ P l)]

theorem scoreProb_or_le (hq : ∀ b, 0 ≤ q b) (n : ℕ) (P Q : List ℝ → Prop) :
    scoreProb q f n (fun l => P l ∨ Q l) ≤ scoreProb q f n P + scoreProb q f n Q := by
  unfold scoreProb
  rw [← scoreExpect_add]
  exact scoreExpect_mono f hq fun l _ => by
    by_cases hP : P l <;> by_cases hQ : Q l <;> simp [hP, hQ]

end Prob

/-! ## The Cramér root `θ` and the exponential tail -/

section Root

variable {q : β → ℝ} (f : β → ℝ)

/-- The single-score MGF is the Karlin–Altschul pair MGF (`Cslib.Bioinformatics.Motifs.PWM.pairMGF`)
of the score `s a b = f a`, which ignores the second letter. -/
theorem scoreMGF_eq_pairMGF (hq : IsDist q) (θ : ℝ) :
    scoreMGF q f θ = pairMGF q (fun a _ => f a) θ := by
  simp only [scoreMGF, pairMGF]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_mul, ← mul_sum, hq.2, mul_one]

/-- **The Cramér (Karlin–Altschul) root** (Karlin and Altschul 1990): if the expected score is
negative and some score is positive, there is a unique `θ > 0` with `E[e^{θX}] = 1`. This is
`Cslib.Bioinformatics.Motifs.PWM.existsUnique_pairMGF_eq_one` applied to `s a b = f a`. -/
theorem existsUnique_scoreMGF_eq_one (hq : IsDist q) (hq0 : ∀ b, 0 < q b)
    (hneg : ∑ b, q b * f b < 0) (hpos : ∃ b, 0 < f b) :
    ∃! θ, 0 < θ ∧ scoreMGF q f θ = 1 := by
  have hneg' : ∑ a, ∑ b, q a * q b * (fun a (_ : β) => f a) a b < 0 := by
    have : ∀ a, ∑ b, q a * q b * f a = q a * f a := fun a => by
      rw [← sum_mul, ← mul_sum, hq.2, mul_one]
    simpa only [this] using hneg
  obtain ⟨b, hb⟩ := hpos
  simpa only [scoreMGF_eq_pairMGF f hq] using
    existsUnique_pairMGF_eq_one hq hq0 hneg' ⟨b, b, hb⟩

/-- **The exponential martingale**: `E[e^{θ Sₙ}] = E[e^{θX}]ⁿ`; at the Cramér root it is `1`. -/
theorem scoreExpect_exp_sum (θ : ℝ) (n : ℕ) :
    scoreExpect q f n (fun l => exp (θ * l.sum)) = scoreMGF q f θ ^ n := by
  induction n with
  | zero => simp [scoreExpect_zero]
  | succ n ih =>
      rw [scoreExpect_succ, pow_succ', scoreMGF, sum_mul]
      refine sum_congr rfl fun a _ => ?_
      simp only [List.sum_cons, mul_add, exp_add]
      rw [scoreExpect_const_mul, ih, mul_assoc]
      rfl

/-- **Finite-horizon Cramér–Lundberg bound**: at a Cramér root `θ ≥ 0` the walk maximum satisfies
`P(max_{k ≤ n} S_k ≥ t) ≤ e^{-θ t}` for every `t` and every horizon `n`. -/
theorem scoreProb_le_walkMax_le (hq : IsDist q) {θ : ℝ} (hθ : 0 ≤ θ)
    (hroot : scoreMGF q f θ = 1) (n : ℕ) (t : ℝ) :
    scoreProb q f n (fun l => t ≤ walkMax l) ≤ exp (-θ * t) := by
  induction n generalizing t with
  | zero =>
      rw [scoreProb, scoreExpect_zero, walkMax_nil]
      split_ifs with ht
      · exact one_le_exp (by nlinarith)
      · exact (exp_pos _).le
  | succ n ih =>
      by_cases ht : t ≤ 0
      · exact (scoreProb_le_one f hq _ _).trans (one_le_exp (by nlinarith))
      push Not at ht
      rw [scoreProb_succ]
      calc ∑ a, q a * scoreProb q f n (fun l => t ≤ walkMax (f a :: l))
          = ∑ a, q a * scoreProb q f n (fun l => t - f a ≤ walkMax l) := by
            refine sum_congr rfl fun a _ => ?_
            rw [scoreProb_congr f fun l _ => ?_]
            rw [walkMax_cons, le_max_iff]
            constructor
            · rintro (h | h) <;> [exact absurd h (not_le.2 ht); linarith]
            · intro h; right; linarith
        _ ≤ ∑ a, q a * exp (-θ * (t - f a)) :=
            sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih _) (hq.1 a)
        _ = exp (-θ * t) * scoreMGF q f θ := by
            rw [scoreMGF, mul_sum]
            refine sum_congr rfl fun a _ => ?_
            rw [← mul_assoc, mul_comm (exp _) (q a), mul_assoc, ← exp_add]
            ring_nf
        _ = exp (-θ * t) := by rw [hroot, mul_one]

/-- **Karlin–Altschul-type tail of the maximal segment score**: at a Cramér root `θ ≥ 0`,
`P(Mₙ ≥ t) ≤ n e^{-θ t}` for `t > 0` (a union bound over the start of the best segment). -/
theorem scoreProb_le_maxSegScore_le (hq : IsDist q) {θ : ℝ} (hθ : 0 ≤ θ)
    (hroot : scoreMGF q f θ = 1) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    scoreProb q f n (fun l => t ≤ maxSegScore l) ≤ n * exp (-θ * t) := by
  induction n with
  | zero =>
      rw [scoreProb, scoreExpect_zero, maxSegScore_nil]
      simp [not_le.2 ht]
  | succ n ih =>
      rw [scoreProb_succ]
      calc ∑ a, q a * scoreProb q f n (fun l => t ≤ maxSegScore (f a :: l))
          ≤ ∑ a, q a * (scoreProb q f n (fun l => t ≤ maxSegScore l) +
              scoreProb q f n (fun l => t ≤ walkMax (f a :: l))) := by
            refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hq.1 a)
            rw [scoreProb_congr f fun l _ => by rw [maxSegScore_cons, le_max_iff]]
            exact scoreProb_or_le f hq.1 n _ _
        _ = scoreProb q f n (fun l => t ≤ maxSegScore l) +
              scoreProb q f (n + 1) (fun l => t ≤ walkMax l) := by
            simp only [mul_add, sum_add_distrib, ← sum_mul, hq.2, one_mul, scoreProb_succ]
        _ ≤ n * exp (-θ * t) + exp (-θ * t) :=
            add_le_add ih (scoreProb_le_walkMax_le f hq hθ hroot _ _)
        _ = (n + 1 : ℕ) * exp (-θ * t) := by push_cast; ring

end Root

/-! ## Lindley process, ladder renewal structure -/

section Ladder

variable {q : β → ℝ} (f : β → ℝ)

/-- **Exchangeability**: reversing an iid score sequence does not change its law. -/
theorem scoreExpect_reverse (n : ℕ) (F : List ℝ → ℝ) :
    scoreExpect q f n (fun l => F l.reverse) = scoreExpect q f n F := by
  unfold scoreExpect
  refine Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl β)) _ _ fun w => ?_
  have hrev : (List.ofFn fun i => f (w i)).reverse =
      List.ofFn fun i => f ((Equiv.arrowCongr Fin.revPerm (Equiv.refl β)) w i) := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Equiv.arrowCongr_apply,
      Equiv.coe_refl, Function.comp_apply, id]
    simp at h1
    congr 2
    ext
    simp [Fin.rev]
    omega
  beta_reduce
  rw [hrev]
  congr 1
  exact (Fintype.prod_equiv Fin.revPerm _ _ fun i => by simp).symm

theorem scoreProb_reverse (n : ℕ) (P : List ℝ → Prop) :
    scoreProb q f n (fun l => P l.reverse) = scoreProb q f n P := by
  unfold scoreProb
  exact scoreExpect_reverse f n fun l => @ite ℝ (P l) (Classical.propDecidable _) 1 0

/-- **The Lindley process has the law of the walk maximum**: `P(Wₙ ≥ t) = P(max_{k ≤ n} S_k ≥ t)`,
so at a Cramér root `θ ≥ 0` the reflected walk is tight, `P(Wₙ ≥ t) ≤ e^{-θ t}` uniformly in
`n` (`scoreProb_le_walkMax_le`). -/
theorem scoreProb_le_lindley (n : ℕ) (t : ℝ) :
    scoreProb q f n (fun l => t ≤ lindley l) = scoreProb q f n (fun l => t ≤ walkMax l) := by
  rw [← scoreProb_reverse f n (fun l => t ≤ walkMax l)]
  exact scoreProb_congr f fun l _ => by rw [lindley_eq_walkMax_reverse]

/-- **Regeneration at a fixed time**: the first `k` scores and the remaining `n - k` are
independent. -/
theorem scoreExpect_take_mul_drop {k n : ℕ} (hk : k ≤ n) (F G : List ℝ → ℝ) :
    scoreExpect q f n (fun l => F (l.take k) * G (l.drop k)) =
      scoreExpect q f k F * scoreExpect q f (n - k) G := by
  rw [scoreExpect_take_drop q f hk fun u v => F u * G v, ← scoreExpect_mul_const]
  exact scoreExpect_congr q f fun u _ => scoreExpect_const_mul q f _ _ _

open Classical in
/-- **The ladder epochs form a renewal process** (regeneration at the first ladder epoch): on
`{τ₊ = k}` the walk after `τ₊` is a fresh iid walk, independent of the ladder segment up to `τ₊`
(hence of the ladder height). For any functionals `H` of the segment and `G` of the remainder,
`E[H; τ₊ = k] · E[G]` factorizes. Iterating (`scoreProb_two_ladders`) the successive
(ladder epoch gap, ladder height) pairs are iid. -/
theorem scoreExpect_firstLadder_regeneration {k n : ℕ} (hk : k ≤ n) (H G : List ℝ → ℝ) :
    scoreExpect q f n (fun l =>
        (if IsFirstLadder (l.take k) then H (l.take k) else 0) * G (l.drop k)) =
      scoreExpect q f k (fun u => if IsFirstLadder u then H u else 0) *
        scoreExpect q f (n - k) G :=
  scoreExpect_take_mul_drop f hk (fun u => if IsFirstLadder u then H u else 0) G

/-- **Independent blocks**: an event about the first `k` scores and an event about the rest have
independent probabilities. -/
theorem scoreProb_take_and_drop {k n : ℕ} (hk : k ≤ n) (A B : List ℝ → Prop) :
    scoreProb q f n (fun l => A (l.take k) ∧ B (l.drop k)) =
      scoreProb q f k A * scoreProb q f (n - k) B := by
  unfold scoreProb
  rw [← scoreExpect_take_mul_drop f hk]
  exact scoreExpect_congr q f fun l _ => by
    by_cases ha : A (l.take k) <;> by_cases hb : B (l.drop k) <;> simp [ha, hb]

/-- **The first two ladder segments are iid**: the probability that the first ladder segment has
length `k` and property `A` and the next one has length `k'` and property `B` is the product of
the two single-segment probabilities (the ladder-height law at the two epochs). -/
theorem scoreProb_two_ladders (hq : IsDist q) {k k' n : ℕ} (h : k + k' ≤ n)
    (A B : List ℝ → Prop) :
    scoreProb q f n (fun l => (IsFirstLadder (l.take k) ∧ A (l.take k)) ∧
        (IsFirstLadder ((l.drop k).take k') ∧ B ((l.drop k).take k'))) =
      scoreProb q f k (fun u => IsFirstLadder u ∧ A u) *
        scoreProb q f k' (fun u => IsFirstLadder u ∧ B u) := by
  rw [scoreProb_take_and_drop f (show k ≤ n by omega) (fun u => IsFirstLadder u ∧ A u)
    (fun v => IsFirstLadder (v.take k') ∧ B (v.take k'))]
  congr 1
  have h2 := scoreProb_take_and_drop f (q := q) (show k' ≤ n - k by omega)
    (fun u => IsFirstLadder u ∧ B u) (fun _ => True)
  have h1 : scoreProb q f (n - k - k') (fun _ => True) = 1 := by
    unfold scoreProb; simpa using scoreExpect_const f hq (n - k - k') 1
  rw [h1, mul_one] at h2
  rw [← h2]
  exact scoreProb_congr f fun l _ => by simp

/-- **First-ladder decomposition of the event `{walk maximum ≥ t}`**, `t > 0`: it happens exactly
when there is a (necessarily unique, `eq_of_isFirstLadder_take`) first ladder epoch `k` after
which the remaining walk climbs a further `t - H`. -/
theorem le_walkMax_iff {l : List ℝ} {t : ℝ} (ht : 0 < t) :
    t ≤ walkMax l ↔ ∃ k ≤ l.length,
      IsFirstLadder (l.take k) ∧ t - (l.take k).sum ≤ walkMax (l.drop k) := by
  constructor
  · intro h
    obtain ⟨k, hk, hfl⟩ := exists_isFirstLadder_take (ht.trans_le h)
    refine ⟨k, hk, hfl, ?_⟩
    have := walkMax_append_of_isFirstLadder hfl (l.drop k)
    rw [List.take_append_drop] at this
    linarith
  · rintro ⟨k, -, hfl, hle⟩
    have := walkMax_append_of_isFirstLadder hfl (l.drop k)
    rw [List.take_append_drop] at this
    linarith

open Classical in
/-- **The defective renewal equation for the walk maximum** (finite horizon): for `t > 0`,
`P(max_{j ≤ n} S_j ≥ t) = ∑_{k ≤ n} E[P_{n-k}(max ≥ t - H); τ₊ = k]`, where `H` is the ladder
height. The tail of the maximum is determined by the ladder-height distribution
`P(τ₊ = k, H ∈ ·) = scoreProb q f k (fun u => IsFirstLadder u ∧ u.sum ∈ ·)`. -/
theorem scoreProb_le_walkMax_eq_sum {t : ℝ} (ht : 0 < t) (n : ℕ) :
    scoreProb q f n (fun l => t ≤ walkMax l) = ∑ k ∈ range (n + 1),
      scoreExpect q f k (fun u =>
        if IsFirstLadder u then scoreProb q f (n - k) (fun v => t - u.sum ≤ walkMax v) else 0) := by
  have hpath : ∀ l : List ℝ, l.length = n →
      (if t ≤ walkMax l then (1 : ℝ) else 0) = ∑ k ∈ range (n + 1),
        (fun u v => if IsFirstLadder u ∧ t - u.sum ≤ walkMax v then (1 : ℝ) else 0)
          (l.take k) (l.drop k) := by
    intro l hl
    by_cases hW : t ≤ walkMax l
    · obtain ⟨k₀, hk₀, hfl₀, hle₀⟩ := (le_walkMax_iff ht).1 hW
      rw [sum_eq_single k₀]
      · simp [hW, hfl₀, hle₀]
      · intro k hk hne
        have hfl : ¬ IsFirstLadder (l.take k) := fun hfl =>
          hne (eq_of_isFirstLadder_take hfl hfl₀ (by rw [hl]; simpa [Nat.lt_succ_iff] using hk)
            hk₀)
        simp [hfl]
      · intro h; exact absurd (by rw [mem_range, ← hl]; omega) h
    · rw [sum_eq_zero fun k hk => ?_]
      · simp [hW]
      · have : ¬ (IsFirstLadder (l.take k) ∧ t - (l.take k).sum ≤ walkMax (l.drop k)) :=
          fun h => hW ((le_walkMax_iff ht).2 ⟨k, by rw [hl]; simpa [Nat.lt_succ_iff] using hk, h⟩)
        simp only [this, ↓reduceIte]
  unfold scoreProb
  rw [scoreExpect_congr q f (G := fun l => ∑ k ∈ range (n + 1),
      (fun u v => if IsFirstLadder u ∧ t - u.sum ≤ walkMax v then (1 : ℝ) else 0)
        (l.take k) (l.drop k)) fun l hl => by rw [← hpath l hl], scoreExpect_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [scoreExpect_take_drop q f (by simpa [Nat.lt_succ_iff] using hk)
    (fun u v => if IsFirstLadder u ∧ t - u.sum ≤ walkMax v then (1 : ℝ) else 0)]
  refine scoreExpect_congr q f fun u _ => ?_
  by_cases hu : IsFirstLadder u
  · simp only [hu, true_and, ↓reduceIte]
  · simp [hu, scoreExpect]

open Classical in
/-- **The tilted ladder-height law is defective**: at a Cramér root `θ`,
`∑_{k ≤ n} E[e^{θ H}; τ₊ = k] ≤ 1` (optional stopping of `e^{θ S}` at the first ladder epoch; as
`n → ∞` this is the Wiener–Hopf identity `E[e^{θ H}; τ₊ < ∞] ≤ 1`). -/
theorem sum_scoreExpect_firstLadder_exp_le_one (hq : ∀ b, 0 ≤ q b) {θ : ℝ}
    (hroot : scoreMGF q f θ = 1) (n : ℕ) :
    ∑ k ∈ range (n + 1),
      scoreExpect q f k (fun u => if IsFirstLadder u then exp (θ * u.sum) else 0) ≤ 1 := by
  have hterm : ∀ k ∈ range (n + 1),
      scoreExpect q f k (fun u => if IsFirstLadder u then exp (θ * u.sum) else 0) =
        scoreExpect q f n (fun l =>
          (if IsFirstLadder (l.take k) then exp (θ * (l.take k).sum) else 0) *
            exp (θ * (l.drop k).sum)) := fun k hk => by
    rw [scoreExpect_take_mul_drop f (by simpa [Nat.lt_succ_iff] using hk)
      (fun u => if IsFirstLadder u then exp (θ * u.sum) else 0) (fun v => exp (θ * v.sum)),
      scoreExpect_exp_sum, hroot, one_pow, mul_one]
  have h1 : scoreExpect q f n (fun l => exp (θ * l.sum)) = 1 := by
    rw [scoreExpect_exp_sum, hroot, one_pow]
  rw [sum_congr rfl hterm, ← scoreExpect_sum]
  refine (scoreExpect_mono f hq fun l hl => ?_).trans h1.le
  by_cases hex : ∃ k ∈ range (n + 1), IsFirstLadder (l.take k)
  · obtain ⟨k₀, hk₀, hfl₀⟩ := hex
    have hk₀' : k₀ ≤ l.length := by rw [hl]; simpa [Nat.lt_succ_iff] using hk₀
    rw [sum_eq_single k₀]
    · simp only [hfl₀, ↓reduceIte]
      rw [← exp_add, ← mul_add, List.sum_take_add_sum_drop]
    · intro k hk hne
      have hfl : ¬ IsFirstLadder (l.take k) := fun hfl =>
        hne (eq_of_isFirstLadder_take hfl hfl₀ (by rw [hl]; simpa [Nat.lt_succ_iff] using hk)
          hk₀')
      simp [hfl]
    · intro h; exact absurd hk₀ h
  · push Not at hex
    rw [sum_eq_zero fun k hk => by simp [hex k hk]]
    exact (exp_pos _).le

end Ladder

/-! ## Boundary cases -/

section Boundary

variable {q : β → ℝ} (f : β → ℝ)

/-- **No positive scores** (`P(X > 0) = 0`): the maximal segment score is `0` almost surely. -/
theorem scoreProb_maxSegScore_pos_eq_zero (hq : ∀ b, 0 ≤ q b) (hf : ∀ b, 0 < q b → f b ≤ 0)
    (n : ℕ) : scoreProb q f n (fun l => 0 < maxSegScore l) = 0 := by
  refine sum_eq_zero fun w _ => ?_
  by_cases hw : ∀ i, 0 < q (w i)
  · have h0 : maxSegScore (List.ofFn fun i => f (w i)) = 0 := maxSegScore_eq_zero_of_nonpos
      fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact hf _ (hw i)
    simp [h0]
  · push Not at hw
    obtain ⟨i, hi⟩ := hw
    have : bgLik q w = 0 := prod_eq_zero (mem_univ i) (le_antisymm hi (hq _))
    simp [this]

/-- With `k` copies of a letter of positive score `c`, the walk reaches `k c` with probability at
least `q_b^k`. -/
theorem pow_le_scoreProb_le_sum (hq : ∀ b, 0 ≤ q b) (b₀ : β) (k : ℕ) {t : ℝ}
    (ht : t ≤ k * f b₀) : q b₀ ^ k ≤ scoreProb q f k (fun l => t ≤ l.sum) := by
  induction k generalizing t with
  | zero =>
      simp only [Nat.cast_zero, zero_mul] at ht
      simp [scoreProb, scoreExpect_zero, ht]
  | succ k ih =>
      rw [scoreProb_succ, pow_succ']
      calc q b₀ * q b₀ ^ k ≤ q b₀ * scoreProb q f k (fun l => t ≤ (f b₀ :: l).sum) := by
            refine mul_le_mul_of_nonneg_left ?_ (hq b₀)
            refine (ih (t := t - f b₀) (by push_cast at ht; linarith)).trans_eq ?_
            exact scoreProb_congr f fun l _ => by
              rw [List.sum_cons]; constructor <;> intro <;> linarith
        _ ≤ _ := single_le_sum (f := fun a => q a * scoreProb q f k (fun l => t ≤ (f a :: l).sum))
            (fun a _ => mul_nonneg (hq a) (scoreProb_nonneg f hq _ _)) (mem_univ b₀)

theorem scoreProb_maxSegScore_lt_add_le (hq : ∀ b, 0 ≤ q b) (k m : ℕ) (t : ℝ) :
    scoreProb q f (k + m) (fun l => maxSegScore l < t) ≤
      scoreProb q f k (fun l => l.sum < t) * scoreProb q f m (fun l => maxSegScore l < t) := by
  unfold scoreProb
  rw [show m = k + m - k by omega, ← scoreExpect_take_mul_drop f (by omega),
    Nat.add_sub_cancel_left]
  refine scoreExpect_mono f hq fun l _ => ?_
  by_cases hM : maxSegScore l < t
  · have h1 : (l.take k).sum < t :=
      (sum_le_maxSegScore_of_infix (List.take_prefix k l).isInfix).trans_lt hM
    have h2 : maxSegScore (l.drop k) < t :=
      (maxSegScore_mono (List.drop_suffix k l).isInfix).trans_lt hM
    simp [hM, h1, h2]
  · simp only [hM, ↓reduceIte]
    split_ifs <;> norm_num

theorem scoreProb_maxSegScore_lt_antitone (hq : IsDist q) (t : ℝ) :
    Antitone fun n => scoreProb q f n (fun l => maxSegScore l < t) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [scoreProb_succ]
  calc ∑ a, q a * scoreProb q f n (fun l => maxSegScore (f a :: l) < t)
      ≤ ∑ a, q a * scoreProb q f n (fun l => maxSegScore l < t) :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (scoreProb_mono f hq.1 fun l _ h =>
          (le_max_left _ _).trans_lt (by rwa [maxSegScore_cons] at h)) (hq.1 a)
    _ = _ := by rw [← sum_mul, hq.2, one_mul]

/-- **The maximal segment score grows without bound** as soon as positive scores have positive
probability: `P(Mₙ ≥ t) → 1` for every `t`. (Under negative drift it grows like `log n / θ`; the
walk maximum itself stays tight, `scoreProb_le_walkMax_le`.) -/
theorem tendsto_scoreProb_le_maxSegScore (hq : IsDist q) {b₀ : β} (hb₀ : 0 < q b₀)
    (hf₀ : 0 < f b₀) (t : ℝ) :
    Filter.Tendsto (fun n => scoreProb q f n (fun l => t ≤ maxSegScore l)) Filter.atTop
      (nhds 1) := by
  set k := ⌈t / f b₀⌉₊ + 1 with hk
  have hk0 : k ≠ 0 := by omega
  set ρ := q b₀ ^ k with hρ
  have hqb1 : q b₀ ≤ 1 := hq.2 ▸ single_le_sum (fun b _ => hq.1 b) (mem_univ b₀)
  have hρ0 : 0 < ρ := pow_pos hb₀ k
  have hρ1 : ρ ≤ 1 := pow_le_one₀ hb₀.le hqb1
  have htk : t ≤ k * f b₀ := by
    have := Nat.le_ceil (t / f b₀)
    rw [div_le_iff₀ hf₀] at this
    have : (⌈t / f b₀⌉₊ : ℝ) * f b₀ ≤ k * f b₀ :=
      mul_le_mul_of_nonneg_right (by rw [hk]; push_cast; linarith) hf₀.le
    linarith
  have hblock : scoreProb q f k (fun l => l.sum < t) ≤ 1 - ρ := by
    have h1 := scoreProb_add_not f hq k (fun l => t ≤ l.sum)
    have h2 := pow_le_scoreProb_le_sum f hq.1 b₀ k htk
    rw [scoreProb_congr f (Q := fun l => ¬ t ≤ l.sum) fun l _ => not_le.symm]
    linarith
  have hD : ∀ m, scoreProb q f (m * k) (fun l => maxSegScore l < t) ≤ (1 - ρ) ^ m := by
    intro m
    induction m with
    | zero => simpa using scoreProb_le_one f hq 0 (fun l => maxSegScore l < t)
    | succ m ih =>
        rw [show (m + 1) * k = k + m * k by ring, pow_succ']
        exact (scoreProb_maxSegScore_lt_add_le f hq.1 k (m * k) t).trans
          (mul_le_mul hblock ih (scoreProb_nonneg f hq.1 _ _) (by linarith))
  have hup : ∀ n, scoreProb q f n (fun l => maxSegScore l < t) ≤ (1 - ρ) ^ (n / k) := fun n =>
    (scoreProb_maxSegScore_lt_antitone f hq t (Nat.div_mul_le_self n k)).trans (hD _)
  have hlim : Filter.Tendsto (fun n => (1 - ρ) ^ (n / k)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (Nat.tendsto_div_const_atTop hk0)
  have hlt : Filter.Tendsto (fun n => scoreProb q f n (fun l => maxSegScore l < t))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => scoreProb_nonneg f hq.1 _ _) hup
  have heq : ∀ n, scoreProb q f n (fun l => t ≤ maxSegScore l) =
      1 - scoreProb q f n (fun l => maxSegScore l < t) := fun n => by
    have := scoreProb_add_not f hq n (fun l => t ≤ maxSegScore l)
    rw [scoreProb_congr f (P := fun l => ¬ t ≤ maxSegScore l)
      (Q := fun l => maxSegScore l < t) fun l _ => not_le] at this
    linarith
  simp only [heq]
  simpa using hlt.const_sub 1

/-- **Nonnegative expected score** (`E[X] ≥ 0`, `X ≢ 0`): the maximal segment score grows without
bound, `P(Mₙ ≥ t) → 1` for every `t`. -/
theorem tendsto_scoreProb_le_maxSegScore_of_mean_nonneg (hq : IsDist q)
    (hmean : 0 ≤ ∑ b, q b * f b) (hne : ∃ b, 0 < q b ∧ f b ≠ 0) (t : ℝ) :
    Filter.Tendsto (fun n => scoreProb q f n (fun l => t ≤ maxSegScore l)) Filter.atTop
      (nhds 1) := by
  by_cases hpos : ∃ b, 0 < q b ∧ 0 < f b
  · obtain ⟨b₀, hb₀, hf₀⟩ := hpos
    exact tendsto_scoreProb_le_maxSegScore f hq hb₀ hf₀ t
  · push Not at hpos
    obtain ⟨b₁, hb₁, hf₁⟩ := hne
    have hlt : ∑ b, q b * f b < ∑ _b : β, (0 : ℝ) := by
      refine sum_lt_sum (fun b _ => ?_) ⟨b₁, mem_univ _,
        mul_neg_of_pos_of_neg hb₁ (lt_of_le_of_ne (hpos b₁ hb₁) hf₁)⟩
      rcases (hq.1 b).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · exact mul_nonpos_of_nonneg_of_nonpos h.le (hpos b h)
    simp at hlt
    linarith

end Boundary

/-! ## Positive drift: the walk maximum diverges -/

section Drift

variable {q : β → ℝ} (f : β → ℝ)

/-- `E[Sₙ] = n E[X]`. -/
theorem scoreExpect_sum_eq (hq : IsDist q) (n : ℕ) :
    scoreExpect q f n (fun l => l.sum) = n * ∑ b, q b * f b := by
  induction n with
  | zero => simp [scoreExpect_zero]
  | succ n ih =>
      rw [scoreExpect_succ]
      have : ∀ a, scoreExpect q f n (fun l => (f a :: l).sum) = f a + n * ∑ b, q b * f b :=
        fun a => by
          simp only [List.sum_cons]
          rw [scoreExpect_add, scoreExpect_const f hq, ih]
      simp only [this, mul_add, sum_add_distrib, ← sum_mul, hq.2, one_mul]
      push_cast; ring

/-- `Var(Sₙ) = n Var(X)`: `E[(Sₙ - n μ)²] = n ∑_b q_b (f(b) - μ)²`. -/
theorem scoreExpect_sq_sub_eq (hq : IsDist q) (n : ℕ) :
    scoreExpect q f n (fun l => (l.sum - n * ∑ b, q b * f b) ^ 2) =
      n * ∑ b, q b * (f b - ∑ b, q b * f b) ^ 2 := by
  set μ := ∑ b, q b * f b with hμ
  have hc : scoreExpect q f n (fun l => l.sum - n * μ) = 0 := by
    have := scoreExpect_add q f n (fun l => l.sum) (fun _ => -(n * μ))
    rw [scoreExpect_const f hq, scoreExpect_sum_eq f hq] at this
    rw [← sub_self ((n : ℝ) * μ)]
    convert this using 1
  induction n with
  | zero => simp [scoreExpect_zero]
  | succ n ih =>
      have hc' : scoreExpect q f n (fun l => l.sum - n * μ) = 0 := by
        have := scoreExpect_add q f n (fun l => l.sum) (fun _ => -(n * μ))
        rw [scoreExpect_const f hq, scoreExpect_sum_eq f hq] at this
        rw [← sub_self ((n : ℝ) * μ)]
        convert this using 1
      rw [scoreExpect_succ]
      have : ∀ a, scoreExpect q f n (fun l => ((f a :: l).sum - ((n + 1 : ℕ) : ℝ) * μ) ^ 2) =
          (f a - μ) ^ 2 + n * ∑ b, q b * (f b - μ) ^ 2 := fun a => by
        rw [scoreExpect_congr q f (G := fun l => (f a - μ) ^ 2 +
            ((2 * (f a - μ)) * (l.sum - n * μ) + (l.sum - n * μ) ^ 2)) fun l _ => by
              simp only [List.sum_cons]; push_cast; ring,
          scoreExpect_add, scoreExpect_const f hq, scoreExpect_add, scoreExpect_const_mul, hc',
          ih hc']
        ring
      simp only [this, mul_add, sum_add_distrib, ← sum_mul, hq.2, one_mul]
      push_cast; ring

/-- **Chebyshev bound for the walk**: for `t < n μ`,
`P(Sₙ < t) ≤ n σ² / (n μ - t)²`. -/
theorem scoreProb_sum_lt_le (hq : IsDist q) (n : ℕ) {t : ℝ}
    (ht : t < n * ∑ b, q b * f b) :
    scoreProb q f n (fun l => l.sum < t) ≤
      n * (∑ b, q b * (f b - ∑ b, q b * f b) ^ 2) / (n * (∑ b, q b * f b) - t) ^ 2 := by
  set μ := ∑ b, q b * f b
  have hd : 0 < n * μ - t := by linarith
  rw [div_eq_mul_inv, ← scoreExpect_sq_sub_eq f hq, ← scoreExpect_mul_const]
  change _ ≤ scoreExpect q f n fun l => (l.sum - n * μ) ^ 2 * ((n * μ - t) ^ 2)⁻¹
  refine scoreExpect_mono f hq.1 fun l _ => ?_
  by_cases h : l.sum < t
  · simp only [h, ↓reduceIte]
    rw [← div_eq_mul_inv, one_le_div (by positivity)]
    nlinarith
  · simp only [h, ↓reduceIte]
    positivity

/-- **Positive expected score**: the walk maximum diverges, `P(max_{k ≤ n} S_k ≥ t) → 1` for every
`t`; so there is no stationary Lindley law, in contrast with the negative-drift bound
`scoreProb_le_walkMax_le`. -/
theorem tendsto_scoreProb_le_walkMax_of_mean_pos (hq : IsDist q)
    (hmean : 0 < ∑ b, q b * f b) (t : ℝ) :
    Filter.Tendsto (fun n => scoreProb q f n (fun l => t ≤ walkMax l)) Filter.atTop
      (nhds 1) := by
  set μ := ∑ b, q b * f b
  set σ2 := ∑ b, q b * (f b - μ) ^ 2
  have hev : ∀ᶠ n : ℕ in Filter.atTop, t < n * μ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (t / μ)
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    rw [div_lt_iff₀ hmean] at hN
    exact hN.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hmean.le)
  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) * σ2 / (n * μ - t) ^ 2) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => σ2 * ((1 : ℝ) / n) / (μ - t * ((1 : ℝ) / n)) ^ 2)
        Filter.atTop (nhds (σ2 * 0 / (μ - t * 0) ^ 2)) :=
      ((h1.const_mul σ2).div ((tendsto_const_nhds.sub (h1.const_mul t)).pow 2)
        (by simpa using hmean.ne'))
    simp only [mul_zero, zero_div] at h2
    refine h2.congr' (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hlow : ∀ᶠ n : ℕ in Filter.atTop,
      1 - (n : ℝ) * σ2 / (n * μ - t) ^ 2 ≤ scoreProb q f n (fun l => t ≤ walkMax l) := by
    filter_upwards [hev] with n hn
    have h1 := scoreProb_add_not f hq n (fun l => t ≤ l.sum)
    rw [scoreProb_congr f (P := fun l => ¬ t ≤ l.sum) (Q := fun l => l.sum < t)
      fun l _ => not_le] at h1
    have h2 := scoreProb_sum_lt_le f hq n hn
    have h3 := scoreProb_mono f hq.1 (n := n) (P := fun l => t ≤ l.sum)
      (Q := fun l => t ≤ walkMax l) fun l _ h => h.trans (sum_le_walkMax l)
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlim.const_sub 1)
    tendsto_const_nhds hlow (Filter.Eventually.of_forall fun n => scoreProb_le_one f hq _ _)

end Drift

end Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
