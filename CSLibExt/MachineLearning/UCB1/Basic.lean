/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Nat.Count
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# UCB1

UCB1 (P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit
problem*, Machine Learning 47 (2002) 235–256, Figure 1) plays each of `K` arms once and then,
after `t` plays, an arm `j` maximizing `x̄_j + √(2 ln t / n_j)`, where `n_j` is the number of plays
of arm `j` so far and `x̄_j` the mean of their rewards.

The rewards come from reward stacks: the `m`-th play of arm `j` (counted from `0`) yields the
entry `x j m` of arm `j`'s stack. A run of UCB1 is then a function of the stacks, up to the order
of the first `K` plays and the choice among maximizers.

## Main definitions

* `ucb1Index x t c j`: the UCB1 index of arm `j` after `t` plays, with play counts `c`.
* `IsUCB1Run x A`: the arm sequence `A` is a run of UCB1 on the stacks `x`; its first `K` plays
  may come in any order and its ties may be broken in any way.
* `ucb1Arm x`: the run that plays the arms in order first and then breaks ties toward the least
  index; `isUCB1Run_ucb1Arm` shows that it is a run of UCB1, and `measurable_ucb1Arm` that each of
  its plays is a measurable function of the stacks.

The pull-count bound of the paper is in `CSLibExt.MachineLearning.UCB1.PullCountBound`.
-/

@[expose] public section

namespace Cslib.MachineLearning.UCB1

open Real Finset

variable {K : ℕ}

/-- **UCB1 index**: the index of arm `j` after `t` plays, when each arm `k` has been played `c k`
times and the `m`-th play of arm `k` (counted from `0`) gave the reward `x k m`, is the empirical
mean `(x j 0 + ⋯ + x j (c j - 1)) / c j` of arm `j` plus the exploration bonus
`√(2 ln t / c j)`. For `c j = 0` it is `0`, by Lean's conventions `x / 0 = 0` and `√0 = 0`; a run of
UCB1 uses the index only once every arm has been played. -/
noncomputable def ucb1Index (x : Fin K → ℕ → ℝ) (t : ℕ) (c : Fin K → ℕ) (j : Fin K) : ℝ :=
  (∑ m ∈ range (c j), x j m) / c j + √(2 * log t / c j)

/-- **Run of UCB1 on reward stacks**: `IsUCB1Run x A` says that the arm sequence `A`, which plays
arm `A t` after `t` plays, is a run of UCB1 (Auer, Cesa-Bianchi and Fischer, 2002, Figure 1) on
the reward stacks `x`, where the `m`-th play of arm `j` (counted from `0`) yields the reward
`x j m`. Its first `K` plays play each arm once, in any order, and every later play, made after
`t ≥ K` plays, plays an arm maximizing the UCB1 index `ucb1Index x t c`, where
`c k = #{u < t | A u = k}` is the number of plays of arm `k` so far. Ties may be broken in any
way. -/
def IsUCB1Run (x : Fin K → ℕ → ℝ) (A : ℕ → Fin K) : Prop :=
  (∀ j, Nat.count (A · = j) K = 1) ∧
    ∀ t, K ≤ t → ∀ j, ucb1Index x t (fun k ↦ Nat.count (A · = k) t) j ≤
      ucb1Index x t (fun k ↦ Nat.count (A · = k) t) (A t)

/-- **UCB1 with least-index tie-breaking**: with at least one arm (`K ≥ 1`), the arm that UCB1
plays on the reward stacks `x` after `t` plays is arm `t` if `t < K`, and otherwise the least arm
maximizing the UCB1 index `ucb1Index x t c`, where `c k` is the number of plays of arm `k` so
far. -/
noncomputable def ucb1Arm [NeZero K] (x : Fin K → ℕ → ℝ) (t : ℕ) : Fin K :=
  if h : t < K then ⟨t, h⟩ else
    ((List.finRange K).argmax
      (ucb1Index x t fun j ↦ ((range t).attach.filter fun u ↦ ucb1Arm x u.1 = j).card)).getD 0
termination_by t
decreasing_by all_goals exact mem_range.mp ‹↥(range t)›.2

private lemma ucb1Arm_eq [NeZero K] (x : Fin K → ℕ → ℝ) (t : ℕ) :
    ucb1Arm x t = if h : t < K then ⟨t, h⟩ else
      ((List.finRange K).argmax
        (ucb1Index x t fun j ↦ Nat.count (ucb1Arm x · = j) t)).getD 0 := by
  have hc : (fun j ↦ ((range t).attach.filter fun u ↦ ucb1Arm x u.1 = j).card) =
      fun j ↦ Nat.count (ucb1Arm x · = j) t := by
    funext j
    rw [Nat.count_eq_card_filter_range, filter_attach (fun u ↦ ucb1Arm x u = j), card_map,
      card_attach]
  rw [ucb1Arm, hc]

/-- **UCB1 with least-index tie-breaking is a run of UCB1**: with at least one arm (`K ≥ 1`) and
on all reward stacks, UCB1 with ties broken toward the least index plays each arm once in its
first `K` plays and then always an arm maximizing the UCB1 index. -/
theorem isUCB1Run_ucb1Arm [NeZero K] (x : Fin K → ℕ → ℝ) : IsUCB1Run x (ucb1Arm x) := by
  refine ⟨fun j ↦ ?_, fun t ht j ↦ ?_⟩
  · rw [Nat.count_eq_card_filter_range, card_eq_one]
    refine ⟨j, Finset.ext fun u ↦ ?_⟩
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hu, h⟩
      rw [ucb1Arm_eq, dite_eq_left hu] at h
      exact congrArg Fin.val h
    · rintro rfl
      refine ⟨j.2, ?_⟩
      rw [ucb1Arm_eq, dite_eq_left j.2]
  · set f := ucb1Index x t fun k ↦ Nat.count (ucb1Arm x · = k) t
    obtain ⟨m, hm⟩ : ∃ m, (List.finRange K).argmax f = some m := by
      refine Option.ne_none_iff_exists'.mp fun h ↦ ?_
      rw [List.argmax_eq_none, List.finRange_eq_nil_iff] at h
      exact NeZero.ne K h
    have hA : ucb1Arm x t = m := by
      rw [ucb1Arm_eq, dite_eq_right (not_lt.mpr ht), hm, Option.getD_some]
    rw [hA]
    exact List.le_of_mem_argmax (List.mem_finRange j) hm

/-! ### Measurability -/

open MeasureTheory

/-- The index is a measurable function of the stacks. -/
private lemma measurable_ucb1Index (t : ℕ) (c : Fin K → ℕ) (j : Fin K) :
    Measurable fun x : Fin K → ℕ → ℝ ↦ ucb1Index x t c j :=
  ((Finset.measurable_fun_sum _ fun m _ ↦
    (measurable_pi_apply m).comp (measurable_pi_apply j)).div_const _).add_const _

/-- For fixed play counts, the least maximizer of the index is a measurable function of the
stacks. -/
private lemma measurable_argmax [NeZero K] (t : ℕ) (c : Fin K → ℕ) :
    Measurable fun x : Fin K → ℕ → ℝ ↦
      ((List.finRange K).argmax (ucb1Index x t c)).getD 0 := by
  refine measurable_to_countable' fun m ↦ ?_
  have hne : ∀ x : Fin K → ℕ → ℝ, ∃ m, (List.finRange K).argmax (ucb1Index x t c) = some m :=
    fun x ↦ Option.ne_none_iff_exists'.mp fun h ↦ by
      rw [List.argmax_eq_none, List.finRange_eq_nil_iff] at h
      exact NeZero.ne K h
  have hset : (fun x : Fin K → ℕ → ℝ ↦ ((List.finRange K).argmax (ucb1Index x t c)).getD 0) ⁻¹'
      {m} = {x | (∀ a : Fin K, ucb1Index x t c a ≤ ucb1Index x t c m) ∧
        ∀ a : Fin K, ucb1Index x t c m ≤ ucb1Index x t c a →
          (List.finRange K).idxOf m ≤ (List.finRange K).idxOf a} := by
    ext x
    obtain ⟨m', hm'⟩ := hne x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hm', Option.getD_some, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      obtain ⟨-, h1, h2⟩ := List.argmax_eq_some_iff.mp hm'
      exact ⟨fun a ↦ h1 a (List.mem_finRange a), fun a ha ↦ h2 a (List.mem_finRange a) ha⟩
    · rintro ⟨h1, h2⟩
      have := List.argmax_eq_some_iff.mpr ⟨List.mem_finRange m, fun a _ ↦ h1 a,
        fun a _ ha ↦ h2 a ha⟩
      rw [hm'] at this
      exact Option.some_injective _ this
  rw [hset]
  refine measurableSet_setOfPred.mpr (Measurable.and (Measurable.forall fun a ↦ ?_)
    (Measurable.forall fun a ↦ Measurable.imp ?_ measurable_const))
  · exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_ucb1Index t c a) (measurable_ucb1Index t c m))
  · exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_ucb1Index t c m) (measurable_ucb1Index t c a))

/-- **UCB1 with least-index tie-breaking is measurable**: with at least one arm (`K ≥ 1`), each
play `ucb1Arm x t` is a measurable function of the reward stacks `x`, for the product σ-algebra.
On measurable reward stacks, its plays and its pull counts are therefore random variables. -/
theorem measurable_ucb1Arm [NeZero K] (t : ℕ) :
    Measurable fun x : Fin K → ℕ → ℝ ↦ ucb1Arm x t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  by_cases ht : t < K
  · have : (fun x : Fin K → ℕ → ℝ ↦ ucb1Arm x t) = fun _ ↦ ⟨t, ht⟩ := by
      funext x
      rw [ucb1Arm_eq, dite_eq_left ht]
    rw [this]
    exact measurable_const
  · have hC : Measurable fun x : Fin K → ℕ → ℝ ↦
        fun j ↦ ((range t).attach.filter fun u ↦ ucb1Arm x u.1 = j).card := by
      refine measurable_pi_iff.mpr fun j ↦ ?_
      simp only [card_filter]
      refine Finset.measurable_sum _ fun u _ ↦ Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_eq_fun (ih u (mem_range.mp u.2)) measurable_const
    have hG : Measurable fun p : (Fin K → ℕ → ℝ) × (Fin K → ℕ) ↦
        ((List.finRange K).argmax (ucb1Index p.1 t p.2)).getD 0 :=
      measurable_from_prod_countable_left fun c ↦ measurable_argmax t c
    have := hG.comp (measurable_id.prodMk hC)
    convert this using 1
    funext x
    rw [ucb1Arm.eq_1, dite_eq_right ht]
    rfl

end Cslib.MachineLearning.UCB1
