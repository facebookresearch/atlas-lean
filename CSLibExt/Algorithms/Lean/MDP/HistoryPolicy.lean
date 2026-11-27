/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticPolicy
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # History-dependent randomized policies and finite trajectory laws -/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace Cslib.Algorithms.Lean.MarkovDecision

universe u

/-- A history with `t` completed transitions. At time zero it consists of a state;
thereafter it appends the action taken and the next state to the preceding history. -/
abbrev History (S A : Type u) : ℕ → Type u
  | 0 => S
  | t + 1 => History S A t × (A × S)

namespace History

variable {S A : Type u}

instance [Fintype S] [Fintype A] (t : ℕ) : Fintype (History S A t) := by
  induction t with
  | zero => exact ‹Fintype S›
  | succ t ih =>
    letI : Fintype (History S A t) := ih
    change Fintype (History S A t × (A × S))
    infer_instance

/-- The initial state in a finite history. -/
def origin : (t : ℕ) → History S A t → S
  | 0, s => s
  | t + 1, h => origin t h.1

/-- The state observed after the last transition (the initial state at time zero). -/
def last : (t : ℕ) → History S A t → S
  | 0, s => s
  | _ + 1, h => h.2.2

/-- Every action in the finite history is available at the preceding state. -/
def Legal (available : S → Set A) : (t : ℕ) → History S A t → Prop
  | 0, _ => True
  | t + 1, h => Legal available t h.1 ∧ h.2.1 ∈ available (last t h.1)

end History

/-- A history-dependent randomized policy chooses an action law after every finite history.
Each law is supported on the actions available at the current state. Since it is a PMF,
there is an available action at every state, including when that state is the initial state.
See Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning: Theory and Algorithms*, §1.1.1. -/
structure HistoryPolicy {S A : Type u} (available : S → Set A) where
  /-- The action law conditional on the complete observed history. -/
  actionLaw : (t : ℕ) → History S A t → PMF A
  /-- An unavailable action has zero probability. -/
  available_mass : ∀ t h a, a ∉ available (History.last t h) → actionLaw t h a = 0

namespace HistoryPolicy

variable {S A : Type u} {available : S → Set A}

/-- The alternating policy and transition factors for a finite history, in temporal order. -/
noncomputable def factors (M : MDP S A ℝ) (π : HistoryPolicy available) :
    (t : ℕ) → History S A t → List ℝ
  | 0, _ => []
  | t + 1, h => factors M π t h.1 ++
    [(π.actionLaw t h.1 h.2.1).toReal, M.prob (History.last t h.1) h.2.1 h.2.2]

/-- The product of the policy and transition factors, zero for a different initial state. -/
noncomputable def weight [DecidableEq S] (M : MDP S A ℝ) (π : HistoryPolicy available)
    (s₀ : S) (t : ℕ) (h : History S A t) : ℝ :=
  (if History.origin t h = s₀ then 1 else 0) * (π.factors M t h).prod

private theorem weight_zero [DecidableEq S] (M : MDP S A ℝ) (π : HistoryPolicy available)
    (s₀ s : S) : π.weight M s₀ 0 s = if s = s₀ then 1 else 0 := by
  by_cases hs : s = s₀ <;> simp [weight, factors, History.origin, hs]

private theorem weight_succ [DecidableEq S] (M : MDP S A ℝ) (π : HistoryPolicy available)
    (s₀ : S) (t : ℕ) (h : History S A t) (a : A) (s : S) :
    π.weight M s₀ (t + 1) (h, a, s) =
      π.weight M s₀ t h * (π.actionLaw t h a).toReal * M.prob (History.last t h) a s := by
  by_cases hs : History.origin t h = s₀ <;>
    simp only [weight, factors, History.origin, List.prod_append, List.prod_cons, List.prod_nil,
      hs, ite_true, ite_false, mul_one, zero_mul, one_mul, mul_assoc]

variable [Fintype S] [Fintype A] [DecidableEq S]
variable (M : MDP S A ℝ) (hM : M.Stochastic) (π : HistoryPolicy available) (s₀ : S)

omit [Fintype S] [Fintype A] in
private theorem weight_nonneg (hprob : ∀ s a s', 0 ≤ M.prob s a s')
    (t : ℕ) (h : History S A t) : 0 ≤ π.weight M s₀ t h := by
  induction t with
  | zero =>
    change 0 ≤ π.weight M s₀ 0 (show S from h)
    rw [weight_zero]
    split_ifs <;> simp
  | succ t ih =>
    let p : History S A t × (A × S) := h
    change 0 ≤ π.weight M s₀ (t + 1) (p.1, p.2.1, p.2.2)
    rw [weight_succ]
    exact mul_nonneg (mul_nonneg (ih p.1) ENNReal.toReal_nonneg) (hprob _ _ _)

include hM in
private theorem sum_weight (t : ℕ) : ∑ h : History S A t, π.weight M s₀ t h = 1 := by
  induction t with
  | zero =>
    change (∑ s : S, π.weight M s₀ 0 s) = 1
    simp [weight_zero]
  | succ t ih =>
    change (∑ p : History S A t × (A × S), π.weight M s₀ (t + 1) p) = 1
    rw [Fintype.sum_prod_type]
    refine (Finset.sum_congr rfl fun h _ => ?_).trans ih
    rw [Fintype.sum_prod_type]
    have hrow := (isRowStochastic_ofPMF (π.actionLaw t)).2 h
    change (∑ a, (π.actionLaw t h a).toReal) = 1 at hrow
    calc
      _ = ∑ a, π.weight M s₀ t h * (π.actionLaw t h a).toReal := by
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [weight_succ]
        rw [← Finset.mul_sum, hM.2, mul_one]
      _ = _ := by rw [← Finset.mul_sum, hrow, mul_one]

/-- The finite-history PMF from start `s₀`. The mass is the product of the conditional policy
and transition probabilities along the history, and zero for a different initial state. -/
noncomputable def law (t : ℕ) : PMF (History S A t) :=
  PMF.ofFintype (fun h => ENNReal.ofReal (π.weight M s₀ t h)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => weight_nonneg M π s₀ hM.1 t h),
      sum_weight M hM π s₀ t, ENNReal.ofReal_one])

/-- The real mass of a finite history is its path product. -/
theorem law_toReal_apply (t : ℕ) (h : History S A t) :
    (law M hM π s₀ t h).toReal = π.weight M s₀ t h := by
  rw [law, PMF.ofFintype_apply, ENNReal.toReal_ofReal (weight_nonneg M π s₀ hM.1 t h)]

/-- Appending an action and next state multiplies the prefix mass by their conditional masses. -/
theorem law_toReal_apply_succ (t : ℕ) (h : History S A t) (a : A) (s : S) :
    (law M hM π s₀ (t + 1) (h, a, s)).toReal =
      (law M hM π s₀ t h).toReal * (π.actionLaw t h a).toReal * M.prob (History.last t h) a s := by
  calc
    _ = π.weight M s₀ (t + 1) (h, a, s) := law_toReal_apply M hM π s₀ (t + 1) (h, a, s)
    _ = _ := by rw [weight_succ, law_toReal_apply M hM π s₀ t h]

omit [Fintype S] [Fintype A] in
private theorem weight_eq_zero_of_not_legal (t : ℕ) (h : History S A t)
    (hh : ¬ History.Legal available t h) : π.weight M s₀ t h = 0 := by
  induction t with
  | zero => exact (hh trivial).elim
  | succ t ih =>
    let p : History S A t × (A × S) := h
    change ¬ (History.Legal available t p.1 ∧ p.2.1 ∈ available (History.last t p.1)) at hh
    change π.weight M s₀ (t + 1) (p.1, p.2.1, p.2.2) = 0
    rw [weight_succ]
    by_cases hpre : History.Legal available t p.1
    · rw [π.available_mass t p.1 p.2.1 (fun ha => hh ⟨hpre, ha⟩)]
      simp
    · rw [ih p.1 hpre, zero_mul, zero_mul]

/-- A history with an unavailable action has zero mass under the trajectory law. -/
theorem law_apply_eq_zero_of_not_legal (t : ℕ) (h : History S A t)
    (hh : ¬ History.Legal available t h) : law M hM π s₀ t h = 0 := by
  rw [law, PMF.ofFintype_apply, weight_eq_zero_of_not_legal M π s₀ t h hh, ENNReal.ofReal_zero]

/-- Expected reward at stage `t`, using the law of the history through its next state. -/
noncomputable def expectedReward (t : ℕ) : ℝ :=
  ∑ p : History S A t × (A × S),
    (law M hM π s₀ (t + 1) p).toReal * M.reward (History.last t p.1) p.2.1

/-- The discounted value is the sum of discounted expected stage rewards. -/
noncomputable def discountedValue (γ : ℝ) : ℝ :=
  ∑' t : ℕ, γ ^ t * expectedReward M hM π s₀ t

/-- Bounded rewards and discount `0 ≤ γ < 1` give an absolutely summable value series, even
for randomized policies that depend on the whole history. -/
theorem summable_abs_discountedReward {γ C : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hC : ∀ s a, |M.reward s a| ≤ C) :
    Summable fun t : ℕ => |γ ^ t * expectedReward M hM π s₀ t| := by
  have hbound (t : ℕ) : |expectedReward M hM π s₀ t| ≤ C := by
    unfold expectedReward
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    calc
      _ ≤ ∑ p : History S A t × (A × S), (law M hM π s₀ (t + 1) p).toReal * C :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hC _ _) ENNReal.toReal_nonneg
      _ = C := by
        rw [← Finset.sum_mul]
        change (∑ h : History S A (t + 1), (law M hM π s₀ (t + 1) h).toReal) * C = C
        have hmass := (isRowStochastic_ofPMF (fun _ : Unit => law M hM π s₀ (t + 1))).2 ()
        change (∑ h : History S A (t + 1), (law M hM π s₀ (t + 1) h).toReal) = 1 at hmass
        rw [hmass, one_mul]
  have hgeom := (summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hγ0])).mul_right C
  refine Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_) hgeom
  rw [abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
  exact mul_le_mul_of_nonneg_left (hbound t) (pow_nonneg hγ0 t)

end HistoryPolicy
end Cslib.Algorithms.Lean.MarkovDecision
