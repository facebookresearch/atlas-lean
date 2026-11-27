/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Max
import MathlibExt.Robotics.Hybrid.RankedResponse

/-!
# Feasible navigation functions and first arrival

An action type may depend on the current state. Reachability uses **all** legal actions,
whereas a policy selects one at each state. A greedy policy minimises the successor's
potential, not a sum of an action cost and a potential. Only the run up to its first goal
is constrained by the arrival theorems; a goal need not be absorbing.

S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, §8.2.2:
the local operator (8.4) and the three feasibility conditions (pp. 375–376);
the shortest number of stages for unit costs (p. 377). The bounds on first arrival
are deductions from these conditions.
-/

@[expose] public section

namespace Cslib.Planning.Navigation

open scoped ENNReal

variable {X V : Type*} {A : X → Type*}
variable (step : (x : X) → A x → X) (goal : Set X)

/-- The legal one-step relation forgets which action was taken, not whether one exists. -/
def Edge (x y : X) : Prop := ∃ a, step x a = y

/-- A legal walk of exactly `n` actions from `x` to some member of the goal set. -/
def HitsIn (x : X) (n : ℕ) : Prop :=
  ∃ y ∈ goal, Relation.RelatesInSteps (Edge step) x y n

/-- A goal can be reached by a finite legal walk, independently of any policy or potential. -/
def GoalReachable (x : X) : Prop := ∃ n, HitsIn step goal x n

variable {step goal} {x : X} {n : ℕ}

@[simp] theorem hitsIn_zero : HitsIn step goal x 0 ↔ x ∈ goal := by simp [HitsIn]

theorem hitsIn_succ : HitsIn step goal x (n + 1) ↔ ∃ a, HitsIn step goal (step x a) n := by
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨_, ⟨a, rfl⟩, tail⟩ := h.succ'
    exact ⟨a, y, hy, tail⟩
  · rintro ⟨a, y, hy, tail⟩
    exact ⟨y, hy, .head _ _ _ _ ⟨a, rfl⟩ tail⟩

variable (step goal) in
/-- A feasible potential vanishes on goals, is infinite exactly where no goal is reachable,
and admits a strictly descending action at each reachable non-goal. The ordered values may
in particular be extended nonnegative reals or extended naturals. -/
structure Feasible [LT V] [Zero V] [Top V] (φ : X → V) : Prop where
  zero_of_goal : ∀ x ∈ goal, φ x = 0
  top_iff : ∀ x, φ x = ⊤ ↔ ¬ GoalReachable step goal x
  descends : ∀ x, GoalReachable step goal x → x ∉ goal → ∃ a, φ (step x a) < φ x

variable (step) in
/-- A greedy policy chooses a legal action of minimum successor value among *all* legal
choices at that state, without prescribing a tie-break. -/
def Greedy [LE V] (φ : X → V) (π : (x : X) → A x) : Prop :=
  ∀ x a, φ (step x (π x)) ≤ φ (step x a)

/-- Every linearly ordered potential has a greedy policy if each action type is finite and
nonempty. -/
theorem exists_greedy [LinearOrder V] [∀ x, Finite (A x)] [∀ x, Nonempty (A x)]
    (step : (x : X) → A x → X) (φ : X → V) : ∃ π, Greedy step φ π := by
  classical
  have atState (x : X) : ∃ a, ∀ b, φ (step x a) ≤ φ (step x b) := by
    let _ := Fintype.ofFinite (A x)
    simpa using Finset.univ.exists_min_image (fun a => φ (step x a)) Finset.univ_nonempty
  exact ⟨fun x => (atState x).choose, fun x => (atState x).choose_spec⟩

variable (step) in
/-- The state after `n` applications of the policy, starting at `x`. -/
def run (π : (x : X) → A x) (x : X) (n : ℕ) : X := (fun y => step y (π y))^[n] x

variable {π : (x : X) → A x} {φ : X → V}

@[simp] theorem run_zero : run step π x 0 = x := rfl

theorem run_succ : run step π x (n + 1) = step (run step π x n) (π (run step π x n)) :=
  Function.iterate_succ_apply' _ _ _

/-- A first goal at time `n`, with strict descent on every step before it, including the
step into the goal. Nothing is required of the run after time `n`. -/
structure DescendingFirstHit [LT V] (goal : Set X) (φ : X → V) (s : ℕ → X) (n : ℕ) : Prop where
  hit : s n ∈ goal
  before : ∀ k < n, s k ∉ goal
  drop : ∀ k < n, φ (s (k + 1)) < φ (s k)

section Arrival

variable [LinearOrder V] [OrderTop V] [Zero V]

private theorem greedy_drop (hf : Feasible step goal φ) (hg : Greedy step φ π)
    (hr : GoalReachable step goal x) (hn : x ∉ goal) : φ (step x (π x)) < φ x := by
  obtain ⟨a, ha⟩ := hf.descends x hr hn
  exact (hg x a).trans_lt ha

private theorem firstHit_of_measure (hf : Feasible step goal φ) (hg : Greedy step φ π)
    (hr : GoalReachable step goal x) (μ : X → ℕ)
    (hμ : ∀ y z, φ z < φ y → φ y ≠ ⊤ → μ z < μ y) :
    ∃ n ≤ μ x, DescendingFirstHit goal φ (run step π x) n := by
  classical
  let s := run step π x
  have reachable (k : ℕ) (hn : ∀ j < k, s j ∉ goal) : GoalReachable step goal (s k) := by
    induction k with
    | zero => exact hr
    | succ k ih =>
      have hd := greedy_drop hf hg (ih fun j hj => hn j (by omega)) (hn k (by omega))
      rw [show s (k + 1) = step (s k) (π (s k)) from run_succ]
      by_contra h
      exact (hd.trans_le le_top).ne ((hf.top_iff _).2 h)
  have drops (k : ℕ) (hn : ∀ j ≤ k, s j ∉ goal) : φ (s (k + 1)) < φ (s k) := by
    rw [show s (k + 1) = step (s k) (π (s k)) from run_succ]
    exact greedy_drop hf hg (reachable k fun j hj => hn j hj.le) (hn k le_rfl)
  obtain ⟨j, _, hj, hit⟩ := Robotics.Hybrid.exists_goal_of_rank_drops
    (goal := fun k => s k ∈ goal) (ρ := fun k => μ (s k)) (i := 0) (by
      intro k _ h
      have hn := fun j (hj : j ≤ k) => h j (Nat.zero_le j) hj
      have hrk := reachable k fun j hj => hn j hj.le
      exact hμ _ _ (drops k hn) (fun ht => (hf.top_iff _).1 ht hrk))
  have ex : ∃ k, s k ∈ goal := ⟨j, hit⟩
  refine ⟨Nat.find ex, (Nat.find_min' ex hit).trans (by simpa [s] using hj),
    Nat.find_spec ex, fun _ => Nat.find_min ex, ?_⟩
  exact fun k hk => drops k fun j hj => Nat.find_min ex (hj.trans_lt hk)

/-- From every goal-reachable state of a finite system, every greedy policy for a feasible
potential first hits a goal within `|X| - 1` actions and strictly descends up to that hit. -/
theorem firstHit_le_card_sub_one [Fintype X] (hf : Feasible step goal φ) (hg : Greedy step φ π)
    (hr : GoalReachable step goal x) :
    ∃ n ≤ Fintype.card X - 1, DescendingFirstHit goal φ (run step π x) n := by
  classical
  -- Count states of lower potential, not values: ties cause no difficulty.
  let lower (y : X) := Finset.univ.filter fun z => φ z < φ y
  obtain ⟨n, hn, hit⟩ := firstHit_of_measure hf hg hr (fun y => (lower y).card) (by
    intro y z hz _
    apply Finset.card_lt_card
    have sub : lower z ⊆ lower y := fun w hw => Finset.mem_filter.mpr
      ⟨Finset.mem_univ w, (Finset.mem_filter.mp hw).2.trans hz⟩
    exact (Finset.ssubset_iff_of_subset sub).2 ⟨z, by simpa [lower] using hz, by simp [lower]⟩)
  have hcard : (lower x).card < Fintype.card X := Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨x, Finset.mem_univ x, lt_irrefl _⟩)
  exact ⟨n, by omega, hit⟩

end Arrival

/-- For a globally extended-natural-valued feasible potential, a finite initial rank `r`
bounds the first arrival time of every greedy policy. -/
theorem firstHit_le_rank {φ : X → ℕ∞} (hf : Feasible step goal φ) (hg : Greedy step φ π)
    {r : ℕ} (hx : φ x = r) : ∃ n ≤ r, DescendingFirstHit goal φ (run step π x) n := by
  have hr : GoalReachable step goal x := by
    by_contra h
    simpa [hx] using (hf.top_iff x).2 h
  have h := firstHit_of_measure hf hg hr (fun y => (φ y).toNat) (by
    intro y z hzy hy
    exact_mod_cast (show ((φ z).toNat : ℕ∞) < (φ y).toNat by
      rw [ENat.natCast_toNat (hzy.trans_le le_top).ne, ENat.natCast_toNat hy]
      exact hzy))
  simpa [hx] using h

variable (step goal) in
/-- The least length of a legal walk to **any** goal, or infinity when there is none. -/
noncomputable def distance (x : X) : ℕ∞ := by
  classical
  exact if h : GoalReachable step goal x then (Nat.find h : ℕ) else ⊤

@[simp] theorem distance_eq_top : distance step goal x = ⊤ ↔ ¬ GoalReachable step goal x := by
  classical
  by_cases h : GoalReachable step goal x <;> simp [distance, h]

/-- At a reachable state the distance is attained, and no legal walk to any goal is shorter. -/
theorem distance_spec (hr : GoalReachable step goal x) :
    ∃ n : ℕ, distance step goal x = n ∧ IsLeast {k | HitsIn step goal x k} n := by
  classical
  exact ⟨Nat.find hr, by simp [distance, hr], Nat.find_spec hr, fun _ hk => Nat.find_min' hr hk⟩

/-- Minimum legal walk length to the goal set is a feasible extended-natural potential. -/
theorem distance_feasible : Feasible step goal (distance step goal) where
  zero_of_goal x hx := by
    have walk : HitsIn step goal x 0 := hitsIn_zero.mpr hx
    obtain ⟨n, hn, _, least⟩ := distance_spec (show GoalReachable step goal x from ⟨0, walk⟩)
    simpa [Nat.eq_zero_of_le_zero (least walk)] using hn
  top_iff _ := distance_eq_top
  descends x hr hn := by
    obtain ⟨m, hm, walk, _⟩ := distance_spec hr
    cases m with
    | zero => exact (hn (hitsIn_zero.mp walk)).elim
    | succ m =>
      obtain ⟨a, ha⟩ := hitsIn_succ.mp walk
      obtain ⟨k, hk, _, least⟩ := distance_spec
        (show GoalReachable step goal (step x a) from ⟨m, ha⟩)
      refine ⟨a, ?_⟩
      rw [hk, hm]
      exact_mod_cast Nat.lt_succ_of_le (least ha)

/-- The same shortest-walk distance, with values in the extended nonnegative reals. -/
theorem distance_feasible_ennreal :
    Feasible step goal (fun y => (distance step goal y : ℝ≥0∞)) where
  zero_of_goal x hx := by simp [distance_feasible.zero_of_goal x hx]
  top_iff x := by simp
  descends x hr hn := by
    obtain ⟨a, ha⟩ := distance_feasible.descends x hr hn
    exact ⟨a, ENat.toENNReal_lt.mpr ha⟩

/-- As a deduction, a greedy policy for the shortest-walk potential first hits a goal at
exactly the shortest length, regardless of ties. -/
theorem firstHit_at_distance (hg : Greedy step (distance step goal) π)
    (hr : GoalReachable step goal x) :
    ∃ n : ℕ, distance step goal x = n ∧
      DescendingFirstHit goal (distance step goal) (run step π x) n := by
  obtain ⟨d, hd, _, least⟩ := distance_spec hr
  obtain ⟨n, hn, hit⟩ := firstHit_le_rank distance_feasible hg hd
  have legal (k : ℕ) : Relation.RelatesInSteps (Edge step) x (run step π x k) k := by
    induction k with
    | zero => exact .refl x
    | succ k ih => exact .tail _ _ _ _ ih ⟨_, run_succ.symm⟩
  have hdn : d ≤ n := least (show HitsIn step goal x n from ⟨_, hit.hit, legal n⟩)
  exact ⟨n, hn.antisymm hdn ▸ hd, hit⟩

end Cslib.Planning.Navigation
