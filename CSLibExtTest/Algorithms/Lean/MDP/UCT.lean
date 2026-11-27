/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.UCT
import Cslib.Probability.PMF
import Mathlib.Tactic.NormNum

/-! # Tests for finite-horizon UCT -/

namespace Cslib.Algorithms.Lean.MarkovDecision.UCT.Tests

open scoped NNReal ENNReal

-- Both root actions lead to the same child. Its second visitor must see its first visitor's data.
private noncomputable def fork : Simulator Bool Bool where
  actions _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  draw s a := PMF.pure (true, if s then (if a then 1 / 4 else 1 / 8) else (if a then 1 / 2 else 0))

private theorem fork_draw (s a : Bool) : fork.draw s a = PMF.pure
    (true, if s then (if a then 1 / 4 else 1 / 8) else (if a then 1 / 2 else 0)) := rfl

private theorem choose_false {c : ℝ≥0} {T : Table Bool Bool} {d : ℕ} {s : Bool}
    (h : priority c (visits fork T d s) (T d s true) ≤ priority c (visits fork T d s) (T d s false)) :
    select fork c T d s = false := by
  have hs := (select_spec fork c T d s).2 false (Finset.mem_univ _)
  cases he : select fork c T d s with
  | false => rfl
  | true => rw [he] at hs; exact absurd (hs.2 (le_antisymm hs.1 h)) (by decide)

private theorem choose_true {c : ℝ≥0} {T : Table Bool Bool} {d : ℕ} {s : Bool}
    (h : priority c (visits fork T d s) (T d s false) < priority c (visits fork T d s) (T d s true)) :
    select fork c T d s = true := by
  have hs := (select_spec fork c T d s).2 true (Finset.mem_univ _)
  cases he : select fork c T d s with
  | false => exact absurd (he ▸ hs.1) h.not_ge
  | true => rfl

-- Even a perfect observed mean cannot displace an untried action.
private theorem tried_lt_untried {c : ℝ≥0} {t : ℕ} {u v : Stats} (hu : u.count ≠ 0)
    (hv : v.count = 0) : priority c t u < priority c t v := by
  simp only [priority, ite_eq_right hu, hv, ite_true, WithTop.coe_lt_top]

example (c : ℝ≥0) : select fork c (record empty 0 false false 1) 0 false = true := by
  apply choose_true
  apply tried_lt_untried <;> simp [record, empty, Stats.observe]

-- Counts 1 and 4: the smaller total wins on empirical mean when exploration is disabled.
example : select fork 0 (fun _ _ a => if a then ⟨1, 1⟩ else ⟨4, 2⟩) 2 true = true := by
  apply choose_true
  norm_num [priority, Stats.mean]

-- At the local count 3 these two *tried* actions tie. The less-sampled true action would
-- gain a larger bonus relative to false at a larger clock. Other nodes have arbitrary counts.
example (other : ℕ) :
    let gap := Real.sqrt (Real.log 3) - Real.sqrt (Real.log 3 / 2)
    let T : Table Bool Bool := fun d s a =>
      if d = 1 ∧ s = true then (if a then ⟨1, 0⟩ else ⟨2, 2 * gap⟩) else ⟨other, 0⟩
    select fork (1 / 2) T 1 true = false := by
  apply choose_false
  simp [visits, fork, priority, Stats.mean]

private theorem choose_empty (c : ℝ≥0) (d : ℕ) (s : Bool) : select fork c empty d s = false :=
  choose_false le_rfl

-- At the horizon there is no draw, update or terminal reward, even with a nonempty input table.
example (P : Simulator Bool Bool) (T : Table Bool Bool) (s : Bool) :
    episode P 1 1 T 0 7 s = PMF.pure (0, T) := rfl

-- On the second episode both the root and the shared child try their other action. Projecting
-- the law exhibits the different backups: root gets 1/2 + (1/2)(1/4); child gets 1/4.
example : ((episodes fork 1 (1 / 2) 2 false 2).map fun T =>
    (T 0 false true, T 1 true true, T 1 true false)) =
      PMF.pure (⟨1, 5 / 8⟩, ⟨1, 1 / 4⟩, ⟨1, 1 / 8⟩) := by
  let U := record (record (empty : Table Bool Bool) 1 true false (1 / 8)) 0 false false (1 / 16)
  have hroot : select fork 1 U 0 false = true := by
    apply choose_true
    apply tried_lt_untried <;> simp [U, record, empty, Stats.observe]
  have hchild : select fork 1 U 1 true = true := by
    apply choose_true
    apply tried_lt_untried <;> simp [U, record, empty, Stats.observe]
  have hfirst : episodes fork 1 (1 / 2) 2 false 1 = PMF.pure U := by
    norm_num [episodes, episode, choose_empty, fork_draw, PMF.pure_bind, PMF.pure_map, U]
  rw [episodes, hfirst, PMF.pure_bind]
  simp only [episode, hroot, hchild, fork_draw, PMF.pure_bind, PMF.pure_map]
  norm_num [U, record, Stats.observe, empty]

-- At false a fair coin jointly determines reward and successor. At true there is a different law.
private noncomputable def coin := Cslib.Probability.PMF.uniformOfFintype Bool

private theorem coin_bind {α : Type*} (f : Bool → PMF α) (x : α) :
    (coin.bind f) x = 2⁻¹ * f true x + 2⁻¹ * f false x := by
  simp [coin, PMF.bind_apply, tsum_fintype]

private noncomputable def lottery : Simulator Bool Unit where
  actions _ := {()}
  nonempty _ := Finset.singleton_nonempty _
  draw s _ := if s then PMF.pure (false, 1 / 8) else
    coin.map fun b => (b, if b then 1 / 2 else 1 / 4)

-- The return 3/4 requires false then true on successive calls at the same state and action.
-- Reusing one draw would instead give only 1/2 or 5/8. The probability is (1/2)(1/2).
example : ((episode lottery 1 1 empty 2 0 false).map Prod.fst) (3 / 4) = 1 / 4 := by
  classical
  simp only [episode, lottery, Bool.false_eq_true, ite_false, ite_true, PMF.pure_map,
    PMF.pure_bind, PMF.map_bind, PMF.bind_map, Function.comp_apply, coin_bind]
  norm_num [PMF.pure_apply]
  rw [← sq, ← ENNReal.inv_pow]
  norm_num

-- The same draw must determine the successor as well as the reward: taking the true branch
-- gives 1/2 now and 1/8 in the child. Sampling the two marginals separately would give mass 1/4.
example : ((episode lottery 1 1 empty 2 0 false).map Prod.fst) (5 / 8) = 1 / 2 := by
  classical
  simp only [episode, lottery, Bool.false_eq_true, ite_false, ite_true, PMF.pure_map,
    PMF.pure_bind, PMF.map_bind, PMF.bind_map, Function.comp_apply, coin_bind]
  norm_num [PMF.pure_apply]

-- Two one-step episodes start at false. A total of 3/4 requires two different draws there.
example : ((episodes lottery 1 1 1 false 2).map fun T => (T 0 false ()).total) (3 / 4) = 1 / 2 := by
  classical
  simp only [episodes, episode, lottery, Bool.false_eq_true, ite_false, PMF.pure_map,
    PMF.pure_bind, PMF.map_bind, PMF.bind_map, PMF.bind_bind, Function.comp_apply, coin_bind]
  norm_num [record, Stats.observe, empty, PMF.pure_apply, ← mul_add, ENNReal.inv_two_add_inv_two]

-- Unit one-step rewards fail the two-step undiscounted return-scale convention.
private noncomputable def unitReward : Simulator Unit Unit where
  actions _ := {()}
  nonempty _ := Finset.singleton_nonempty _
  draw _ _ := PMF.pure ((), 1)

example : ¬ ScaledReturns unitReward unitReward.outcomes 1 2 := by
  intro h
  have hz : ((), (1 : ℝ)) ∈ unitReward.outcomes () () := by simp [Simulator.outcomes, unitReward]
  have ha : () ∈ unitReward.actions () := by simp [unitReward]
  have h₁ := PossibleReturn.step ha hz (PossibleReturn.zero (γ := (1 : ℝ)) ())
  have h₂ := h (le_refl 2) (PossibleReturn.step ha hz h₁)
  norm_num at h₂

end Cslib.Algorithms.Lean.MarkovDecision.UCT.Tests
