/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tests for identifiability

* A functional that is not identified: the identity on `Bool` with a constant observation.
* Non-vacuity of `BayesNet.backdoorClass`: the two-node network `X → Y` on `Bool` with
  fair-coin tables (built with `StdSimplex.duple`) belongs to the back-door class with the empty
  adjustment set (no path enters `X`, which has no parents).
-/

@[expose] public section

namespace Cslib.MachineLearning.IdentifiabilityTests

open Cslib.MachineLearning GraphicalModels BayesNet

noncomputable def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Convexity.StdSimplex ℝ Bool :=
  Convexity.StdSimplex.duple (t := 1 - p) true false h0 (by linarith) (by ring)

theorem coin_true (p : ℝ) (h0 h1) : (coin p h0 h1).weights true = p := by
  simp [coin, Convexity.StdSimplex.duple]

theorem coin_false (p : ℝ) (h0 h1) : (coin p h0 h1).weights false = 1 - p := by
  simp [coin, Convexity.StdSimplex.duple]

def testPa : (k : Fin 2) → Finset (Fin k) :=
  Fin.cases (motive := fun k => Finset (Fin k)) ∅ (fun _ => {⟨0, Nat.succ_pos _⟩})

noncomputable def testNet : BayesNet Bool 2 where
  pa := testPa
  cpt := fun _ _ => coin (1 / 2) (by norm_num) (by norm_num)

theorem test_cpt_pos (k : Fin 2) (w : testNet.pa k → Bool) (v : Bool) :
    0 < (testNet.cpt k w).weights v := by
  simp only [testNet]
  cases v
  case false =>
    rw [coin_false]
    norm_num
  case true =>
    rw [coin_true]
    norm_num

theorem testNet_joint_pos (x : Fin 2 → Bool) : 0 < testNet.joint x := by
  rw [BayesNet.joint_eq_prod]
  exact Finset.prod_pos fun k _ => test_cpt_pos k _ _

example : (⟨0, by decide⟩ : Fin 1) ∈ testPa 1 := by
  show (⟨0, by decide⟩ : Fin 1) ∈ ({⟨0, Nat.succ_pos _⟩} : Finset (Fin ↑(1 : Fin 2)))
  exact Finset.mem_singleton_self _

example : ¬ IdentifiedOn (Set.univ : Set Bool) (fun _ => ()) id := by
  intro h
  exact Bool.noConfusion (h true (Set.mem_univ true) false (Set.mem_univ false) rfl)

example : testNet ∈ backdoorClass testNet.pa 0 1 ∅ true := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · exact fun z hz => (Finset.notMem_empty z hz).elim
  · intro p _ hex
    obtain ⟨_, hedge⟩ := hex
    obtain ⟨hlt, _⟩ := hedge
    exact absurd hlt (Nat.not_lt_zero _)
  · intro z _
    refine ne_of_gt (Finset.sum_pos (fun x _ => testNet_joint_pos x) ⟨fun _ => true, ?_⟩)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, ?_⟩
    exact funext fun i => absurd i.2 (Finset.notMem_empty _)

end Cslib.MachineLearning.IdentifiabilityTests
