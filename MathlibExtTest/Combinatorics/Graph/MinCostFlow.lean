/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.MinCostFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Examples for arc-indexed minimum-cost flow certificates -/

namespace MathlibExtTest.Combinatorics.Graph.MinCostFlow

open MathlibExt.Combinatorics.Graph.ArcNetwork
open MinCostFlow

-- Two parallel arcs from false to true. The lower bound is negative, and the total transfer
-- is one in both cases. The positive real scale `k` need not be rational.
private abbrev src : Bool → Bool := fun _ => false
private abbrev dst : Bool → Bool := fun _ => true
private abbrev lo : Bool → ℝ := fun _ => -1
private abbrev hi : Bool → ℝ := fun _ => 2
private def bal (v : Bool) : ℝ := if v then 1 else -1
private def f (e : Bool) : ℝ := if e then -1 else 2
private def g (e : Bool) : ℝ := if e then 2 else -1
private noncomputable def cost (k : ℝ) (e : Bool) := if e then k else -2 * k
private def price (k : ℝ) (v : Bool) := if v then k else 0

private theorem f_feasible : lo ≤ f ∧ f ≤ hi ∧ (incidenceMatrix src dst).mulVec f = bal := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; cases e <;> norm_num [f, lo]
  · intro e; cases e <;> norm_num [f, hi]
  · funext v; cases v <;> norm_num [Matrix.mulVec, dotProduct, incidenceMatrix, f, bal, src, dst]

private theorem g_feasible : lo ≤ g ∧ g ≤ hi ∧ (incidenceMatrix src dst).mulVec g = bal := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; cases e <;> norm_num [g, lo]
  · intro e; cases e <;> norm_num [g, hi]
  · funext v; cases v <;> norm_num [Matrix.mulVec, dotProduct, incidenceMatrix, g, bal, src, dst]

private theorem price_valid (k : ℝ) (hk : 0 < k) : IsResidualPotential src dst lo hi f (cost k)
    (price k) := by
  rintro ⟨(e | e), ha⟩ <;> cases e <;>
    norm_num [f, lo, hi] at ha <;>
    norm_num [ResidualArc.cost, ResidualArc.tail, ResidualArc.head, cost, price, src, dst]
  linarith

example (k : ℝ) (hk : 0 < k) : price k false ≠ price k true ∧
    ∀ x, lo ≤ x ∧ x ≤ hi ∧ (incidenceMatrix src dst).mulVec x = bal → cost k ⬝ᵥ f ≤ cost k ⬝ᵥ x :=
  ⟨hk.ne, minimumCost_of_residualPotential f_feasible (price_valid k hk)⟩

-- The gap between these feasible flows is strictly positive for every positive scale.
example (k : ℝ) (hk : 0 < k) : (lo ≤ g ∧ g ≤ hi ∧ (incidenceMatrix src dst).mulVec g = bal) ∧
    cost k ⬝ᵥ g - cost k ⬝ᵥ f = 9 * k ∧ 0 < 9 * k := by
  refine ⟨g_feasible, ?_, by linarith⟩
  simp [dotProduct, cost, f, g]; ring

-- At g the cheap forward arc and the expensive reverse arc close a negative elementary cycle.
example (k : ℝ) (hk : 0 < k) : ∃ p : List (ResidualArc lo hi g),
    IsElementaryCycle (ResidualArc.tail src dst) (ResidualArc.head src dst) false p ∧
      (p.map (ResidualArc.cost (cost k))).sum < 0 := by
  let a : ResidualArc lo hi g := ⟨.inl false, by norm_num [g, hi]⟩
  let b : ResidualArc lo hi g := ⟨.inr true, by norm_num [g, lo]⟩
  refine ⟨[a, b], ⟨by decide, walk_cons_mk rfl (walk_singleton rfl rfl), ?_⟩, ?_⟩
  · change [true, false].Nodup; decide
  · change -2 * k + (-k + 0) < 0; linarith

-- An original forward arc and the reverse of its antiparallel neighbour can share both
-- endpoints without sharing a cost. Both copies are active at the zero flow.
example : ∃ a b : ResidualArc lo hi 0, a.tail id Bool.not = b.tail id Bool.not ∧
    a.head id Bool.not = b.head id Bool.not ∧ a.cost (cost 1) ≠ b.cost (cost 1) := by
  refine ⟨⟨.inl false, by norm_num [hi]⟩, ⟨.inr true, by norm_num [lo]⟩, rfl, rfl, ?_⟩
  change (-2 : ℝ) * 1 ≠ -1; norm_num

-- A fixed bound excludes both directions regardless of the endpoints, even for a loop.
example (x : ℝ) : IsEmpty (ResidualArc (fun _ : Unit => x) (fun _ => x) (fun _ => x)) := by
  constructor
  rintro ⟨(e | e), ha⟩ <;> simp at ha

-- A single negative forward arc 0 → 1 and an isolated vertex 2. Potential existence does
-- not need a chosen source reaching them all, and every valid potential drops strictly here.
private abbrev orig : Unit → Fin 3 := fun _ => 0
private abbrev dest : Unit → Fin 3 := fun _ => 1
private abbrev A := ResidualArc (0 : Unit → ℝ) 1 0

example : ∃ π, IsResidualPotential orig dest 0 1 0 (fun _ => -1) π ∧ π 1 < π 0 := by
  have ends (a : A) : a.tail orig dest = 0 ∧ a.head orig dest = 1 := by
    rcases a with ⟨(e | e), ha⟩
    · exact ⟨rfl, rfl⟩
    · simp at ha
  have noCycle (v : Fin 3) (p : List A) :
      ¬ IsElementaryCycle (ResidualArc.tail orig dest) (ResidualArc.head orig dest) v p := by
    rintro ⟨hne, hw, -⟩
    cases p with
    | nil => exact hne rfl
    | cons a rest =>
      have hstart := (ends a).1.symm.trans (arcWalk_tail_head hw)
      cases rest with
      | nil =>
        have hend := (ends a).2.symm.trans (arcWalk_single_head hw)
        exact (by decide : (0 : Fin 3) ≠ 1) (hstart.trans hend.symm)
      | cons b rest =>
        have hnext := arcWalk_tail_head (walk_tail hw)
        exact (by decide : (0 : Fin 3) ≠ 1) (((ends b).1.symm.trans hnext).trans (ends a).2)
  obtain ⟨π, hπ⟩ := exists_residualPotential_of_no_negative_cycle (c := fun _ => -1)
    (fun v p hp => (noCycle v p hp).elim)
  refine ⟨π, hπ, ?_⟩
  have h := hπ ⟨.inl (), by simp⟩
  change 0 ≤ -1 + π 0 - π 1 at h
  linarith

end MathlibExtTest.Combinatorics.Graph.MinCostFlow
