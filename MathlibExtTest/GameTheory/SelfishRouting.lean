/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SelfishRouting

open MathlibExt.GameTheory.SelfishRouting

/-- Pigou's network attains the price of anarchy `4/3` of affine latencies. -/
example : pigou.cost pigouWardrop = 4 / 3 * pigou.cost pigouOptimal :=
  pigou_cost_wardrop_eq

/-- The `4/3` bound applied to Pigou's network itself: Pigou's latencies `1` and `x` are
affine with nonnegative coefficients. -/
example : pigou.cost pigouWardrop ≤ 4 / 3 * pigou.cost pigouOptimal :=
  pigou_isWardrop.cost_le_of_affine (a := ![0, 1]) (b := ![1, 0])
    (fun e => by fin_cases e <;> simp) (fun e => by fin_cases e <;> simp)
    (fun e x => by fin_cases e <;> simp [pigou]) pigou_isFeasible_wardrop
    pigou_isFeasible_optimal

/-- The split flow is not a Wardrop flow: the constant-latency path carries flow while the
other path has latency `1/2 < 1`. -/
example : ¬ pigou.IsWardrop pigouOptimal := by
  intro h
  have := h 0 1 rfl (by norm_num [pigouOptimal])
  simp only [RoutingInstance.pathLatency, pigou_edgeFlow] at this
  norm_num [pigou, pigouOptimal] at this

/-- Bicriteria bound in Pigou's network: routing two units with one unit on each edge costs
`1 + 1 = 2 ≥ 1`, the cost of the Wardrop flow for one unit. -/
example : pigou.cost pigouWardrop ≤ pigou.cost ![1, 1] := by
  refine pigou_isWardrop.cost_le_of_feasible_two (r := fun _ => 1)
    (fun e => ?_) (fun e x hx => ?_) pigou_isFeasible_wardrop ⟨fun p => ?_, fun _ => ?_⟩
  · fin_cases e
    · intro x _ y _ _; simp [pigou]
    · intro x _ y _ h; simpa [pigou] using h
  · fin_cases e <;> simp [pigou, hx]
  · fin_cases p <;> simp
  · simp [pigou, Fin.sum_univ_two]; norm_num

/-- Uniqueness of equilibrium cost in Pigou's network: every Wardrop flow for one unit
costs `1`. -/
example (f : Fin 2 → ℝ) (hW : pigou.IsWardrop f)
    (hf : pigou.IsFeasible (fun _ => 1) f) : pigou.cost f = 1 := by
  rw [hW.cost_eq (fun e => ?_) hf pigou_isWardrop pigou_isFeasible_wardrop,
    pigou_cost_wardrop]
  fin_cases e
  · intro x _ y _ _; simp [pigou]
  · intro x _ y _ h; simpa [pigou] using h

/-- Braess's paradox: the Wardrop flow after adding the shortcut is strictly costlier than
before, although the optimal cost cannot increase. -/
example : braessBefore.cost ![1 / 2, 1 / 2] < braessAfter.cost ![0, 0, 1] := by
  have hb : braessBefore.IsFeasible (fun _ => 1) ![1 / 2, 1 / 2] :=
    ⟨fun p => by fin_cases p <;> norm_num, fun _ => by norm_num [braessBefore, Fin.sum_univ_two]⟩
  have ha : braessAfter.IsFeasible (fun _ => 1) ![0, 0, 1] :=
    ⟨fun p => by fin_cases p <;> norm_num, fun _ => by norm_num [braessAfter, Fin.sum_univ_three]⟩
  rw [braess_paradox.1 _ hb braessBefore_isWardrop, braess_paradox.2 _ ha braessAfter_isWardrop]
  norm_num

#print axioms braess_paradox
#print axioms RoutingInstance.IsWardrop.cost_le_of_affine
#print axioms RoutingInstance.IsWardrop.mul_cost_le_of_feasible_one_add
#print axioms RoutingInstance.IsWardrop.cost_eq
