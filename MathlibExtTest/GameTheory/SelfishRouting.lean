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

/-- The public statement shape of demand admission. -/
example {E ι P : Type*} [Fintype P] [DecidableEq ι] (N : RoutingInstance E ι P)
    (r : ι → ℝ) :
    (∃ f : P → ℝ, N.IsFeasible r f) ↔
      (∀ i, 0 ≤ r i) ∧ ∀ i, (∀ p, N.commodity p ≠ i) → r i = 0 :=
  N.exists_isFeasible_iff r

/-- The public statement shape of unserved-commodity rejection. -/
example {E ι P : Type*} [Fintype P] [DecidableEq ι] (N : RoutingInstance E ι P)
    {r : ι → ℝ} {i : ι} (hi : ∀ p, N.commodity p ≠ i) (hr : 0 < r i) :
    ¬∃ f : P → ℝ, ∀ j, ∑ p with N.commodity p = j, f p = r j :=
  N.not_exists_sum_eq_of_forall_commodity_ne hi hr

/-- OD specialization of admission at the commodity map `p ↦ (orig p, dest p)`. -/
example {V P : Type*} [DecidableEq V] [Fintype P] (orig dest : P → V) (r : V × V → ℝ) :
    (∃ f : P → ℝ, (∀ p, 0 ≤ f p) ∧ ∀ w, ∑ p with (orig p, dest p) = w, f p = r w) ↔
      (∀ w, 0 ≤ r w) ∧ ∀ w, (∀ p, (orig p, dest p) ≠ w) → r w = 0 :=
  RoutingInstance.exists_isFeasible_iff
    (⟨fun p => (orig p, dest p), fun _ => ∅, fun _ _ => 0⟩ :
      RoutingInstance (Fin 1) (V × V) P) r

/-- OD specialization of rejection at the commodity map `p ↦ (orig p, dest p)`. -/
example {V P : Type*} [DecidableEq V] [Fintype P] {orig dest : P → V} {r : V × V → ℝ}
    {w : V × V} (hw : ∀ p, (orig p, dest p) ≠ w) (hr : 0 < r w) :
    ¬∃ f : P → ℝ, ∀ w', ∑ p with (orig p, dest p) = w', f p = r w' :=
  RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne
    (⟨fun p => (orig p, dest p), fun _ => ∅, fun _ _ => 0⟩ :
      RoutingInstance (Fin 1) (V × V) P) hw hr

/-- The `IsFeasible`-form rejection follows in one line. -/
example {E ι P : Type*} [Fintype P] [DecidableEq ι] (N : RoutingInstance E ι P)
    {r : ι → ℝ} {i : ι} (hi : ∀ p, N.commodity p ≠ i) (hr : 0 < r i) :
    ¬∃ f : P → ℝ, N.IsFeasible r f :=
  fun ⟨f, hf⟩ => N.not_exists_sum_eq_of_forall_commodity_ne hi hr ⟨f, hf.2⟩

/-- Admission and rejection at an example table: two paths serve commodity `0` only,
so demand `6` on commodity `0` (and `0` on commodity `1`) is feasible, and unit
demand on commodity `1` is rejected. -/
example :
    (∃ f : Fin 2 → ℝ,
      (⟨![0, 0], fun _ => ∅, fun _ _ => 0⟩ :
        RoutingInstance (Fin 1) (Fin 2) (Fin 2)).IsFeasible ![6, 0] f) ∧
      ¬∃ f : Fin 2 → ℝ,
        (⟨![0, 0], fun _ => ∅, fun _ _ => 0⟩ :
          RoutingInstance (Fin 1) (Fin 2) (Fin 2)).IsFeasible ![0, 1] f := by
  constructor
  · exact (RoutingInstance.exists_isFeasible_iff _ _).mpr
      ⟨fun i => by fin_cases i <;> norm_num, fun i hi => by
        fin_cases i
        · exact absurd rfl (hi 0)
        · norm_num⟩
  · rintro ⟨f, hf⟩
    exact RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne
      (⟨![0, 0], fun _ => ∅, fun _ _ => 0⟩ : RoutingInstance (Fin 1) (Fin 2) (Fin 2))
      (r := ![0, 1]) (i := 1) (fun p => by fin_cases p <;> decide) (by norm_num) ⟨f, hf.2⟩

#print axioms braess_paradox
#print axioms RoutingInstance.IsWardrop.cost_le_of_affine
#print axioms RoutingInstance.IsWardrop.mul_cost_le_of_feasible_one_add
#print axioms RoutingInstance.IsWardrop.cost_eq

#print axioms RoutingInstance.exists_isFeasible_iff
#print axioms RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne
