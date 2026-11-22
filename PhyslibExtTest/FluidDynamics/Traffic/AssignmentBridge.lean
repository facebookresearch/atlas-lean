/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.AssignmentBridge
import Mathlib.Tactic.NormNum

/-!
# OD assignment checks

Concrete consumers of `PhyslibExt.FluidDynamics.Traffic.AssignmentBridge`: OD node
balance `![-6, 0, 6]` for demand `6` on the pair `(0, 2)`; feasibility of that demand
table on two parallel supplied routes; and rejection of positive demand on the
unreachable pair `(2, 0)`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Balance, admission and rejection

## iv. References

- `PhyslibExt.FluidDynamics.Traffic.AssignmentBridge`
-/

open FluidDynamics.Traffic.AssignmentBridge
open MathlibExt.Combinatorics.Graph.ArcNetwork
open Matrix

/-! ## A. Balance, admission and rejection -/

/-- The public statement shapes of the four assignment results. -/
example {V E P : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype P]
    {tail head : E → V} {orig dest : P → V} {edges : P → List E}
    (hwalk : ∀ p, IsArcWalk tail head (orig p) (dest p) (edges p)) {f : P → ℝ}
    {r : V × V → ℝ} (hdem : ∀ w, ∑ p with (orig p, dest p) = w, f p = r w) (v : V)
    {w : V × V} (hw : ∀ p, (orig p, dest p) ≠ w) (hr : 0 < r w) {o d : V}
    (hod : ¬Relation.ReflTransGen (fun u v => ∃ e, tail e = u ∧ head e = v) o d) :
    (incidenceMatrix tail head).mulVec (edgeVolume edges f) v =
        ∑ o, r (o, v) - ∑ d, r (v, d) ∧
      ((∃ f : P → ℝ, (∀ p, 0 ≤ f p) ∧ ∀ w, ∑ p with (orig p, dest p) = w, f p = r w) ↔
        (∀ w, 0 ≤ r w) ∧ ∀ w, (∀ p, (orig p, dest p) ≠ w) → r w = 0) ∧
      (¬∃ f : P → ℝ, ∀ w', ∑ p with (orig p, dest p) = w', f p = r w') ∧
      ∀ p, (orig p, dest p) ≠ (o, d) :=
  ⟨incidenceMatrix_mulVec_edgeVolume_of_demand hwalk hdem v,
    exists_feasible_pathFlow_iff orig dest r, not_exists_pathFlow_of_unserved hw hr,
    unserved_of_not_reachable hwalk hod⟩

/-- OD node balance at the example table: demand `6` on `(0, 2)` met by flows `4`, `2`
on the parallel routes gives attraction minus production `![-6, 0, 6]`. -/
example :
    (incidenceMatrix ![0, 0, 1, 2] ![1, 1, 2, 0]).mulVec
        (edgeVolume ![([0, 2] : List (Fin 4)), [1, 2]] ![4, 2]) = ![-6, 0, 6] := by
  have hwalk : ∀ p : Fin 2,
      IsArcWalk (![0, 0, 1, 2] : Fin 4 → Fin 3) (![1, 1, 2, 0] : Fin 4 → Fin 3) 0 2
        ((![([0, 2] : List (Fin 4)), [1, 2]]) p) := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;>
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · intro e he
          simp only [List.head?_cons, Option.mem_some] at he
          rw [← he]
          decide
        · refine List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩
          intro b hb
          simp only [List.head?_cons, Option.mem_some] at hb
          rw [← hb]
          decide
        · intro e he
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
          rw [← he]
          decide
  have hdem : ∀ w : Fin 3 × Fin 3,
      ∑ p with ((0 : Fin 3), (2 : Fin 3)) = w, (![4, 2] : Fin 2 → ℝ) p =
        (if w = (0, 2) then (6 : ℝ) else 0) := by
    intro w
    by_cases hw : w = (0, 2)
    · subst hw
      norm_num [Finset.sum_filter, Fin.sum_univ_two]
    · have hempty : Finset.univ.filter (fun _ : Fin 2 => ((0 : Fin 3), (2 : Fin 3)) = w) =
          ∅ := Finset.filter_false_of_mem fun _ _ h => hw h.symm
      rw [hempty, Finset.sum_empty, ite_eq_right hw]
  funext v
  rw [incidenceMatrix_mulVec_edgeVolume_of_demand hwalk hdem]
  fin_cases v <;> simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] <;> norm_num [Prod.mk.injEq, Fin.ext_iff]

/-- Admission at the example table: demand `5` on `(0, 2)` and `0` elsewhere is met by
some nonnegative path flow on the two supplied routes. -/
example :
    ∃ f : Fin 2 → ℝ, (∀ p, 0 ≤ f p) ∧
      ∑ p with ((0 : Fin 3), (2 : Fin 3)) = ((0, 2) : Fin 3 × Fin 3), f p = 5 := by
  have h := (exists_feasible_pathFlow_iff (fun _ : Fin 2 => (0 : Fin 3))
    (fun _ : Fin 2 => (2 : Fin 3))
    (fun w => if w = (0, 2) then 5 else 0)).mpr ⟨?_, ?_⟩
  · obtain ⟨f, hf, hdem⟩ := h
    exact ⟨f, hf, by simpa using hdem (0, 2)⟩
  · intro w
    split <;> norm_num
  · intro w hun
    by_cases hw : w = (0, 2)
    · exact absurd hw.symm (hun 0)
    · simp [hw]

/-- Rejection: on the network with arcs `0 : 0 → 1`, `1 : 0 → 1`, `2 : 1 → 2` only, the
pair `(2, 0)` is unreachable, hence unserved by the routes `[0, 2]`, `[1, 2]`, and unit
demand on it is met by no path flow. -/
example :
    ¬∃ f : Fin 2 → ℝ, ∀ w : Fin 3 × Fin 3,
      ∑ p with ((0 : Fin 3), (2 : Fin 3)) = w, f p = (if w = (2, 0) then 1 else 0) := by
  have hwalk : ∀ p : Fin 2,
      IsArcWalk (![0, 0, 1] : Fin 3 → Fin 3) (![1, 1, 2] : Fin 3 → Fin 3) 0 2
        ((![([0, 2] : List (Fin 3)), [1, 2]]) p) := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;>
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · intro e he
          simp only [List.head?_cons, Option.mem_some] at he
          rw [← he]
          decide
        · refine List.isChain_cons.mpr ⟨?_, List.IsChain.singleton _⟩
          intro b hb
          simp only [List.head?_cons, Option.mem_some] at hb
          rw [← hb]
          decide
        · intro e he
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some] at he
          rw [← he]
          decide
  have hunreach :
      ¬Relation.ReflTransGen (fun u v => ∃ e : Fin 3, ![0, 0, 1] e = u ∧ ![1, 1, 2] e = v)
        (2 : Fin 3) 0 := by
    intro h
    have hstay : ∀ u : Fin 3,
        Relation.ReflTransGen (fun u v => ∃ e : Fin 3, ![0, 0, 1] e = u ∧ ![1, 1, 2] e = v)
          2 u → u = 2 := by
      intro u hu
      induction hu with
      | refl => rfl
      | tail _ hstep ih =>
          obtain ⟨e, ht, -⟩ := hstep
          subst ih
          fin_cases e <;> exact absurd ht (by decide)
    exact (by decide : (0 : Fin 3) ≠ 2) (hstay 0 h)
  have hunserved := unserved_of_not_reachable hwalk hunreach
  exact not_exists_pathFlow_of_unserved hunserved (by norm_num)
