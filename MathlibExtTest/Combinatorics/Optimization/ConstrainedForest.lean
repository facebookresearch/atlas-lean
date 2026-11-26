/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Optimization.ConstrainedForest
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Optimization.ConstrainedForest

open Finset MathlibExt.Combinatorics.Optimization.ConstrainedForest

private def demand : Finset (Fin 2) → Bool := steinerForestRequirement [(0, 1)]

private theorem demand_false (S : Finset (Fin 2)) : demand S = false ↔ (0 ∈ S ↔ 1 ∈ S) := by
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S <;> simp [demand, steinerForestRequirement, h0, h1]

private theorem demand_true (S : Finset (Fin 2)) :
    demand S = true ↔ ((0 ∈ S ∧ 1 ∉ S) ∨ (1 ∈ S ∧ 0 ∉ S)) := by
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S <;> simp [demand, steinerForestRequirement, h0, h1]

private theorem demand_proper : IsProper demand := by
  constructor
  · intro S
    apply Bool.eq_iff_iff.mpr
    simp only [demand_true, mem_compl, not_not]
    tauto
  · intro A B _ ha hb
    rw [demand_false] at ha hb ⊢
    simp only [mem_union]
    tauto

open Classical in
private theorem edgeFinset_top_fin_two (i : Fintype ↑(⊤ : SimpleGraph (Fin 2)).edgeSet) :
    @SimpleGraph.edgeFinset _ ⊤ i = {s(0, 1)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | _ u v =>
    fin_cases u <;> fin_cases v <;> simp

open Classical in
private theorem cutEdges_top_fin_two (S : Finset (Fin 2)) (hS : demand S = true) :
    cutEdges ⊤ S = {s(0, 1)} := by
  unfold cutEdges
  rw [edgeFinset_top_fin_two, filter_singleton, ite_eq_left]
  rcases (demand_true S).mp hS with h | h
  · exact ⟨0, h.1, 1, h.2, rfl⟩
  · exact ⟨1, h.1, 0, h.2, Sym2.eq_swap⟩

-- A single demand across one edge has two active vertices and approximation factor one.
open Classical in
example :
    ∃ F ⊆ ({s(0, 1)} : Finset (Sym2 (Fin 2))),
      (∀ S, demand S = true → (F ∩ cutEdges ⊤ S).Nonempty) ∧
        ∑ _e ∈ F, (3 : ℝ) ≤ 3 := by
  have hV : demand univ = false := (demand_false _).mpr (by simp)
  have hx (S : Finset (Fin 2)) (hS : demand S = true) :
      1 ≤ ∑ _e ∈ cutEdges ⊤ S, (1 : ℝ) := by rw [cutEdges_top_fin_two S hS]; simp
  have hactive : (univ.filter fun v : Fin 2 => demand {v} = true) = univ := by
    apply filter_eq_self.mpr
    intro v _
    fin_cases v <;> decide
  obtain ⟨F, hF, hfeas, hcost⟩ := exists_forest_cost_le_of_lp_feasible
    (⊤ : SimpleGraph (Fin 2)) (fun _ => 3) (by norm_num) demand demand_proper hV
    (fun _ => 1) (by norm_num) hx
  refine ⟨F, by simpa only [edgeFinset_top_fin_two] using hF, hfeas, ?_⟩
  rw [hactive, edgeFinset_top_fin_two] at hcost
  norm_num at hcost ⊢
  exact hcost

private theorem edgeFinset_bot_fin_two (i : Fintype ↑(⊥ : SimpleGraph (Fin 2)).edgeSet) :
    @SimpleGraph.edgeFinset _ ⊥ i = ∅ := by
  ext e
  calc
    _ ↔ e ∈ (⊥ : SimpleGraph (Fin 2)).edgeSet := @SimpleGraph.mem_edgeFinset _ _ e i
    _ ↔ _ := by rw [SimpleGraph.edgeSet_bot]; simp

-- A repeated endpoint imposes no requirement, even when the graph has no edges.
open Classical in
example :
    ∃ F : Finset (Sym2 (Fin 2)), F = ∅ ∧
      (∀ S, steinerForestRequirement [(0, 0)] S = true →
        (F ∩ cutEdges ⊥ S).Nonempty) ∧ ∑ _e ∈ F, (0 : ℝ) ≤ 0 := by
  have hf (S : Finset (Fin 2)) : steinerForestRequirement [(0, 0)] S = false := by
    simp [steinerForestRequirement]
  have hproper : IsProper (steinerForestRequirement [(0, 0)] : Finset (Fin 2) → Bool) := by
    constructor <;> simp [hf]
  obtain ⟨F, hF, hfeas, _⟩ := exists_forest_cost_le_of_lp_feasible
    (⊥ : SimpleGraph (Fin 2)) (fun _ => 0) (fun _ => le_rfl) _ hproper (hf _) (fun _ => 0)
    (fun _ => le_rfl) (fun S hS => by rw [hf S] at hS; contradiction)
  rw [edgeFinset_bot_fin_two] at hF
  exact ⟨F, subset_empty.mp hF, hfeas, by simp⟩

end MathlibExtTest.Combinatorics.Optimization.ConstrainedForest
