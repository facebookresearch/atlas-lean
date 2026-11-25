/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Geometry.SimplePolygon
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Simple polygon boundary tests

A clockwise square is simple. A bow-tie with a proper crossing, a triangle with backtracking at
vertex zero, and a sequence that repeats its initial vertex are not simple.
-/

namespace Cslib.Algorithms.Lean.Geometry

private theorem fst_eq_of_mem_segment {a b p : ℝ × ℝ} (hp : p ∈ segment ℝ a b)
    (h : a.1 = b.1) : p.1 = a.1 := by
  obtain ⟨s, t, _, _, hst, heq⟩ := hp
  calc
    p.1 = s * a.1 + t * b.1 := (congrArg Prod.fst heq).symm
    _ = a.1 := by rw [← h, ← add_mul, hst, one_mul]

private theorem snd_eq_of_mem_segment {a b p : ℝ × ℝ} (hp : p ∈ segment ℝ a b)
    (h : a.2 = b.2) : p.2 = a.2 := by
  obtain ⟨s, t, _, _, hst, heq⟩ := hp
  calc
    p.2 = s * a.2 + t * b.2 := (congrArg Prod.snd heq).symm
    _ = a.2 := by rw [← h, ← add_mul, hst, one_mul]

private theorem perpendicular_inter {a b c : ℝ × ℝ}
    (h : (a.1 = b.1 ∧ b.2 = c.2) ∨ (a.2 = b.2 ∧ b.1 = c.1)) :
    segment ℝ a b ∩ segment ℝ b c = {b} := by
  ext p
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hab, hbc⟩
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Prod.ext ((fst_eq_of_mem_segment hab hx).trans hx) (snd_eq_of_mem_segment hbc hy)
    · exact Prod.ext (fst_eq_of_mem_segment hbc hx) ((snd_eq_of_mem_segment hab hy).trans hy)
  · intro hp
    subst p
    exact ⟨right_mem_segment ℝ a b, left_mem_segment ℝ b c⟩

private theorem disjoint_parallel {a b c d : ℝ × ℝ}
    (h : (a.1 = b.1 ∧ c.1 = d.1 ∧ a.1 ≠ c.1) ∨ (a.2 = b.2 ∧ c.2 = d.2 ∧ a.2 ≠ c.2)) :
    Disjoint (segment ℝ a b) (segment ℝ c d) := by
  rw [Set.disjoint_left]
  intro p hab hcd
  rcases h with ⟨h₁, h₂, hne⟩ | ⟨h₁, h₂, hne⟩
  · exact hne ((fst_eq_of_mem_segment hab h₁).symm.trans (fst_eq_of_mem_segment hcd h₂))
  · exact hne ((snd_eq_of_mem_segment hab h₁).symm.trans (snd_eq_of_mem_segment hcd h₂))

private def square : Fin 4 → ℝ × ℝ := ![(0, 0), (0, 1), (1, 1), (1, 0)]

private theorem square_simple : IsSimplePolygon square := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [square] at hij
  · intro i
    fin_cases i <;> apply perpendicular_inter <;>
      first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩
  · intro i j hne hforward hbackward
    fin_cases i <;> fin_cases j
    all_goals first
      | exact (hne rfl).elim
      | exact (hforward rfl).elim
      | exact (hbackward rfl).elim
      | apply disjoint_parallel
        norm_num [square, finRotate_apply]

private def bowTie : Fin 4 → ℝ × ℝ := ![(0, 0), (2, 2), (0, 2), (2, 0)]

private theorem bowTie_not_simple : ¬ IsSimplePolygon bowTie := by
  rintro ⟨_, _, _, nonadjacent⟩
  have h := nonadjacent 0 2 (by decide) (by decide) (by decide)
  change Disjoint (segment ℝ ((0, 0) : ℝ × ℝ) (2, 2)) (segment ℝ (0, 2) (2, 0)) at h
  rw [Set.disjoint_left] at h
  refine h (a := (1, 1)) ?_ ?_ <;>
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩ <;>
    apply Prod.ext <;> norm_num [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

private def backtracking : Fin 3 → ℝ × ℝ := ![(0, 0), (2, 0), (1, 0)]

private theorem wrapAround_overlap_not_simple : ¬ IsSimplePolygon backtracking := by
  rintro ⟨_, _, adjacent, _⟩
  have h := adjacent (Fin.last 2)
  change segment ℝ ((1, 0) : ℝ × ℝ) (0, 0) ∩ segment ℝ (0, 0) (2, 0) = {(0, 0)} at h
  have hx : ((1, 0) : ℝ × ℝ) ∈ segment ℝ (1, 0) (0, 0) ∩ segment ℝ (0, 0) (2, 0) := by
    refine ⟨left_mem_segment ℝ _ _, ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩⟩
    apply Prod.ext <;> norm_num [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [h, Set.mem_singleton_iff] at hx
  norm_num at hx

private theorem repeatedVertex_not_simple :
    ¬ IsSimplePolygon (![(0, 0), (1, 0), (0, 1), (0, 0)] : Fin 4 → ℝ × ℝ) := by
  intro h
  have heq : (0 : Fin 4) = 3 := h.2.1 rfl
  exact (by decide : (0 : Fin 4) ≠ 3) heq

private theorem twoVertices_not_simple (v : Fin 2 → ℝ × ℝ) : ¬ IsSimplePolygon v :=
  fun h => (by decide : ¬ 3 ≤ (2 : ℕ)) h.1

#print axioms IsSimplePolygon
#print axioms square_simple
#print axioms bowTie_not_simple
#print axioms wrapAround_overlap_not_simple
#print axioms repeatedVertex_not_simple
#print axioms twoVertices_not_simple

end Cslib.Algorithms.Lean.Geometry
