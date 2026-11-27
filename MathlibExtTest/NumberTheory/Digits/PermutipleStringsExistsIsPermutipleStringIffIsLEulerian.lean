/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringIffIsLEulerian
import Mathlib.Tactic.NormNum

/-!
# Tests of the $L$-Eulerian criterion for permutiple strings

The cycle union for $87912$ satisfies the criterion. Nonempty cycle unions also test
failure of the zero-vertex, connectivity, and balance conditions.

Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025),
Article A111 (arXiv:2505.11414).
-/

namespace MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringIffIsLEulerian

open MetaMathlibExt

private theorem cycles_87912 :
    ∀ vs ∈ ([[2, 8], [1, 7], [9]] : Multiset (List ℕ)), IsMotherGraphCycle 4 10 vs := by
  intro vs hvs
  simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hvs
  rcases hvs with rfl | rfl | rfl <;> unfold IsMotherGraphCycle <;> decide

example : IsLEulerian (multiImageUnion 4 10 ([[2, 8], [1, 7], [9]] : Multiset (List ℕ))) := by
  apply (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ cycles_87912).mp
  exact ⟨[(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)], by decide, isPermutipleString_87912⟩

example : ∃ s : List (ℕ × ℕ),
    (s : Multiset (ℕ × ℕ)) = cycleUnion ([[2, 8], [1, 7], [9]] : Multiset (List ℕ)) ∧
      IsPermutipleString 4 10 s := by
  apply (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ cycles_87912).mpr
  refine ⟨⟨(0, 3), by decide, Or.inl rfl⟩, ?_, ?_⟩
  · intro u v hu hv
    have endpoints (x : ℕ)
        (hx : ∃ e ∈ multiImageUnion 4 10 ([[2, 8], [1, 7], [9]] : Multiset (List ℕ)),
          e.1 = x ∨ e.2 = x) : x = 0 ∨ x = 3 := by
      norm_num [multiImageUnion, cycleUnion, cycleEdges, hoeySloaneTransition] at hx
      omega
    rcases endpoints u hu with rfl | rfl <;> rcases endpoints v hv with rfl | rfl
    · exact .refl
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .refl
  · intro c
    by_cases hc0 : c = 0
    · subst c; decide
    by_cases hc3 : c = 3
    · subst c; decide
    norm_num [multiImageUnion, cycleUnion, cycleEdges, hoeySloaneTransition, hc0, hc3,
      Ne.symm hc0, Ne.symm hc3]

example : IsLEulerian
    (multiImageUnion 4 10 ([[2, 8], [1, 7], [9], [9]] : Multiset (List ℕ))) := by
  have hcycles : ∀ vs ∈ ([[2, 8], [1, 7], [9], [9]] : Multiset (List ℕ)),
      IsMotherGraphCycle 4 10 vs := by
    intro vs hvs
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hvs
    rcases hvs with rfl | rfl | rfl | rfl <;> unfold IsMotherGraphCycle <;> decide
  apply (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ hcycles).mp
  refine ⟨[(2, 8), (1, 7), (9, 9), (9, 9), (7, 1), (8, 2)], by decide, ?_⟩
  refine ⟨⟨3, by decide, 3, by decide, 3, by decide, 3, by decide, 0, by decide,
    0, by decide, rfl⟩, 5, ![2, 1, 9, 9, 7, 8], Fin.revPerm, ?_, by decide⟩
  unfold IsPermutiple
  decide

example : ¬ ∃ s : List (ℕ × ℕ),
    (s : Multiset (ℕ × ℕ)) = cycleUnion ([[9]] : Multiset (List ℕ)) ∧
      IsPermutipleString 4 10 s := by
  intro hs
  have hcycles : ∀ vs ∈ ([[9]] : Multiset (List ℕ)), IsMotherGraphCycle 4 10 vs := by
    intro vs hvs
    have hv : vs = [9] := by simpa using hvs
    subst vs
    unfold IsMotherGraphCycle
    decide
  have h := (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ hcycles).mp hs
  have hz := h.1
  norm_num [multiImageUnion, cycleUnion, cycleEdges, hoeySloaneTransition] at hz

example : ¬ ∃ s : List (ℕ × ℕ),
    (s : Multiset (ℕ × ℕ)) = cycleUnion ([[2, 8]] : Multiset (List ℕ)) ∧
      IsPermutipleString 4 10 s := by
  intro hs
  have hcycles : ∀ vs ∈ ([[2, 8]] : Multiset (List ℕ)), IsMotherGraphCycle 4 10 vs := by
    intro vs hvs
    have hv : vs = [2, 8] := by simpa using hvs
    subst vs
    unfold IsMotherGraphCycle
    decide
  have h := (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ hcycles).mp hs
  have hc := h.2.2 3
  norm_num [multiImageUnion, cycleUnion, cycleEdges, hoeySloaneTransition] at hc

example : ¬ ∃ s : List (ℕ × ℕ),
    (s : Multiset (ℕ × ℕ)) = cycleUnion ([[0], [9]] : Multiset (List ℕ)) ∧
      IsPermutipleString 4 10 s := by
  intro hs
  have hcycles : ∀ vs ∈ ([[0], [9]] : Multiset (List ℕ)), IsMotherGraphCycle 4 10 vs := by
    intro vs hvs
    simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hvs
    rcases hvs with rfl | rfl <;> unfold IsMotherGraphCycle <;> decide
  have h := (exists_isPermutipleString_iff_isLEulerian 4 10 (by decide) (by decide)
    _ hcycles).mp hs
  have hp := h.2.1 0 3 ⟨(0, 0), by decide, Or.inl rfl⟩
    ⟨(3, 3), by decide, Or.inl rfl⟩
  have same {x y : ℕ}
      (he : (x, y) ∈ multiImageUnion 4 10 ([[0], [9]] : Multiset (List ℕ))) : x = y := by
    norm_num [multiImageUnion, cycleUnion, cycleEdges, hoeySloaneTransition] at he
    omega
  have equal {y : ℕ}
      (hy : Relation.ReflTransGen
        (fun x y => (x, y) ∈ multiImageUnion 4 10 ([[0], [9]] : Multiset (List ℕ))) 0 y) :
      0 = y := by
    induction hy with
    | refl => rfl
    | tail hy he ih => exact ih.trans (same he)
  exact (by decide : (0 : ℕ) ≠ 3) (equal hp)

end MathlibExtTest.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringIffIsLEulerian
