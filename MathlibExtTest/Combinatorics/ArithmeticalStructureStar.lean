/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.ArithmeticalStructureStar

/-!
# Counts for two- and three-leaf stars

Both leaves in a smooth structure must have half the central r-label. Primitivity
gives the unique smooth structure, so the counting formula gives exactly two structures.
On three leaves there are four structures in addition to the smooth ones.
-/

namespace MetaMathlibExt.ArithmeticalStructureStar

private abbrev V := Fin 1 ⊕ Fin 2
private abbrev center : V := .inl 0
private abbrev leaf (i : Fin 2) : V := .inr i

private theorem vertex_sums (r : V → ℕ) :
    (∑ᶠ w ∈ {w | (coconutTree 1 2).Adj center w}, r w) = r (leaf 0) + r (leaf 1) ∧
      ∀ i, (∑ᶠ w ∈ {w | (coconutTree 1 2).Adj (leaf i) w}, r w) = r center := by
  classical
  constructor
  · simp [finsum_eq_sum_of_fintype, Fintype.sum_sum_type, Fin.sum_univ_two,
      center, leaf, coconutTree, SimpleGraph.fromRel_adj]
  · intro i
    fin_cases i <;> simp [finsum_eq_sum_of_fintype, Fintype.sum_sum_type,
      center, leaf, coconutTree, SimpleGraph.fromRel_adj]

private theorem smooth_pair {d r : V → ℕ} :
    IsSmoothCoconut 1 2 d r ↔
      d = Sum.elim (fun _ => 1) (fun _ => 2) ∧ r = Sum.elim (fun _ => 2) (fun _ => 1) := by
  obtain ⟨hc, hl⟩ := vertex_sums r
  constructor
  · intro h
    have he := (h.1.2.2.1 center).trans hc
    have he' (i) := (h.1.2.2.1 (leaf i)).trans (hl i)
    have hbound (i) : 2 * r (leaf i) ≤ r center :=
      (Nat.mul_le_mul_right _ (h.two_le_leaf i)).trans_eq (he' i)
    have hc' := Nat.mul_le_mul_right (r center) (h.1.1 center)
    have heq : r (leaf 0) = r (leaf 1) := by
      have := hbound 0
      have := hbound 1
      omega
    have hr0 : r (leaf 0) = 1 := h.eq_one_of_dvd_leaves (g := r (leaf 0)) fun j => by
      fin_cases j <;> first | exact dvd_rfl | exact heq ▸ dvd_rfl
    have hr (i : Fin 2) : r (leaf i) = 1 := by
      fin_cases i
      · exact hr0
      · exact heq.symm.trans hr0
    have hrc : r center = 2 := by
      have := hbound 0
      rw [hr 0, hr 1] at he
      omega
    have hd (i) : d (leaf i) = 2 := by simpa [hr i, hrc] using he' i
    have hdc : d center = 1 := by simpa [hr, hrc] using he
    constructor <;> funext v <;> rcases v with i | i
    · exact Subsingleton.elim i 0 ▸ hdc
    · exact hd i
    · exact Subsingleton.elim i 0 ▸ hrc
    · exact hr i
  · rintro ⟨rfl, rfl⟩
    refine ⟨⟨by decide, by decide, ?_, fun g hg => Nat.dvd_one.mp (hg (leaf 0))⟩,
      by decide, by decide⟩
    rintro (i | i)
    · rw [Subsingleton.elim i 0]
      exact hc.symm
    · exact (hl i).symm

private theorem smooth_two : Set.ncard {x : (V → ℕ) × (V → ℕ) |
    IsSmoothCoconut 1 2 x.1 x.2} = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨(Sum.elim (fun _ => 1) (fun _ => 2), Sum.elim (fun _ => 2) (fun _ => 1)), ?_⟩
  ext x
  rw [Set.mem_singleton_iff, Prod.ext_iff]
  exact smooth_pair

example : Set.ncard {x : (V → ℕ) × (V → ℕ) |
    IsArithmeticalStructure (coconutTree 1 2) x.1 x.2} = 2 := by
  rw [ncard_arithmeticalStructure_coconutTree_star (by decide : 2 ≤ 2)]
  simpa using congrArg (1 + ·) smooth_two

-- One unit-labelled leaf can occupy any of the three positions.
example : Set.ncard {x : (Fin 1 ⊕ Fin 3 → ℕ) × (Fin 1 ⊕ Fin 3 → ℕ) |
    IsArithmeticalStructure (coconutTree 1 3) x.1 x.2} =
    Set.ncard {x : (Fin 1 ⊕ Fin 3 → ℕ) × (Fin 1 ⊕ Fin 3 → ℕ) |
      IsSmoothCoconut 1 3 x.1 x.2} + 4 := by
  rw [ncard_arithmeticalStructure_coconutTree_star (by decide : 2 ≤ 3)]
  simp [Finset.sum_range_succ, smooth_two]
  omega

end MetaMathlibExt.ArithmeticalStructureStar
