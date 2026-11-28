/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree

/-!
# Tests for smooth arithmetical structures on coconut trees
-/

open MetaMathlibExt

-- The leaf labels 2, 3, 3 have collective gcd one even though two coincide.
example {g : ℕ} (h₂ : g ∣ 2) (h₃ : g ∣ 3) : g = 1 := by
  let d : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 2) ![3, 2, 2]
  let r : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![2, 4, 6] ![2, 3, 3]
  have h : IsSmoothCoconut 3 3 d r := by
    refine ⟨⟨by decide, by decide, ?_, ?_⟩, by decide, by decide⟩
    · intro v
      classical
      rw [finsum_mem_def, finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
      rcases v with i | i <;> fin_cases i <;>
        simp [Fin.sum_univ_three, Set.indicator_apply, coconutTree, SimpleGraph.fromRel_adj, d, r]
    · intro k hk
      have hd : k ∣ Nat.gcd 2 3 := Nat.dvd_gcd (hk (.inl 0)) (hk (.inr 1))
      exact Nat.dvd_one.mp hd
  apply h.eq_one_of_dvd_leaves
  intro j
  fin_cases j <;> first | exact h₂ | exact h₃

-- With no leaves, a smooth structure would make zero equal to one.
example {p : ℕ} {d r : Fin p ⊕ Fin 0 → ℕ} : ¬ IsSmoothCoconut p 0 d r := by
  intro h
  exact Nat.zero_ne_one (h.eq_one_of_dvd_leaves (g := 0) fun j => Fin.elim0 j)

-- When p = 1 the centre has no predecessor, and the leaf sum equals the centre's r-label.
example : ∃ d r : Fin 1 ⊕ Fin 2 → ℕ,
    IsSmoothCoconut 1 2 d r ∧ d (.inl 0) ≤ 1 ∧ (∑ j, r (.inr j)) ≤ r (.inl 0) := by
  let d : Fin 1 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 1) (fun _ => 2)
  let r : Fin 1 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
  have ha : IsArithmeticalStructure (coconutTree 1 2) d r := by
    refine ⟨by decide, by decide, ?_, ?_⟩
    · intro v
      classical
      rw [finsum_mem_def, finsum_eq_sum_of_fintype, Fintype.sum_sum_type, Fin.sum_univ_one,
        Fin.sum_univ_two]
      simp only [Set.indicator_apply]
      rcases v with i | i <;> fin_cases i <;>
        simp [coconutTree, SimpleGraph.fromRel_adj, d, r]
    · intro g hg
      exact Nat.dvd_one.mp (hg (.inr 0))
  have hm := (ha.coconut_tfae.out 1 3).mp (by decide)
  have h : IsSmoothCoconut 1 2 d r := (ha.isSmoothCoconut_iff (by decide)).mpr ⟨by decide, hm⟩
  have hcenter : d (.inl 0) ≤ 1 := h.center_le_one_of_two (by decide)
  refine ⟨d, r, h, hcenter, Nat.le_of_not_gt ?_⟩
  intro hsum
  exact (Nat.not_lt_of_ge hcenter) ((h.one_lt_center_iff (by decide)).mpr hsum)

-- On a two-vertex path the first r-label is strictly below the centre's r-label.
example : ∃ d r : Fin 2 ⊕ Fin 3 → ℕ,
    IsSmoothCoconut 2 3 d r ∧ r (.inl 1) < ∑ j, r (.inr j) ∧ r (.inl 0) < r (.inl 1) := by
  let d : Fin 2 ⊕ Fin 3 → ℕ := fun _ => 2
  let r : Fin 2 ⊕ Fin 3 → ℕ := Sum.elim ![1, 2] (fun _ => 1)
  have h : IsSmoothCoconut 2 3 d r := by
    refine ⟨⟨by decide, by decide, ?_, ?_⟩, by decide, by decide⟩
    · intro v
      classical
      rw [finsum_mem_def, finsum_eq_sum_of_fintype, Fintype.sum_sum_type, Fin.sum_univ_two,
        Fin.sum_univ_three]
      simp only [Set.indicator_apply]
      rcases v with i | i <;> fin_cases i <;>
        simp [coconutTree, SimpleGraph.fromRel_adj, d, r]
    · intro g hg
      exact Nat.dvd_one.mp (hg (.inr 0))
  refine ⟨d, r, h, (h.one_lt_center_iff (by decide)).mp (by decide), ?_⟩
  exact (h.1.isSmoothCoconut_iff (by decide)).mp h |>.2 (show (0 : Fin 2) < 1 by decide)

-- The gaps can increase even when the central d-label is one.
example : ∃ d r : Fin 3 ⊕ Fin 3 → ℕ,
    IsArithmeticalStructure (coconutTree 3 3) d r ∧ d (.inl 2) = 1 ∧
      StrictMono (fun i : Fin 3 => r (.inl i)) ∧
      (r (.inl 1) : ℤ) - r (.inl 0) ≤ (r (.inl 2) : ℤ) - r (.inl 1) := by
  let d : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![2, 3, 1] (fun _ => 5)
  let r : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![1, 2, 5] (fun _ => 1)
  have h : IsArithmeticalStructure (coconutTree 3 3) d r := by
    refine ⟨by decide, by decide, ?_, fun g hg => Nat.dvd_one.mp (hg (.inr 0))⟩
    intro v
    classical
    rw [finsum_mem_def, finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
    rcases v with i | i <;> fin_cases i <;>
      simp [Fin.sum_univ_three, Set.indicator_apply, coconutTree, SimpleGraph.fromRel_adj, d, r]
  have hd : ∀ i : Fin 3, i.val + 1 < 3 → 2 ≤ d (.inl i) := by decide
  refine ⟨d, r, h, rfl, (h.coconut_tfae.out 1 3).mp hd, ?_⟩
  have hgaps := (h.coconut_tfae.out 1 2).mp hd
  exact hgaps.2 0 (by decide)
