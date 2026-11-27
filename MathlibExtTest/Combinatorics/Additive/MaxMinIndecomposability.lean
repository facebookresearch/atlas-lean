/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MaxMinIndecomposability

open MetaMathlibExt

private def shortDigits : Fin 2 → Fin 3 := fun i => if i = 0 then 1 else 2

-- The base-three polynomial 1 ⊕ 2x is prime: its largest digit occurs at degree one,
-- rather than at the constant term.
example : digitSeq shortDigits ≠ lunarUnit 3 ∧ IsLunarPrime 3 (digitSeq shortDigits) := by
  apply isLunarPrime_of_nonmonomial_indecomposable_candidate (by decide) shortDigits
  · exact ⟨by decide, 1, by decide⟩
  · rintro ⟨i, hi⟩
    have h₀ := (hi 0).mp (by decide : digitSeq shortDigits 0 ≠ 0)
    have h₁ := (hi 1).mp (by decide : digitSeq shortDigits 1 ≠ 0)
    omega
  · intro g h hprod
    have hconst : min (g 0) (h 0) = 1 := by
      rw [← maxMinMul_zero, hprod]
      decide
    have hg₀ : g 0 ≠ 0 := by
      intro hz
      simp [hz] at hconst
    have hh₀ : h 0 ≠ 0 := by
      intro hz
      simp [hz] at hconst
    by_cases he : ∃ i : ℕ, i ≠ 0 ∧ g i ≠ 0
    · obtain ⟨i, hi, hgi⟩ := he
      refine Or.inr ⟨0, fun j => ⟨?_, by rintro rfl; exact hh₀⟩⟩
      intro hj
      by_contra hj₀
      have hpair : (i, j) ∈ Finset.antidiagonal (i + j) := Finset.mem_antidiagonal.mpr rfl
      have hmin : 0 < min (g i) (h j) := lt_min (Nat.pos_of_ne_zero hgi) (Nat.pos_of_ne_zero hj)
      have hlt : 0 < maxMinMul g h (i + j) :=
        hmin.trans_le (Finset.le_sup (f := fun p : ℕ × ℕ => min (g p.1) (h p.2)) hpair)
      rw [hprod, digitSeq_of_le shortDigits (by omega : 2 ≤ i + j)] at hlt
      omega
    · refine Or.inl ⟨0, fun j => ⟨?_, by rintro rfl; exact hg₀⟩⟩
      intro hj
      by_contra hj₀
      exact he ⟨j, hj₀, hj⟩

-- A one-digit string containing only the largest digit represents the unit, not a prime.
example : ¬ (digitSeq (fun _ : Fin 1 => (2 : Fin 3)) ≠ lunarUnit 3 ∧
    IsLunarPrime 3 (digitSeq (fun _ : Fin 1 => (2 : Fin 3)))) := by
  have hunit : digitSeq (fun _ : Fin 1 => (2 : Fin 3)) = lunarUnit 3 := by
    funext k
    cases k with
    | zero => decide
    | succ k =>
      rw [digitSeq_of_le _ (by omega : 1 ≤ k + 1)]
      simp [lunarUnit]
  simp [hunit]
