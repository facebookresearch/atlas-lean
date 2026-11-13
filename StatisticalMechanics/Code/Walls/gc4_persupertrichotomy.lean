/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.Walls.gc3_signedperSuper
import Code.Walls.gc3_backbonetrichotomy
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]















theorem gc4_gap_eq_mass_mul_factor (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_gap ends m φ A o x y
      = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y :=
  gc3_gap_eq_mass_mul_backbone ends m hnd A hm hox hoy hxy φ hφ





theorem gc4_factor_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
      ∨ asd_ghsBackboneFactor ends m o x y = 0
      ∨ asd_ghsBackboneFactor ends m o x y = -2 :=
  gc3_backboneFactor_trichotomy ends m o x y




theorem gc4_mass_nonneg (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (A : Finset V) : 0 ≤ aie_mass ends m φ A :=
  aie_mass_nonneg ends m φ hφnn A











theorem gc4_factor_eq_one_of_none (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnone : aie_noneConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = 1 :=
  (gc3_backboneFactor_eq_one_iff ends m o x y).2 hnone





theorem gc4_factor_eq_zero_of_exactlyOne (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = 0 := by
  
  
  simp only [aie_allConn, aie_noneConn] at hnotall hnotnone
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · exact absurd ⟨hxy, hoy, hox⟩ hnotall
  · exact absurd (gc3_third_of_two_ox ends m hxy hoy) hox
  · exact absurd (gc3_third_of_two_oy ends m hxy hox) hoy
  · exact gc3_backboneFactor_eq_zero_of_exactlyOne ends m (Or.inl ⟨hxy, hoy, hox⟩)
  · exact absurd (gc3_third_of_two_xy ends m hoy hox) hxy
  · exact gc3_backboneFactor_eq_zero_of_exactlyOne ends m (Or.inr (Or.inl ⟨hxy, hoy, hox⟩))
  · exact gc3_backboneFactor_eq_zero_of_exactlyOne ends m (Or.inr (Or.inr ⟨hxy, hoy, hox⟩))
  · exact absurd ⟨hxy, hoy, hox⟩ hnotnone




theorem gc4_factor_eq_neg_two_of_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = -2 :=
  (gc3_backboneFactor_eq_neg_two_iff ends m o x y).2 hall























theorem gc4_PerSuperTrichotomy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -2)
      ∧ aie_gap ends m φ A o x y = aie_mass ends m φ A * c
      ∧ 0 ≤ aie_mass ends m φ A := by
  refine ⟨asd_ghsBackboneFactor ends m o x y,
    gc4_factor_trichotomy ends m o x y,
    gc4_gap_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ,
    gc4_mass_nonneg ends m φ hφnn A⟩






theorem gc4_factor_pinned_by_regime (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    (aie_noneConn ends m o x y → asd_ghsBackboneFactor ends m o x y = 1)
      ∧ ((¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y)
          → asd_ghsBackboneFactor ends m o x y = 0)
      ∧ (aie_allConn ends m o x y → asd_ghsBackboneFactor ends m o x y = -2) :=
  ⟨gc4_factor_eq_one_of_none ends m,
   fun ⟨h1, h2⟩ => gc4_factor_eq_zero_of_exactlyOne ends m h1 h2,
   gc4_factor_eq_neg_two_of_all ends m⟩










theorem gc4_gap_value_none (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnone : aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A := by
  refine ⟨?_, gc4_mass_nonneg ends m φ hφnn A⟩
  rw [gc4_gap_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ,
      gc4_factor_eq_one_of_none ends m hnone]
  ring




theorem gc4_gap_value_exactlyOne (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = 0 := by
  rw [gc4_gap_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ,
      gc4_factor_eq_zero_of_exactlyOne ends m hnotall hnotnone]
  ring





theorem gc4_gap_value_all (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A := by
  refine ⟨?_, gc4_mass_nonneg ends m φ hφnn A⟩
  rw [gc4_gap_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ,
      gc4_factor_eq_neg_two_of_all ends m hall]
  ring














theorem gc4_per_super_trichotomy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    (aie_noneConn ends m o x y
        ∧ aie_gap ends m φ A o x y = aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A)
      ∨ ((¬ aie_allConn ends m o x y ∧ ¬ aie_noneConn ends m o x y)
          ∧ aie_gap ends m φ A o x y = 0)
      ∨ (aie_allConn ends m o x y
          ∧ aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A ∧ 0 ≤ aie_mass ends m φ A) := by
  by_cases hall : aie_allConn ends m o x y
  · exact Or.inr (Or.inr ⟨hall,
      gc4_gap_value_all ends m hnd A hm hox hoy hxy φ hφnn hφ hall⟩)
  · by_cases hnone : aie_noneConn ends m o x y
    · exact Or.inl ⟨hnone,
        gc4_gap_value_none ends m hnd A hm hox hoy hxy φ hφnn hφ hnone⟩
    · exact Or.inr (Or.inl ⟨⟨hall, hnone⟩,
        gc4_gap_value_exactlyOne ends m hnd A hm hox hoy hxy φ hφ hall hnone⟩)











theorem gc4_gap_sign_none (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnone : aie_noneConn ends m o x y) :
    0 ≤ aie_gap ends m φ A o x y := by
  obtain ⟨hgap, hmass⟩ := gc4_gap_value_none ends m hnd A hm hox hoy hxy φ hφnn hφ hnone
  rw [hgap]; exact hmass




theorem gc4_gap_sign_all (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y ≤ 0 := by
  obtain ⟨hgap, hmass⟩ := gc4_gap_value_all ends m hnd A hm hox hoy hxy φ hφnn hφ hall
  rw [hgap]; linarith

end StatMech.Walls
