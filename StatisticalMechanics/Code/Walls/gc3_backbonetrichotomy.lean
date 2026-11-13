/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Ising.AizenmanSignDominance

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent
open StatMech.Ising

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]













theorem gc3_third_of_two_ox (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hoy : connK ends m o y) : connK ends m o x :=
  hoy.trans (connK_symm ends m hxy)



theorem gc3_third_of_two_oy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hox : connK ends m o x) : connK ends m o y :=
  hox.trans hxy




theorem gc3_third_of_two_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hoy : connK ends m o y) (hox : connK ends m o x) : connK ends m x y :=
  (connK_symm ends m hox).trans hoy

















theorem gc3_no_exactlyTwo (ends : ι → Sym2 V) (m : Finset ι) {o x y : V} :
    ¬ ((connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x)
       ∨ (connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x)
       ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ connK ends m o x)) := by
  rintro (⟨hxy, hoy, hox⟩ | ⟨hxy, hoy, hox⟩ | ⟨hxy, hoy, hox⟩)
  · exact hox (gc3_third_of_two_ox ends m hxy hoy)
  · exact hoy (gc3_third_of_two_oy ends m hxy hox)
  · exact hxy (gc3_third_of_two_xy ends m hoy hox)











theorem gc3_connCount_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x)
      ∨ ((connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x)
         ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x)
         ∨ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x))
      ∨ (connK ends m x y ∧ connK ends m o y ∧ connK ends m o x) := by
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · exact Or.inr (Or.inr ⟨hxy, hoy, hox⟩)
  · exact absurd (gc3_third_of_two_ox ends m hxy hoy) hox
  · exact absurd (gc3_third_of_two_oy ends m hxy hox) hoy
  · exact Or.inr (Or.inl (Or.inl ⟨hxy, hoy, hox⟩))
  · exact absurd (gc3_third_of_two_xy ends m hoy hox) hxy
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hxy, hoy, hox⟩)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hxy, hoy, hox⟩)))
  · exact Or.inl ⟨hxy, hoy, hox⟩



















theorem gc3_backboneFactor_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
      ∨ asd_ghsBackboneFactor ends m o x y = 0
      ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
  unfold asd_ghsBackboneFactor
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · rw [if_pos hxy, if_pos hoy, if_pos hox]; right; right; norm_num
  · exact absurd (gc3_third_of_two_ox ends m hxy hoy) hox
  · exact absurd (gc3_third_of_two_oy ends m hxy hox) hoy
  · rw [if_pos hxy, if_neg hoy, if_neg hox]; right; left; norm_num
  · exact absurd (gc3_third_of_two_xy ends m hoy hox) hxy
  · rw [if_neg hxy, if_pos hoy, if_neg hox]; right; left; norm_num
  · rw [if_neg hxy, if_neg hoy, if_pos hox]; right; left; norm_num
  · rw [if_neg hxy, if_neg hoy, if_neg hox]; left; norm_num






theorem gc3_backboneFactor_ne_neg_one (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y ≠ -1 := by
  rcases gc3_backboneFactor_trichotomy ends m o x y with h | h | h <;> rw [h] <;> norm_num







theorem gc3_backboneFactor_eq_one_iff (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
      ↔ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x) := by
  constructor
  · intro h
    by_contra hcon
    
    unfold asd_ghsBackboneFactor at h
    by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
      by_cases hox : connK ends m o x <;>
      simp only [hxy, hoy, hox, if_true, if_false] at h <;>
      first
        | (exact hcon ⟨hxy, hoy, hox⟩)
        | norm_num at h
  · rintro ⟨hxy, hoy, hox⟩
    exact asd_ghsBackboneFactor_noConn ends m hxy hoy hox





theorem gc3_backboneFactor_eq_neg_two_iff (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = -2
      ↔ (connK ends m x y ∧ connK ends m o y ∧ connK ends m o x) := by
  constructor
  · intro h
    by_contra hcon
    unfold asd_ghsBackboneFactor at h
    by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
      by_cases hox : connK ends m o x <;>
      simp only [hxy, hoy, hox, if_true, if_false] at h <;>
      first
        | (exact hcon ⟨hxy, hoy, hox⟩)
        | norm_num at h
  · rintro ⟨hxy, hoy, hox⟩
    exact asd_ghsBackboneFactor_allConn ends m hxy hoy hox





theorem gc3_backboneFactor_eq_zero_of_exactlyOne (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : (connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x)
       ∨ (¬ connK ends m x y ∧ connK ends m o y ∧ ¬ connK ends m o x)
       ∨ (¬ connK ends m x y ∧ ¬ connK ends m o y ∧ connK ends m o x)) :
    asd_ghsBackboneFactor ends m o x y = 0 := by
  unfold asd_ghsBackboneFactor
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
    simp only [a, b, c, if_true, if_false] <;> norm_num




















theorem gc3_signed_eq_mass_mul_factor (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K)
      - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K)
      = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
          * asd_ghsBackboneFactor ends m o x y := by
  rw [asd_ghsSigned_eq ends m hnd A hm hox hoy hxy φ hφ]
  rfl








theorem gc3_signed_eq_mass_mul_trichotomy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -2)
      ∧ (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {x, y}), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, y}), φ K)
          - (∑ K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {o, x}), φ K)
        = (∑ K ∈ m.powerset.filter (fun K => sources ends K = A), φ K) * c := by
  refine ⟨asd_ghsBackboneFactor ends m o x y, gc3_backboneFactor_trichotomy ends m o x y, ?_⟩
  exact gc3_signed_eq_mass_mul_factor ends m hnd A hm hox hoy hxy φ hφ








open StatMech.Sharpness.FluxEdgeCopy in




theorem gc3_backboneFactor_trichotomy_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) (o x y : W) :
    asd_ghsBackboneFactor (endsM G m) M o x y = 1
      ∨ asd_ghsBackboneFactor (endsM G m) M o x y = 0
      ∨ asd_ghsBackboneFactor (endsM G m) M o x y = -2 :=
  gc3_backboneFactor_trichotomy (endsM G m) M o x y

open StatMech.Sharpness.FluxEdgeCopy in



theorem gc3_no_exactlyTwo_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) {o x y : W} :
    ¬ ((connK (endsM G m) M x y ∧ connK (endsM G m) M o y ∧ ¬ connK (endsM G m) M o x)
       ∨ (connK (endsM G m) M x y ∧ ¬ connK (endsM G m) M o y ∧ connK (endsM G m) M o x)
       ∨ (¬ connK (endsM G m) M x y ∧ connK (endsM G m) M o y ∧ connK (endsM G m) M o x)) :=
  gc3_no_exactlyTwo (endsM G m) M

end StatMech.Walls
