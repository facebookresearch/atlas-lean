/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.PlanarDual
import Code.Lattice.StraightWalk

open Set SimpleGraph
open StatMech StatMech.Lattice

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000




theorem bcor_origin_eq : (![0, 0] : Site 2) = 0 := by
  funext i; fin_cases i <;> rfl


theorem bcor_mem_box {a b : ℤ} {n : ℕ} (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    (![a, b] : Site 2) ∈ box 2 n := by
  rw [mem_box]
  intro i; fin_cases i
  · simpa using ha
  · simpa using hb


theorem bcor_uIcc_natAbs {s t : ℤ} {n : ℕ} (hs : s.natAbs ≤ n) (ht : t ∈ Set.uIcc 0 s) :
    t.natAbs ≤ n := by
  rw [Set.mem_uIcc] at ht
  omega







def bcor_Corridors (n : ℕ) (u₁ u₂ u₃ : Site 2) : Prop :=
  ∃ (P₁ : (hypercubicLattice 2).Walk ![0, 0] u₁)
    (P₂ : (hypercubicLattice 2).Walk ![0, 0] u₂)
    (P₃ : (hypercubicLattice 2).Walk ![0, 0] u₃),
      P₁.IsPath ∧ P₂.IsPath ∧ P₃.IsPath ∧
      (∀ z ∈ P₁.support, z ∈ box 2 n) ∧
      (∀ z ∈ P₂.support, z ∈ box 2 n) ∧
      (∀ z ∈ P₃.support, z ∈ box 2 n) ∧
      (∀ z, z ∈ P₁.support → z ∈ P₂.support → z = ![0, 0]) ∧
      (∀ z, z ∈ P₁.support → z ∈ P₃.support → z = ![0, 0]) ∧
      (∀ z, z ∈ P₂.support → z ∈ P₃.support → z = ![0, 0])




theorem bcor_rot90_mem_box {n : ℕ} {x : Site 2} (hx : x ∈ box 2 n) :
    rot90Fun x ∈ box 2 n := by
  rw [mem_box] at hx ⊢
  intro i
  fin_cases i
  · simpa [rot90Fun] using hx 1
  · simpa [rot90Fun] using hx 0




theorem bcor_corridors_rot90 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    bcor_Corridors n (rot90Fun u₁) (rot90Fun u₂) (rot90Fun u₃) := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  have hstart : rot90Fun ![0, 0] = (![0, 0] : Site 2) := by
    rw [rot90Fun_apply]
    rfl
  let M₁ := P₁.map rot90Iso.toHom
  let M₂ := P₂.map rot90Iso.toHom
  let M₃ := P₃.map rot90Iso.toHom
  let Q₁ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₁) := M₁.copy hstart rfl
  let Q₂ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₂) := M₂.copy hstart rfl
  let Q₃ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₃) := M₃.copy hstart rfl
  have hq1 : Q₁.IsPath := by
    simpa [Q₁, M₁, Walk.isPath_copy] using
      P₁.map_isPath_of_injective rot90Iso.injective hp1
  have hq2 : Q₂.IsPath := by
    simpa [Q₂, M₂, Walk.isPath_copy] using
      P₂.map_isPath_of_injective rot90Iso.injective hp2
  have hq3 : Q₃.IsPath := by
    simpa [Q₃, M₃, Walk.isPath_copy] using
      P₃.map_isPath_of_injective rot90Iso.injective hp3
  refine ⟨Q₁, Q₂, Q₃, hq1, hq2, hq3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb1 x hx)
  · intro z hz
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb2 x hx)
  · intro z hz
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb3 x hx)
  · intro z hz1 hz2
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz2
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd12 x hx hy)
  · intro z hz1 hz3
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd13 x hx hy)
  · intro z hz2 hz3
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz2
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd23 x hx hy)



theorem bcor_corridors_rot90_iterate (k : ℕ) {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    bcor_Corridors n ((rot90Fun^[k]) u₁) ((rot90Fun^[k]) u₂)
      ((rot90Fun^[k]) u₃) := by
  induction k with
  | zero => simpa using hC
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using bcor_corridors_rot90 ih


theorem bcor_corridors_swap12 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) : bcor_Corridors n u₂ u₁ u₃ := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  refine ⟨P₂, P₁, P₃, hp2, hp1, hp3, hb2, hb1, hb3, ?_, ?_, ?_⟩
  · intro z hz2 hz1
    exact hd12 z hz1 hz2
  · exact hd23
  · exact hd13


theorem bcor_corridors_swap23 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) : bcor_Corridors n u₁ u₃ u₂ := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  refine ⟨P₁, P₃, P₂, hp1, hp3, hp2, hb1, hb3, hb2, hd13, hd12, ?_⟩
  intro z hz3 hz2
  exact hd23 z hz2 hz3




def bcor_reflFun (x : Site 2) : Site 2 := ![x 0, -x 1]

@[simp] theorem bcor_reflFun_apply (a b : ℤ) :
    bcor_reflFun ![a, b] = ![a, -b] := by
  funext i; fin_cases i <;> simp [bcor_reflFun]


def bcor_reflEquiv : Site 2 ≃ Site 2 where
  toFun := bcor_reflFun
  invFun := bcor_reflFun
  left_inv := by intro x; funext i; fin_cases i <;> simp [bcor_reflFun]
  right_inv := by intro x; funext i; fin_cases i <;> simp [bcor_reflFun]

theorem bcor_refl_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (bcor_reflFun x) (bcor_reflFun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [bcor_reflFun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg]


def bcor_reflIso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨bcor_reflEquiv, fun {x y} ↦ bcor_refl_adj x y⟩

theorem bcor_refl_mem_box {n : ℕ} {x : Site 2} (hx : x ∈ box 2 n) :
    bcor_reflFun x ∈ box 2 n := by
  rw [mem_box] at hx ⊢
  intro i
  fin_cases i
  · simpa [bcor_reflFun] using hx 0
  · simpa [bcor_reflFun] using hx 1


theorem bcor_corridors_refl {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    bcor_Corridors n (bcor_reflFun u₁) (bcor_reflFun u₂) (bcor_reflFun u₃) := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  have hstart : bcor_reflFun ![0, 0] = (![0, 0] : Site 2) := by simp
  let M₁ := P₁.map bcor_reflIso.toHom
  let M₂ := P₂.map bcor_reflIso.toHom
  let M₃ := P₃.map bcor_reflIso.toHom
  let Q₁ : (hypercubicLattice 2).Walk ![0, 0] (bcor_reflFun u₁) := M₁.copy hstart rfl
  let Q₂ : (hypercubicLattice 2).Walk ![0, 0] (bcor_reflFun u₂) := M₂.copy hstart rfl
  let Q₃ : (hypercubicLattice 2).Walk ![0, 0] (bcor_reflFun u₃) := M₃.copy hstart rfl
  have hq1 : Q₁.IsPath := by
    simpa [Q₁, M₁, Walk.isPath_copy] using
      P₁.map_isPath_of_injective bcor_reflEquiv.injective hp1
  have hq2 : Q₂.IsPath := by
    simpa [Q₂, M₂, Walk.isPath_copy] using
      P₂.map_isPath_of_injective bcor_reflEquiv.injective hp2
  have hq3 : Q₃.IsPath := by
    simpa [Q₃, M₃, Walk.isPath_copy] using
      P₃.map_isPath_of_injective bcor_reflEquiv.injective hp3
  refine ⟨Q₁, Q₂, Q₃, hq1, hq2, hq3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_refl_mem_box (hb1 x hx)
  · intro z hz
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_refl_mem_box (hb2 x hx)
  · intro z hz
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_refl_mem_box (hb3 x hx)
  · intro z hz1 hz2
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz2
    have hxy : x = y := bcor_reflEquiv.injective heq.symm
    subst y
    simpa using congrArg bcor_reflFun (hd12 x hx hy)
  · intro z hz1 hz3
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := bcor_reflEquiv.injective heq.symm
    subst y
    simpa using congrArg bcor_reflFun (hd13 x hx hy)
  · intro z hz2 hz3
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz2
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := bcor_reflEquiv.injective heq.symm
    subst y
    simpa using congrArg bcor_reflFun (hd23 x hx hy)




















theorem bcor_corridors_RTL (n : ℕ) (hn : 1 ≤ n) (s t r : ℤ)
    (hs : s.natAbs ≤ n) (ht : t.natAbs ≤ n) (hr : r.natAbs ≤ n)
    (h12 : (![(n : ℤ), s] : Site 2) ≠ ![t, (n : ℤ)])
    (h23 : (![t, (n : ℤ)] : Site 2) ≠ ![(-(n : ℤ)), r]) :
    bcor_Corridors n ![(n : ℤ), s] ![t, (n : ℤ)] ![(-(n : ℤ)), r] := by
  
  set W₁ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), s] := sw_lshape 0 0 (n : ℤ) s with hW1
  set W₂ : (hypercubicLattice 2).Walk ![0, 0] ![t, (n : ℤ)] :=
    (sw_vertSeg 0 0 (n : ℤ)).append (sw_horizSeg (n : ℤ) 0 t) with hW2
  set W₃ : (hypercubicLattice 2).Walk ![0, 0] ![(-(n : ℤ)), r] := sw_lshape 0 0 (-(n : ℤ)) r with hW3
  
  have hW1supp : ∀ z : Site 2, z ∈ W₁.support ↔
      (∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![a, 0]) ∨
      (∃ a : ℤ, a ∈ Set.uIcc 0 s ∧ z = ![(n : ℤ), a]) := by
    intro z; rw [hW1]; exact sw_lshape_support_eq 0 0 (n : ℤ) s z
  have hW3supp : ∀ z : Site 2, z ∈ W₃.support ↔
      (∃ a : ℤ, a ∈ Set.uIcc 0 (-(n : ℤ)) ∧ z = ![a, 0]) ∨
      (∃ a : ℤ, a ∈ Set.uIcc 0 r ∧ z = ![(-(n : ℤ)), a]) := by
    intro z; rw [hW3]; exact sw_lshape_support_eq 0 0 (-(n : ℤ)) r z
  have hW2supp : ∀ z : Site 2, z ∈ W₂.support ↔
      (∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![0, a]) ∨
      (∃ a : ℤ, a ∈ Set.uIcc 0 t ∧ z = ![a, (n : ℤ)]) := by
    intro z
    rw [hW2, Walk.mem_support_append_iff, sw_vertSeg_mem_support, sw_horizSeg_mem_support]
  refine ⟨W₁.bypass, W₂.bypass, W₃.bypass, W₁.bypass_isPath, W₂.bypass_isPath,
    W₃.bypass_isPath, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro z hz
    rcases (hW1supp z).mp (W₁.support_bypass_subset hz) with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (bcor_uIcc_natAbs (by simp : ((n:ℤ)).natAbs ≤ n) ha) (by simp)
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs hs ha)
  · 
    intro z hz
    rcases (hW2supp z).mp (W₂.support_bypass_subset hz) with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs (by simp : ((n:ℤ)).natAbs ≤ n) ha)
    · exact bcor_mem_box (bcor_uIcc_natAbs ht ha) (by simp)
  · 
    intro z hz
    rcases (hW3supp z).mp (W₃.support_bypass_subset hz) with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · refine bcor_mem_box ?_ (by simp)
      have : (-(n : ℤ)).natAbs ≤ n := by simp
      exact bcor_uIcc_natAbs this ha
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs hr ha)
  · 
    intro z h1 h2
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    rcases h1' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases h2' with ⟨b, hb, hz⟩ | ⟨b, hb, hz⟩
    · 
      have e0 := congrFun hz 0; have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
      subst e0; rfl
    · 
      exfalso; have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e1
      omega
    · 
      exfalso; have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      omega
    · 
      exfalso
      have e0 := congrFun hz 0; have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
      rw [Set.mem_uIcc] at ha hb
      have hsn : s = (n : ℤ) := by omega
      have htn : t = (n : ℤ) := by omega
      exact h12 (by rw [hsn, htn])
  · 
    intro z h1 h3
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h1' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases h3' with ⟨b, hb, hz⟩ | ⟨b, hb, hz⟩
    · 
      have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      rw [Set.mem_uIcc] at ha hb
      have : a = 0 := by omega
      subst this; rfl
    · 
      exfalso
      have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      rw [Set.mem_uIcc] at ha
      omega
    · 
      exfalso
      have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      rw [Set.mem_uIcc] at hb
      omega
    · 
      exfalso
      have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      omega
  · 
    intro z h2 h3
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h2' with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ <;>
      rcases h3' with ⟨b, hb, hz⟩ | ⟨b, hb, hz⟩
    · 
      have e0 := congrFun hz 0; have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
      rw [Set.mem_uIcc] at ha hb
      have : a = 0 := by omega
      subst this; ext i; fin_cases i <;> simp_all
    · 
      exfalso
      have e0 := congrFun hz 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0
      omega
    · 
      exfalso
      have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e1
      omega
    · 
      exfalso
      have e0 := congrFun hz 0; have e1 := congrFun hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
      rw [Set.mem_uIcc] at ha hb
      have htn : t = (-(n : ℤ)) := by omega
      have hrn : r = (n : ℤ) := by omega
      exact h23 (by rw [htn, hrn])











theorem bcor_corridors_two_right_upper (n : ℕ) (hn : 1 ≤ n)
    (y₁ y₂ x y : ℤ)
    (hy₁ : y₁.natAbs ≤ n) (hy₂ : y₂.natAbs ≤ n)
    (hx : x.natAbs ≤ n) (hy : y.natAbs ≤ n)
    (h12 : y₁ < y₂) (h2top : y₂ < n)
    (houter : y = n ∨ x = -(n : ℤ)) :
    bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![x, y] := by
  set W₁ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), y₁] :=
    ((sw_vertSeg 0 0 (-(n : ℤ))).append (sw_horizSeg (-(n : ℤ)) 0 (n : ℤ))).append
      (sw_vertSeg (n : ℤ) (-(n : ℤ)) y₁) with hW1
  set W₂ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), y₂] :=
    ((sw_horizSeg 0 0 1).append (sw_vertSeg 1 0 y₂)).append
      (sw_horizSeg y₂ 1 (n : ℤ)) with hW2
  set W₃ : (hypercubicLattice 2).Walk ![0, 0] ![x, y] :=
    ((sw_vertSeg 0 0 (n : ℤ)).append (sw_horizSeg (n : ℤ) 0 x)).append
      (sw_vertSeg x (n : ℤ) y) with hW3
  have hW1supp : ∀ z : Site 2, z ∈ W₁.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 (-(n : ℤ)) ∧ z = ![0, a]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![a, (-(n : ℤ))])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc (-(n : ℤ)) y₁ ∧ z = ![(n : ℤ), a]) := by
    intro z
    rw [hW1, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_vertSeg_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]
  have hW2supp : ∀ z : Site 2, z ∈ W₂.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 1 ∧ z = ![a, 0]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 y₂ ∧ z = ![1, a])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc 1 (n : ℤ) ∧ z = ![a, y₂]) := by
    intro z
    rw [hW2, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_horizSeg_mem_support, sw_vertSeg_mem_support, sw_horizSeg_mem_support]
  have hW3supp : ∀ z : Site 2, z ∈ W₃.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![0, a]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 x ∧ z = ![a, (n : ℤ)])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc (n : ℤ) y ∧ z = ![x, a]) := by
    intro z
    rw [hW3, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_vertSeg_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]
  refine ⟨W₁.bypass, W₂.bypass, W₃.bypass, W₁.bypass_isPath, W₂.bypass_isPath,
    W₃.bypass_isPath, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (hW1supp z).mp (W₁.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs (by simp) ha)
    · exact bcor_mem_box (bcor_uIcc_natAbs (by simp) ha) (by simp)
    · rw [Set.mem_uIcc] at ha
      apply bcor_mem_box (by simp)
      omega
  · intro z hz
    rcases (hW2supp z).mp (W₂.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · apply bcor_mem_box
      · rw [Set.mem_uIcc] at ha
        omega
      · simp
    · exact bcor_mem_box (by omega) (bcor_uIcc_natAbs hy₂ ha)
    · rw [Set.mem_uIcc] at ha
      apply bcor_mem_box ?_ hy₂
      omega
  · intro z hz
    rcases (hW3supp z).mp (W₃.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs (by simp) ha)
    · exact bcor_mem_box (bcor_uIcc_natAbs hx ha) (by simp)
    · apply bcor_mem_box hx
      rw [Set.mem_uIcc] at ha
      omega
  · intro z h1 h2
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    rcases h1' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h2' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · intro z h1 h3
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h1' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h3' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rcases houter with htop | hleft <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] at * <;> omega
  · intro z h2 h3
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h2' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h3' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rcases houter with htop | hleft <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] at * <;> omega


theorem bcor_corridors_two_right_lower (n : ℕ) (hn : 1 ≤ n)
    (y₁ y₂ x y : ℤ)
    (hy₁ : y₁.natAbs ≤ n) (hy₂ : y₂.natAbs ≤ n)
    (hx : x.natAbs ≤ n) (hy : y.natAbs ≤ n)
    (h12 : y₁ < y₂) (hbot1 : -(n : ℤ) < y₁)
    (houter : y = -(n : ℤ) ∨ x = -(n : ℤ)) :
    bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![x, y] := by
  have hu := bcor_corridors_two_right_upper n hn (-y₂) (-y₁) x (-y)
    (by simpa using hy₂) (by simpa using hy₁) hx (by simpa using hy)
    (by omega) (by omega) (by rcases houter with h | h <;> simp [h])
  simpa using bcor_corridors_swap12 (bcor_corridors_refl hu)









theorem bcor_corridors_same_right (n : ℕ) (hn : 1 ≤ n) (y₁ y₂ y₃ : ℤ)
    (hy₁ : y₁.natAbs ≤ n) (hy₂ : y₂.natAbs ≤ n) (hy₃ : y₃.natAbs ≤ n)
    (h12 : y₁ < y₂) (h23 : y₂ < y₃) :
    bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![(n : ℤ), y₃] := by
  set W₁ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), y₁] :=
    ((sw_vertSeg 0 0 (-(n : ℤ))).append (sw_horizSeg (-(n : ℤ)) 0 (n : ℤ))).append
      (sw_vertSeg (n : ℤ) (-(n : ℤ)) y₁) with hW1
  set W₂ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), y₂] :=
    ((sw_horizSeg 0 0 1).append (sw_vertSeg 1 0 y₂)).append
      (sw_horizSeg y₂ 1 (n : ℤ)) with hW2
  set W₃ : (hypercubicLattice 2).Walk ![0, 0] ![(n : ℤ), y₃] :=
    ((sw_vertSeg 0 0 (n : ℤ)).append (sw_horizSeg (n : ℤ) 0 (n : ℤ))).append
      (sw_vertSeg (n : ℤ) (n : ℤ) y₃) with hW3
  have hW1supp : ∀ z : Site 2, z ∈ W₁.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 (-(n : ℤ)) ∧ z = ![0, a]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![a, (-(n : ℤ))])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc (-(n : ℤ)) y₁ ∧ z = ![(n : ℤ), a]) := by
    intro z
    rw [hW1, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_vertSeg_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]
  have hW2supp : ∀ z : Site 2, z ∈ W₂.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 1 ∧ z = ![a, 0]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 y₂ ∧ z = ![1, a])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc 1 (n : ℤ) ∧ z = ![a, y₂]) := by
    intro z
    rw [hW2, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_horizSeg_mem_support, sw_vertSeg_mem_support, sw_horizSeg_mem_support]
  have hW3supp : ∀ z : Site 2, z ∈ W₃.support ↔
      ((∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![0, a]) ∨
       (∃ a : ℤ, a ∈ Set.uIcc 0 (n : ℤ) ∧ z = ![a, (n : ℤ)])) ∨
      (∃ a : ℤ, a ∈ Set.uIcc (n : ℤ) y₃ ∧ z = ![(n : ℤ), a]) := by
    intro z
    rw [hW3, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      sw_vertSeg_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]
  refine ⟨W₁.bypass, W₂.bypass, W₃.bypass, W₁.bypass_isPath, W₂.bypass_isPath,
    W₃.bypass_isPath, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (hW1supp z).mp (W₁.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs (by simp) ha)
    · exact bcor_mem_box (bcor_uIcc_natAbs (by simp) ha) (by simp)
    · rw [Set.mem_uIcc] at ha
      apply bcor_mem_box (by simp)
      omega
  · intro z hz
    rcases (hW2supp z).mp (W₂.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · apply bcor_mem_box
      · rw [Set.mem_uIcc] at ha
        omega
      · simp
    · exact bcor_mem_box (by omega) (bcor_uIcc_natAbs hy₂ ha)
    · rw [Set.mem_uIcc] at ha
      apply bcor_mem_box ?_ hy₂
      omega
  · intro z hz
    rcases (hW3supp z).mp (W₃.support_bypass_subset hz) with
      (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
    · exact bcor_mem_box (by simp) (bcor_uIcc_natAbs (by simp) ha)
    · exact bcor_mem_box (bcor_uIcc_natAbs (by simp) ha) (by simp)
    · rw [Set.mem_uIcc] at ha
      apply bcor_mem_box (by simp)
      omega
  · intro z h1 h2
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    rcases h1' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h2' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · intro z h1 h3
    have h1' := (hW1supp z).mp (W₁.support_bypass_subset h1)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h1' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h3' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · intro z h2 h3
    have h2' := (hW2supp z).mp (W₂.support_bypass_subset h2)
    have h3' := (hW3supp z).mp (W₃.support_bypass_subset h3)
    rcases h2' with (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩ <;>
      rcases h3' with (⟨b, hb, hz⟩ | ⟨b, hb, hz⟩) | ⟨b, hb, hz⟩ <;>
      have e0 := congrFun hz 0 <;> have e1 := congrFun hz 1 <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 <;>
      rw [Set.mem_uIcc] at ha hb <;>
      rw [bcor_origin_eq] <;>
      ext i <;> fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega




theorem bcor_corridors_same_right_of_distinct (n : ℕ) (hn : 1 ≤ n) (y₁ y₂ y₃ : ℤ)
    (hy₁ : y₁.natAbs ≤ n) (hy₂ : y₂.natAbs ≤ n) (hy₃ : y₃.natAbs ≤ n)
    (hne12 : y₁ ≠ y₂) (hne13 : y₁ ≠ y₃) (hne23 : y₂ ≠ y₃) :
    bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![(n : ℤ), y₃] := by
  rcases lt_or_gt_of_ne hne12 with h12 | h21
  · rcases lt_or_gt_of_ne hne23 with h23 | h32
    · exact bcor_corridors_same_right n hn y₁ y₂ y₃ hy₁ hy₂ hy₃ h12 h23
    · rcases lt_or_gt_of_ne hne13 with h13 | h31
      · exact bcor_corridors_swap23
          (bcor_corridors_same_right n hn y₁ y₃ y₂ hy₁ hy₃ hy₂ h13 h32)
      · exact bcor_corridors_swap23 (bcor_corridors_swap12
          (bcor_corridors_same_right n hn y₃ y₁ y₂ hy₃ hy₁ hy₂ h31 h12))
  · rcases lt_or_gt_of_ne hne13 with h13 | h31
    · exact bcor_corridors_swap12
        (bcor_corridors_same_right n hn y₂ y₁ y₃ hy₂ hy₁ hy₃ h21 h13)
    · rcases lt_or_gt_of_ne hne23 with h23 | h32
      · exact bcor_corridors_swap12 (bcor_corridors_swap23
          (bcor_corridors_same_right n hn y₂ y₃ y₁ hy₂ hy₃ hy₁ h23 h31))
      · exact bcor_corridors_swap12 (bcor_corridors_swap23 (bcor_corridors_swap12
          (bcor_corridors_same_right n hn y₃ y₂ y₁ hy₃ hy₂ hy₁ h32 h21)))











theorem bcor_firstSteps (n : ℕ) {u₁ u₂ u₃ : Site 2}
    (hu₁ : u₁ ≠ ![0, 0]) (hu₂ : u₂ ≠ ![0, 0]) (hu₃ : u₃ ≠ ![0, 0])
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    ∃ a₁ a₂ a₃ : Site 2,
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) := by
  obtain ⟨P₁, P₂, P₃, _, _, _, _, _, _, d12, d13, d23⟩ := hC
  
  have step : ∀ {u : Site 2} (P : (hypercubicLattice 2).Walk ![0, 0] u), u ≠ ![0, 0] →
      (hypercubicLattice 2).Adj ![0, 0] (P.getVert 1) ∧ P.getVert 1 ∈ P.support ∧
        P.getVert 1 ≠ ![0, 0] := by
    intro u P hu
    have hne : P.length ≠ 0 := by
      intro h; apply hu
      have hL := P.getVert_length; rw [h] at hL; exact hL.symm.trans P.getVert_zero
    have hlen : 0 < P.length := Nat.pos_of_ne_zero hne
    have hadj0 : (hypercubicLattice 2).Adj (P.getVert 0) (P.getVert (0 + 1)) :=
      P.adj_getVert_succ hlen
    rw [P.getVert_zero] at hadj0
    have hadj : (hypercubicLattice 2).Adj ![0, 0] (P.getVert 1) := hadj0
    exact ⟨hadj, P.getVert_mem_support 1, ((hypercubicLattice 2).ne_of_adj hadj).symm⟩
  obtain ⟨ha1, hm1, hn1⟩ := step P₁ hu₁
  obtain ⟨ha2, hm2, hn2⟩ := step P₂ hu₂
  obtain ⟨ha3, hm3, hn3⟩ := step P₃ hu₃
  have ha1' : (hypercubicLattice 2).Adj 0 (P₁.getVert 1) := by rw [← bcor_origin_eq]; exact ha1
  have ha2' : (hypercubicLattice 2).Adj 0 (P₂.getVert 1) := by rw [← bcor_origin_eq]; exact ha2
  have ha3' : (hypercubicLattice 2).Adj 0 (P₃.getVert 1) := by rw [← bcor_origin_eq]; exact ha3
  refine ⟨P₁.getVert 1, P₂.getVert 1, P₃.getVert 1, ⟨ha1', ha2', ha3'⟩, ?_, ?_, ?_⟩
  · intro h; exact hn1 (d12 _ hm1 (h ▸ hm2))
  · intro h; exact hn1 (d13 _ hm1 (h ▸ hm3))
  · intro h; exact hn2 (d23 _ hm2 (h ▸ hm3))









theorem bcor_witness :
    bcor_Corridors 3 ![(3 : ℤ), 1] ![(-2 : ℤ), (3 : ℤ)] ![(-3 : ℤ), -2] := by
  have h := bcor_corridors_RTL 3 (by norm_num) 1 (-2) (-2)
    (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by decide)
  simpa using h








theorem bcor_incident_corner_impossible (n : ℕ) (hn : 1 ≤ n) :
    ¬ bcor_Corridors n
      ![(n : ℤ), (n : ℤ) - 1]
      ![(n : ℤ), (n : ℤ)]
      ![(n : ℤ) - 1, (n : ℤ)] := by
  rintro ⟨P₁, P₂, P₃, _, _, _, _, hb2, _, hd12, _, hd23⟩
  have hend : P₂.getVert P₂.length = (![(n : ℤ), (n : ℤ)] : Site 2) :=
    P₂.getVert_length
  have hlen : 0 < P₂.length := by
    by_contra h
    have hz : P₂.length = 0 := Nat.eq_zero_of_not_pos h
    have hstart := P₂.getVert_zero
    rw [hz] at hend
    have heq : (![0, 0] : Site 2) = ![(n : ℤ), (n : ℤ)] := hstart.symm.trans hend
    have := congrFun heq 0
    simp only [Matrix.cons_val_zero] at this
    omega
  let v := P₂.getVert (P₂.length - 1)
  have hvadj : (hypercubicLattice 2).Adj v ![(n : ℤ), (n : ℤ)] := by
    have hlt : P₂.length - 1 < P₂.length := by omega
    have h := P₂.adj_getVert_succ hlt
    have hs : P₂.length - 1 + 1 = P₂.length := by omega
    rw [hs, hend] at h
    exact h
  have hvmem : v ∈ P₂.support := P₂.getVert_mem_support _
  have hvbox : v ∈ box 2 n := hb2 v hvmem
  have hv : v = (![(n : ℤ), (n : ℤ) - 1] : Site 2) ∨
      v = (![(n : ℤ) - 1, (n : ℤ)] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hvadj
    rw [mem_box] at hvbox
    have hb0 := hvbox 0
    have hb1 := hvbox 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvadj
    have hcoord : (v 0 = (n : ℤ) ∧ v 1 = (n : ℤ) - 1) ∨
        (v 0 = (n : ℤ) - 1 ∧ v 1 = (n : ℤ)) := by
      omega
    rcases hcoord with h | h
    · left
      ext i
      fin_cases i <;> simp [h.1, h.2]
    · right
      ext i
      fin_cases i <;> simp [h.1, h.2]
  rcases hv with hv | hv
  · have ht : (![(n : ℤ), (n : ℤ) - 1] : Site 2) ∈ P₁.support := by
      simp
    have ho := hd12 _ ht (hv ▸ hvmem)
    have := congrFun ho 0
    norm_num [Matrix.cons_val_zero] at this
    omega
  · have ht : (![(n : ℤ) - 1, (n : ℤ)] : Site 2) ∈ P₃.support := by
      simp
    have ho := hd23 _ (hv ▸ hvmem) ht
    have := congrFun ho 1
    norm_num [Matrix.cons_val_one] at this
    omega


theorem bcor_witness_firstSteps :
    ∃ a₁ a₂ a₃ : Site 2,
      ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
        (hypercubicLattice 2).Adj 0 a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) :=
  bcor_firstSteps 3 (by decide) (by decide) (by decide) bcor_witness

end StatMech.Walls
