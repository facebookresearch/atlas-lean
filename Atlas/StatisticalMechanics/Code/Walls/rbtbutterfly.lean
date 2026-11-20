/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.WellFoundedSet

open Finset
open scoped BigOperators

namespace StatMech.Walls.Reimer

set_option linter.style.longLine false








abbrev rbt_Q (m : ℕ) : Type := Fin m → Bool







def rbt_e2 (c : Bool) : Bool → ℝ :=
  fun z => if c = false then (1 : ℝ) else (if z = false then 0 else 1)


def rbt_f2 (c : Bool) : Bool → ℝ :=
  fun z => if c = false then (if z = false then 1 else 0) else (if z = false then 1 else -1)


def rbt_g2 (c d : Bool) : Bool → ℝ :=
  fun z =>
    match c, d with
    | false, false => if z = false then 1 else 0     
    | false, true  => 1                              
    | true,  false => if z = false then 0 else 1     
    | true,  true  => if z = false then 1 else -1    






def rbt_inner2 (u v : Bool → ℝ) : ℝ := ∑ z : Bool, u z * v z

@[simp] lemma rbt_inner2_eq (u v : Bool → ℝ) :
    rbt_inner2 u v = u false * v false + u true * v true := by
  simp only [rbt_inner2, Fintype.sum_bool]; ring


lemma rbt_inner2_e_f (c : Bool) : rbt_inner2 (rbt_e2 c) (rbt_f2 (!c)) = 0 := by
  cases c <;> simp [rbt_e2, rbt_f2]



lemma rbt_inner2_e_g (c : Bool) : rbt_inner2 (rbt_e2 c) (rbt_g2 (!c) (!c)) = 0 := by
  cases c <;> simp [rbt_e2, rbt_g2]



lemma rbt_inner2_f_g (c : Bool) : rbt_inner2 (rbt_f2 c) (rbt_g2 (!c) c) = 0 := by
  cases c <;> simp [rbt_f2, rbt_g2]









def rbt_tens {m : ℕ} (v : Fin m → Bool → ℝ) : rbt_Q m → ℝ :=
  fun z => ∏ i, v i (z i)


def rbt_e {m : ℕ} (x : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_e2 (x i))


def rbt_f {m : ℕ} (x : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_f2 (x i))


def rbt_g {m : ℕ} (x y : rbt_Q m) : rbt_Q m → ℝ := rbt_tens (fun i => rbt_g2 (x i) (y i))




def rbt_inner {m : ℕ} (A B : rbt_Q m → ℝ) : ℝ := ∑ z : rbt_Q m, A z * B z



theorem rbt_tens_inner {m : ℕ} (u v : Fin m → Bool → ℝ) :
    rbt_inner (rbt_tens u) (rbt_tens v) = ∏ i, rbt_inner2 (u i) (v i) := by
  simp only [rbt_inner, rbt_tens, rbt_inner2]
  
  rw [Fintype.prod_sum (fun i (z : Bool) => u i z * v i z)]
  
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.prod_mul_distrib]








theorem rbt_e_perp_f {m : ℕ} (x y : rbt_Q m) (hxy : x ≠ y) :
    rbt_inner (rbt_e x) (rbt_f y) = 0 := by
  rw [rbt_e, rbt_f, rbt_tens_inner]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have : y i = !(x i) := by cases hxy' : x i <;> cases hyi : y i <;> simp_all
  rw [this]; exact rbt_inner2_e_f (x i)







def rbt_antipode {m : ℕ} (x : rbt_Q m) : rbt_Q m := fun i => !(x i)


def rbt_inCube {m : ℕ} (y z x : rbt_Q m) : Prop := ∀ i, x i = y i ∨ x i = z i


def rbt_inRed {m : ℕ} (y z x : rbt_Q m) : Prop := rbt_inCube y z x


def rbt_inYellow {m : ℕ} (y z x : rbt_Q m) : Prop := rbt_inCube y (rbt_antipode z) x




theorem rbt_e_perp_g {m : ℕ} (x y z : rbt_Q m) (hx : ¬ rbt_inRed y z x) :
    rbt_inner (rbt_e x) (rbt_g y z) = 0 := by
  rw [rbt_e, rbt_g, rbt_tens_inner]
  rw [rbt_inRed, rbt_inCube, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  push Not at hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hy : y i = !(x i) := by cases hxy : x i <;> cases hyi : y i <;> simp_all
  have hz : z i = !(x i) := by cases hxy : x i <;> cases hzi : z i <;> simp_all
  rw [hy, hz]; exact rbt_inner2_e_g (x i)




theorem rbt_f_perp_g {m : ℕ} (x y z : rbt_Q m) (hx : ¬ rbt_inYellow y z x) :
    rbt_inner (rbt_f x) (rbt_g y z) = 0 := by
  rw [rbt_f, rbt_g, rbt_tens_inner]
  rw [rbt_inYellow, rbt_inCube, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  push Not at hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hy : y i = !(x i) := by cases hxy : x i <;> cases hyi : y i <;> simp_all
  have hz : z i = x i := by
    have := hi.2
    simp only [rbt_antipode] at this
    cases hxy : x i <;> cases hzi : z i <;> simp_all
  rw [hy, hz]; exact rbt_inner2_f_g (x i)










open Classical in



theorem rbt_triangular_indep {ι : Type*} [Fintype ι] [PartialOrder ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hoff : ∀ x z, ¬ x ≤ z → M x z = 0) (hdiag : ∀ x, M x x ≠ 0) :
    LinearIndependent ℝ (fun x : ι => (fun z => M x z : ι → ℝ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  
  have hcz : ∀ z, ∑ x, c x * M x z = 0 := by
    intro z
    have := congrFun hc z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  
  intro z
  induction z using WellFoundedLT.induction with
  | _ z ih =>
    
    
    have hsum := hcz z
    have hkey : c z * M z z = 0 := by
      have : (∑ x, c x * M x z) = c z * M z z := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z)]
        have hzero : (∑ x ∈ Finset.univ.erase z, c x * M x z) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hxz : x ≠ z := (Finset.mem_erase.mp hx).1
          by_cases hle : x ≤ z
          · 
            have hlt : x < z := lt_of_le_of_ne hle hxz
            rw [ih x hlt, zero_mul]
          · rw [hoff x z hle, mul_zero]
        rw [hzero, zero_add]
      rw [← this]; exact hsum
    exact (mul_eq_zero.mp hkey).resolve_right (hdiag z)









lemma rbt_e2_eq_zeta (c c' : Bool) : rbt_e2 c c' = if c ≤ c' then 1 else 0 := by
  cases c <;> cases c' <;> simp [rbt_e2]

open Classical in

theorem rbt_e_apply {m : ℕ} (x z : rbt_Q m) :
    rbt_e x z = if x ≤ z then 1 else 0 := by
  simp only [rbt_e, rbt_tens, rbt_e2_eq_zeta]
  by_cases hxz : x ≤ z
  · rw [if_pos hxz]
    apply Finset.prod_eq_one
    intro i _
    rw [if_pos (hxz i)]
  · rw [if_neg hxz]
    rw [Pi.le_def, not_forall] at hxz
    obtain ⟨i, hi⟩ := hxz
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

open Classical in

lemma rbt_e_off {m : ℕ} (x z : rbt_Q m) (h : ¬ x ≤ z) : rbt_e x z = 0 := by
  rw [rbt_e_apply, if_neg h]

open Classical in

lemma rbt_e_diag {m : ℕ} (x : rbt_Q m) : rbt_e x x ≠ 0 := by
  rw [rbt_e_apply, if_pos le_rfl]; exact one_ne_zero



theorem rbt_e_indep (m : ℕ) : LinearIndependent ℝ (fun x : rbt_Q m => rbt_e x) :=
  rbt_triangular_indep (fun x z => rbt_e x z) (fun x z h => rbt_e_off x z h) rbt_e_diag


lemma rbt_f2_off (c c' : Bool) (h : ¬ c' ≤ c) : rbt_f2 c c' = 0 := by
  cases c <;> cases c' <;> simp_all [rbt_f2]


lemma rbt_f2_diag (c : Bool) : rbt_f2 c c ≠ 0 := by
  cases c <;> simp [rbt_f2]


lemma rbt_f_off {m : ℕ} (x z : rbt_Q m) (h : ¬ z ≤ x) : rbt_f x z = 0 := by
  simp only [rbt_f, rbt_tens]
  rw [Pi.le_def, not_forall] at h
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rbt_f2_off (x i) (z i) hi)


lemma rbt_f_diag {m : ℕ} (x : rbt_Q m) : rbt_f x x ≠ 0 := by
  simp only [rbt_f, rbt_tens]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => rbt_f2_diag (x i))



theorem rbt_f_indep (m : ℕ) : LinearIndependent ℝ (fun x : rbt_Q m => rbt_f x) := by
  
  have h := rbt_triangular_indep
    (ι := (rbt_Q m)ᵒᵈ)
    (M := fun x z => rbt_f (OrderDual.ofDual x) (OrderDual.ofDual z))
    (fun x z hxz => rbt_f_off _ _ (by
      
      simpa [OrderDual.toDual_le_toDual] using hxz))
    (fun x => rbt_f_diag _)
  
  exact h












open Classical in

noncomputable def rbt_Red {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) :=
  Finset.univ.filter (fun x => ∃ y ∈ T, rbt_inRed (body y) y x)

open Classical in

noncomputable def rbt_Yellow {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) :=
  Finset.univ.filter (fun x => ∃ y ∈ T, rbt_inYellow (body y) y x)























def rbt_G_indep : Prop :=
  ∀ (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)),
    LinearIndependent ℝ (fun y : T => rbt_g (body ↑y) ↑y)











open Classical in

noncomputable def rbt_Ybar {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) := Finset.univ \ rbt_Yellow body T

open Classical in

noncomputable def rbt_Rbar {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) := rbt_Yellow body T \ rbt_Red body T






def rbt_ButterflyLinIndep : Prop :=
  ∀ (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)),
    LinearIndependent ℝ
      (Sum.elim (fun y : T => rbt_g (body ↑y) ↑y)
        (Sum.elim (fun x : rbt_Ybar body T => rbt_f ↑x)
          (fun x : rbt_Rbar body T => rbt_e ↑x)))

open Classical in


theorem rbt_partition_card {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    2 ^ m = (rbt_Red body T ∩ rbt_Yellow body T).card
      + (rbt_Ybar body T).card + (rbt_Rbar body T).card := by
  classical
  have hcard : (Finset.univ : Finset (rbt_Q m)).card = 2 ^ m := by
    simp [Finset.card_univ, Fintype.card_fin]
  rw [← hcard, rbt_Ybar, rbt_Rbar]
  
  have hU : (Finset.univ \ rbt_Yellow body T).card + (rbt_Yellow body T).card
      = (Finset.univ : Finset (rbt_Q m)).card :=
    Finset.card_sdiff_add_card_inter Finset.univ (rbt_Yellow body T) ▸ by
      rw [Finset.univ_inter]
  have hY : (rbt_Yellow body T \ rbt_Red body T).card
      + (rbt_Red body T ∩ rbt_Yellow body T).card = (rbt_Yellow body T).card := by
    have := Finset.card_sdiff_add_card_inter (rbt_Yellow body T) (rbt_Red body T)
    rwa [Finset.inter_comm (rbt_Yellow body T) (rbt_Red body T)] at this
  
  rw [← hU, ← hY]; ring

end StatMech.Walls.Reimer
