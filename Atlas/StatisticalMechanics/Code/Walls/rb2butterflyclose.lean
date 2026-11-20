/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























import Code.Walls.rbtbutterfly
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Extension.Linear

open Finset
open scoped BigOperators

namespace StatMech.Walls.Reimer

set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1200000








theorem rb2_finrank_Q (m : ℕ) :
    Module.finrank ℝ (rbt_Q m → ℝ) = 2 ^ m := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [rbt_Q, Fintype.card_fin]














section rb2_part6
open Matrix
open Classical

def rb2_Cz (x y w : Bool) : ℤ :=
  match x, y, w with
  | false, false, false => 1
  | false, false, true  => 0
  | false, true,  false => 0
  | false, true,  true  => 1
  | true,  false, false => -1
  | true,  false, true  => 1
  | true,  true,  false => 2
  | true,  true,  true  => -1

def rb2_C (x y w : Bool) : ℝ := (rb2_Cz x y w : ℝ)

lemma rb2_g2_decomp (x y z : Bool) :
    rbt_g2 x y z = ∑ w : Bool, rb2_C x y w * rbt_g2 false w z := by
  simp only [rb2_C, rb2_Cz, Fintype.sum_bool]
  cases x <;> cases y <;> cases z <;> simp [rbt_g2] <;> norm_num

noncomputable def rb2_hbasis {m : ℕ} (z : rbt_Q m) : rbt_Q m → ℝ := rbt_g (fun _ => false) z

lemma rb2_g_decomp {m : ℕ} (x y : rbt_Q m) :
    rbt_g x y = ∑ z : rbt_Q m, (∏ i, rb2_C (x i) (y i) (z i)) • rb2_hbasis z := by
  funext w
  simp only [rb2_hbasis, rbt_g, rbt_tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hL : ∀ i, rbt_g2 (x i) (y i) (w i)
      = ∑ zi : Bool, rb2_C (x i) (y i) zi * rbt_g2 false zi (w i) := fun i => rb2_g2_decomp _ _ _
  rw [Finset.prod_congr rfl (fun i _ => hL i)]
  rw [Fintype.prod_sum (fun i (zi : Bool) => rb2_C (x i) (y i) zi * rbt_g2 false zi (w i))]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.prod_mul_distrib]



lemma rb2_hbasis_off {m : ℕ} (z w : rbt_Q m) (h : ¬ w ≤ z) : rb2_hbasis z w = 0 := by
  simp only [rb2_hbasis, rbt_g, rbt_tens]
  rw [Pi.le_def, not_forall] at h
  obtain ⟨i, hi⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  
  have : z i = false ∧ w i = true := by
    cases hz : z i <;> cases hw : w i <;> simp_all [Bool.le_iff_imp]
  rw [this.1, this.2]; simp [rbt_g2]

lemma rb2_hbasis_diag {m : ℕ} (z : rbt_Q m) : rb2_hbasis z z ≠ 0 := by
  simp only [rb2_hbasis, rbt_g, rbt_tens]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases hz : z i <;> simp [rbt_g2]

lemma rb2_hbasis_indep (m : ℕ) : LinearIndependent ℝ (fun z : rbt_Q m => rb2_hbasis z) := by
  have h := rbt_triangular_indep
    (ι := (rbt_Q m)ᵒᵈ)
    (M := fun z w => rb2_hbasis (OrderDual.ofDual z) (OrderDual.ofDual w))
    (fun z w hzw => rb2_hbasis_off _ _ (by simpa [OrderDual.toDual_le_toDual] using hzw))
    (fun z => rb2_hbasis_diag _)
  exact h




lemma rb2_Cz_off (x y w : Bool) (h : ¬ y ≤ w) : ((rb2_Cz x y w : ZMod 2)) = 0 := by
  
  have hyw : y = true ∧ w = false := by cases hy:y <;> cases hw:w <;> simp_all [Bool.le_iff_imp]
  obtain ⟨hy, hw⟩ := hyw; subst hy; subst hw
  cases x <;> decide

lemma rb2_Cz_diag (x y : Bool) : ((rb2_Cz x y y : ZMod 2)) = 1 := by
  cases x <;> cases y <;> decide




noncomputable def rb2_M2 {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Matrix T T (ZMod 2) :=
  fun y z => ∏ i, ((rb2_Cz (body (y : rbt_Q m) i) ((y : rbt_Q m) i) ((z : rbt_Q m) i) : ZMod 2))


noncomputable def rb2_blab {m : ℕ} (T : Finset (rbt_Q m)) : T → LinearExtension (rbt_Q m) :=
  fun y => toLinearExtension (y : rbt_Q m)

lemma rb2_blab_inj {m : ℕ} (T : Finset (rbt_Q m)) : Function.Injective (rb2_blab T) := by
  intro a b h
  exact Subtype.ext (show (a : rbt_Q m) = (b : rbt_Q m) from h)

lemma rb2_M2_blockTri {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_M2 body T).BlockTriangular (rb2_blab T) := by
  intro y z hlt
  simp only [rb2_M2]
  have hlt' : (toLinearExtension (z : rbt_Q m)) < (toLinearExtension (y : rbt_Q m)) := hlt
  have hnle : ¬ (y : rbt_Q m) ≤ (z : rbt_Q m) := by
    intro hle
    exact absurd (toLinearExtension.monotone hle) (not_le.mpr hlt')
  rw [Pi.le_def, not_forall] at hnle
  obtain ⟨i, hi⟩ := hnle
  exact Finset.prod_eq_zero (Finset.mem_univ i) (rb2_Cz_off _ _ _ hi)

lemma rb2_M2_det {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_M2 body T).det = 1 := by
  rw [(rb2_M2_blockTri body T).det]
  apply Finset.prod_eq_one
  intro a ha
  
  obtain ⟨y0, _, hy0⟩ := Finset.mem_image.mp ha
  haveI : Subsingleton {y // rb2_blab T y = a} := ⟨by
    rintro ⟨p, hp⟩ ⟨q, hq⟩
    exact Subtype.ext (rb2_blab_inj T (hp.trans hq.symm))⟩
  have hk : (⟨y0, hy0⟩ : {y // rb2_blab T y = a}) = (⟨y0, hy0⟩ : {y // rb2_blab T y = a}) := rfl
  rw [det_eq_elem_of_subsingleton _ (⟨y0, hy0⟩ : {y // rb2_blab T y = a})]
  simp only [toSquareBlock_def, rb2_M2, Matrix.of_apply]
  apply Finset.prod_eq_one
  intro i _
  exact rb2_Cz_diag _ _



noncomputable def rb2_Mz {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Matrix T T ℤ :=
  fun y z => ∏ i, rb2_Cz (body (y : rbt_Q m) i) ((y : rbt_Q m) i) ((z : rbt_Q m) i)

lemma rb2_Mz_det_ne_zero {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_Mz body T).det ≠ 0 := by
  intro h
  
  have hmap : rb2_M2 body T = (rb2_Mz body T).map (Int.castRingHom (ZMod 2)) := by
    funext y z
    simp only [rb2_M2, rb2_Mz, Matrix.map_apply, Int.coe_castRingHom, Int.cast_prod]
  have : (rb2_M2 body T).det = ((rb2_Mz body T).det : ZMod 2) := by
    have hd := RingHom.map_det (Int.castRingHom (ZMod 2)) (rb2_Mz body T)
    rw [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd]; rfl
  rw [rb2_M2_det] at this
  rw [h] at this
  simp at this


noncomputable def rb2_Mr {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Matrix T T ℝ :=
  fun y z => ∏ i, rb2_C (body (y : rbt_Q m) i) ((y : rbt_Q m) i) ((z : rbt_Q m) i)

lemma rb2_Mr_det_ne_zero {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    (rb2_Mr body T).det ≠ 0 := by
  have hmap : rb2_Mr body T = (rb2_Mz body T).map (Int.castRingHom ℝ) := by
    funext y z
    simp only [rb2_Mr, rb2_Mz, Matrix.map_apply, Int.coe_castRingHom, Int.cast_prod, rb2_C]
  have hdet : (rb2_Mr body T).det = ((rb2_Mz body T).det : ℝ) := by
    have hd := RingHom.map_det (Int.castRingHom ℝ) (rb2_Mz body T)
    rw [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd]; rfl
  rw [hdet]
  exact_mod_cast rb2_Mz_det_ne_zero body T



theorem rb2_g_indep {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    LinearIndependent ℝ (fun y : T => rbt_g (body (y : rbt_Q m)) (y : rbt_Q m)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  
  have hc2 : ∑ z : rbt_Q m, (∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z = 0 := by
    rw [← hc]
    
    have step1 : ∀ z : rbt_Q m,
        (∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z
        = ∑ y : T, (c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) • rb2_hbasis z := by
      intro z; rw [Finset.sum_smul]
    rw [Finset.sum_congr rfl (fun z _ => step1 z)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [rb2_g_decomp (body (y:rbt_Q m)) (y:rbt_Q m), Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [smul_smul]
  
  have hzero := (Fintype.linearIndependent_iff.mp (rb2_hbasis_indep m)
    (fun z => ∑ y : T, c y * (∏ i, rb2_C (body (y:rbt_Q m) i) ((y:rbt_Q m) i) (z i))) hc2)
  
  have hMrU : IsUnit (rb2_Mr body T) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (rb2_Mr_det_ne_zero body T)
  have hvec : (c ᵥ* (rb2_Mr body T)) = 0 := by
    funext z
    have := hzero (z : rbt_Q m)
    simp only [Matrix.vecMul, dotProduct, rb2_Mr, Pi.zero_apply]
    rw [← this]
  have : c = 0 := by
    have hinj := (Matrix.vecMul_injective_iff_isUnit).2 hMrU
    have : c ᵥ* (rb2_Mr body T) = (0 : T → ℝ) ᵥ* (rb2_Mr body T) := by rw [hvec]; simp
    exact hinj this
  intro y
  have := congrFun this y
  simpa using this

end rb2_part6










lemma rb2_inner_sum_right {m : ℕ} {ι : Type*} [Fintype ι]
    (A : rbt_Q m → ℝ) (c : ι → ℝ) (v : ι → (rbt_Q m → ℝ)) :
    rbt_inner A (∑ i, c i • v i) = ∑ i, c i * rbt_inner A (v i) := by
  simp only [rbt_inner]
  have : ∀ z, A z * (∑ i, c i • v i) z = ∑ i, c i * (A z * v i z) := by
    intro z
    rw [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  simp only [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]


lemma rb2_inner_sum_left {m : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → (rbt_Q m → ℝ)) (A : rbt_Q m → ℝ) :
    rbt_inner (∑ i, c i • v i) A = ∑ i, c i * rbt_inner (v i) A := by
  simp only [rbt_inner]
  have : ∀ z, (∑ i, c i • v i) z * A z = ∑ i, c i * (v i z * A z) := by
    intro z
    rw [Finset.sum_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    simp [Pi.smul_apply, smul_eq_mul]; ring
  simp only [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]


lemma rb2_inner_self_eq_zero {m : ℕ} (A : rbt_Q m → ℝ) :
    rbt_inner A A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext z
    by_contra hz
    have hpos : (0 : ℝ) < rbt_inner A A := by
      rw [rbt_inner]
      apply Finset.sum_pos'
      · intro i _; exact mul_self_nonneg _
      · exact ⟨z, Finset.mem_univ z, mul_self_pos.mpr hz⟩
    exact absurd h (ne_of_gt hpos)
  · intro h; simp [rbt_inner, h]




theorem rb2_orthUnion3 {m : ℕ} {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (A : α → (rbt_Q m → ℝ)) (B : β → (rbt_Q m → ℝ)) (C : γ → (rbt_Q m → ℝ))
    (hA : LinearIndependent ℝ A) (hB : LinearIndependent ℝ B) (hC : LinearIndependent ℝ C)
    (hAB : ∀ a b, rbt_inner (A a) (B b) = 0)
    (hAC : ∀ a c, rbt_inner (A a) (C c) = 0)
    (hBC : ∀ b c, rbt_inner (B b) (C c) = 0) :
    LinearIndependent ℝ (Sum.elim A (Sum.elim B C)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro d hd
  
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hd
  simp only [Sum.elim_inl, Sum.elim_inr] at hd
  set u := ∑ a, d (Sum.inl a) • A a with hu
  set v := ∑ b, d (Sum.inr (Sum.inl b)) • B b with hv
  set w := ∑ c, d (Sum.inr (Sum.inr c)) • C c with hw
  
  
  have huv : rbt_inner u v = 0 := by
    rw [hu, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro a _
    rw [hv, rb2_inner_sum_right]
    simp [hAB a]
  have huw : rbt_inner u w = 0 := by
    rw [hu, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro a _
    rw [hw, rb2_inner_sum_right]
    simp [hAC a]
  have hvw : rbt_inner v w = 0 := by
    rw [hv, rb2_inner_sum_left]
    apply Finset.sum_eq_zero; intro b _
    rw [hw, rb2_inner_sum_right]
    simp [hBC b]
  
  have hsymm : ∀ (P R : rbt_Q m → ℝ), rbt_inner P R = rbt_inner R P := by
    intro P R; simp only [rbt_inner]; apply Finset.sum_congr rfl; intro z _; ring
  
  have hdsum : u + v + w = 0 := by rw [add_assoc]; exact hd
  have huu : rbt_inner u u = 0 := by
    have : rbt_inner u (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner u (u + v + w) = rbt_inner u u + rbt_inner u v + rbt_inner u w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, huv, huw] at this; linarith
  have hvv : rbt_inner v v = 0 := by
    have : rbt_inner v (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner v (u + v + w) = rbt_inner v u + rbt_inner v v + rbt_inner v w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, hsymm v u, huv, hvw] at this; linarith
  have hww : rbt_inner w w = 0 := by
    have : rbt_inner w (u + v + w) = 0 := by rw [hdsum]; simp [rbt_inner]
    have hexp : rbt_inner w (u + v + w) = rbt_inner w u + rbt_inner w v + rbt_inner w w := by
      simp only [rbt_inner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro z _
      simp [Pi.add_apply]; ring
    rw [hexp, hsymm w u, huw, hsymm w v, hvw] at this; linarith
  have hu0 : u = 0 := (rb2_inner_self_eq_zero u).mp huu
  have hv0 : v = 0 := (rb2_inner_self_eq_zero v).mp hvv
  have hw0 : w = 0 := (rb2_inner_self_eq_zero w).mp hww
  
  rw [Fintype.linearIndependent_iff] at hA hB hC
  have hda := hA (fun a => d (Sum.inl a)) (by rw [← hu]; exact hu0)
  have hdb := hB (fun b => d (Sum.inr (Sum.inl b))) (by rw [← hv]; exact hv0)
  have hdc := hC (fun c => d (Sum.inr (Sum.inr c))) (by rw [← hw]; exact hw0)
  intro i
  cases i with
  | inl a => exact hda a
  | inr j => cases j with
    | inl b => exact hdb b
    | inr c => exact hdc c








open Classical in




theorem rb2_butterflyLinIndep_of_gIndep (hG : rbt_G_indep) : rbt_ButterflyLinIndep := by
  intro m body T
  
  have hfY : LinearIndependent ℝ (fun x : rbt_Ybar body T => rbt_f (m := m) ↑x) :=
    (rbt_f_indep m).comp (Subtype.val : rbt_Ybar body T → rbt_Q m) Subtype.coe_injective
  have heR : LinearIndependent ℝ (fun x : rbt_Rbar body T => rbt_e (m := m) ↑x) :=
    (rbt_e_indep m).comp (Subtype.val : rbt_Rbar body T → rbt_Q m) Subtype.coe_injective
  
  have hgT : LinearIndependent ℝ (fun y : T => rbt_g (body ↑y) ↑y) := hG m body T
  
  have hsymm : ∀ (P R : rbt_Q m → ℝ), rbt_inner P R = rbt_inner R P := by
    intro P R; simp only [rbt_inner]; apply Finset.sum_congr rfl; intro z _; ring
  apply rb2_orthUnion3 _ _ _ hgT hfY heR
  · 
    intro y x
    rw [hsymm]
    apply rbt_f_perp_g
    
    have hx : (↑x : rbt_Q m) ∉ rbt_Yellow body T := by
      have h2 := x.2; simp only [rbt_Ybar, Finset.mem_sdiff] at h2; exact h2.2
    intro hin
    apply hx
    simp only [rbt_Yellow, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨↑y, y.2, hin⟩⟩
  · 
    intro y x
    rw [hsymm]
    apply rbt_e_perp_g
    have hx : (↑x : rbt_Q m) ∉ rbt_Red body T := by
      have h2 := x.2; simp only [rbt_Rbar, Finset.mem_sdiff] at h2; exact h2.2
    intro hin
    apply hx
    simp only [rbt_Red, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨↑y, y.2, hin⟩⟩
  · 
    intro x x'
    rw [hsymm]
    apply rbt_e_perp_f
    
    have hx' : (↑x' : rbt_Q m) ∈ rbt_Yellow body T := by
      have h2 := x'.2; simp only [rbt_Rbar, Finset.mem_sdiff] at h2; exact h2.1
    have hx : (↑x : rbt_Q m) ∉ rbt_Yellow body T := by
      have h2 := x.2; simp only [rbt_Ybar, Finset.mem_sdiff] at h2; exact h2.2
    intro hcon
    apply hx; rw [← hcon]; exact hx'










theorem rb2_butterfly (hLI : rbt_ButterflyLinIndep) (m : ℕ)
    (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card := by
  classical
  
  have hcard := (hLI m body T).fintype_card_le_finrank
  rw [rb2_finrank_Q] at hcard
  
  rw [Fintype.card_sum, Fintype.card_sum] at hcard
  simp only [Fintype.card_coe] at hcard
  
  
  have hpart := rbt_partition_card body T
  omega









theorem rb2_G_indep : rbt_G_indep := fun _ body T => rb2_g_indep body T



theorem rb2_butterflyLinIndep : rbt_ButterflyLinIndep :=
  rb2_butterflyLinIndep_of_gIndep rb2_G_indep





theorem rb2_butterfly_thm (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card :=
  rb2_butterfly rb2_butterflyLinIndep m body T












end StatMech.Walls.Reimer
