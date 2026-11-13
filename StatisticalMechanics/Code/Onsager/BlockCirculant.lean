/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib




















namespace StatMech.Onsager

open scoped Matrix Kronecker
open Matrix



def ons_blockCirculant (n d : ℕ) (v : ZMod n → Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((ZMod n) × Fin d) ((ZMod n) × Fin d) ℂ :=
  fun p q => v (p.1 - q.1) p.2 q.2


noncomputable def ons_blockSymbol (n d : ℕ) [NeZero n] (ω : ℂ)
    (v : ZMod n → Matrix (Fin d) (Fin d) ℂ)
    (j : ZMod n) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : ZMod n, ω ^ ((k.val) * (j.val)) • v k

theorem ons_det_blockCirculant (n d : ℕ) [NeZero n] (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (v : ZMod n → Matrix (Fin d) (Fin d) ℂ) :
    (ons_blockCirculant n d v).det = ∏ j : ZMod n, (ons_blockSymbol n d ω v j).det := by
  classical
  
  have hpm : ∀ x : ℕ, ω ^ (x % n) = ω ^ x := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x n]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
  
  set F : Matrix (ZMod n) (ZMod n) ℂ := fun i j => ω ^ (i.val * j.val) with hF
  have hFij : ∀ i j : ZMod n, F i j = ω ^ (i.val * j.val) := fun _ _ => rfl
  
  have hinj : Function.Injective (fun a : Fin n => ω ^ (a.val)) := by
    intro a b h
    exact Fin.ext (hω.pow_inj a.isLt b.isLt h)
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde (fun a : Fin n => ω ^ (a.val)) with hV
  have hdetV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  
  have hcard : Fintype.card (Fin n) = Fintype.card (ZMod n) := by
    rw [ZMod.card, Fintype.card_fin]
  have hfval : ∀ a : Fin n, ((a.val : ZMod n)).val = a.val := fun a => ZMod.val_natCast_of_lt a.isLt
  have hfinj : Function.Injective (fun a : Fin n => (a.val : ZMod n)) := by
    intro a b h
    apply Fin.ext
    have := congrArg ZMod.val h
    simpa [hfval] using this
  have hfbij : Function.Bijective (fun a : Fin n => (a.val : ZMod n)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hfinj, hcard⟩
  set e : Fin n ≃ ZMod n := Equiv.ofBijective _ hfbij with he
  have hesymm : ∀ i : ZMod n, (e.symm i).val = i.val := by
    intro i
    have h1 : ((e.symm i).val : ZMod n) = i := by
      change (fun a : Fin n => (a.val : ZMod n)) (e.symm i) = i
      change e (e.symm i) = i
      exact Equiv.apply_symm_apply e i
    calc (e.symm i).val = (((e.symm i).val : ZMod n)).val := (hfval _).symm
      _ = i.val := by rw [h1]
  
  have hFeq : F = Matrix.reindex e e V := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hV, Matrix.vandermonde_apply, hFij,
      ← pow_mul, hesymm, hesymm]
  have hdetF : F.det ≠ 0 := by
    rw [hFeq, Matrix.det_reindex_self]; exact hdetV
  
  set S : ZMod n → Matrix (Fin d) (Fin d) ℂ := fun j => ons_blockSymbol n d ω v j with hS
  have hSapply : ∀ (i : ZMod n) (a c : Fin d),
      (S i) a c = ∑ k : ZMod n, ω ^ (k.val * i.val) * (v k a c) := by
    intro i a c
    change (ons_blockSymbol n d ω v i) a c = _
    rw [ons_blockSymbol, Matrix.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Matrix.smul_apply, smul_eq_mul]
  set D : Matrix ((ZMod n) × Fin d) ((ZMod n) × Fin d) ℂ :=
    Matrix.of (fun p q => if p.1 = q.1 then S p.1 p.2 q.2 else 0) with hDdef
  have hDapply : ∀ (i : ZMod n) (a : Fin d) (l : ZMod n) (b : Fin d),
      D (i, a) (l, b) = if i = l then S i a b else 0 := fun _ _ _ _ => rfl
  
  set 𝓕 : Matrix ((ZMod n) × Fin d) ((ZMod n) × Fin d) ℂ :=
    F ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) with h𝓕
  have h𝓕apply : ∀ (i : ZMod n) (a : Fin d) (l : ZMod n) (b : Fin d),
      𝓕 (i, a) (l, b) = ω ^ (i.val * l.val) * (if a = b then 1 else 0) := by
    intro i a l b
    rw [h𝓕, Matrix.kroneckerMap_apply, hFij, Matrix.one_apply]
  
  have hdet𝓕 : 𝓕.det ≠ 0 := by
    rw [h𝓕, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
    exact pow_ne_zero _ hdetF
  
  have hL : ∀ (i : ZMod n) (a : Fin d) (j : ZMod n) (c : Fin d),
      (𝓕 * ons_blockCirculant n d v) (i, a) (j, c) = ω ^ (i.val * j.val) * (S i) a c := by
    intro i a j c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    
    have hinner : ∀ l : ZMod n,
        (∑ b : Fin d, 𝓕 (i, a) (l, b) * ons_blockCirculant n d v (l, b) (j, c))
          = ω ^ (i.val * l.val) * v (l - j) a c := by
      intro l
      have hb : ∀ b : Fin d,
          𝓕 (i, a) (l, b) * ons_blockCirculant n d v (l, b) (j, c)
            = (if a = b then ω ^ (i.val * l.val) * v (l - j) b c else 0) := by
        intro b
        rw [h𝓕apply, ons_blockCirculant]
        by_cases h : a = b <;> simp [h]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun l _ => hinner l)]
    
    have hre : (∑ l : ZMod n, ω ^ (i.val * l.val) * v (l - j) a c)
        = ∑ k : ZMod n, ω ^ (i.val * (k + j).val) * v k a c := by
      refine (Fintype.sum_equiv (Equiv.addRight j)
        (fun k : ZMod n => ω ^ (i.val * (k + j).val) * v k a c)
        (fun l : ZMod n => ω ^ (i.val * l.val) * v (l - j) a c) ?_).symm
      intro k
      simp only [Equiv.coe_addRight]
      rw [add_sub_cancel_right]
    rw [hre]
    
    have hstep : ∀ k : ZMod n,
        ω ^ (i.val * (k + j).val) * v k a c
          = ω ^ (i.val * j.val) * (ω ^ (k.val * i.val) * v k a c) := by
      intro k
      have hcong : i.val * (k + j).val ≡ i.val * (k.val + j.val) [MOD n] := by
        have : (k + j).val ≡ k.val + j.val [MOD n] := by
          rw [ZMod.val_add]; exact Nat.mod_modEq _ _
        exact this.mul_left _
      have hpow : ω ^ (i.val * (k + j).val) = ω ^ (i.val * k.val) * ω ^ (i.val * j.val) := by
        rw [← hpm (i.val * (k + j).val)]
        rw [show i.val * (k + j).val % n = i.val * (k.val + j.val) % n from hcong]
        rw [hpm (i.val * (k.val + j.val)), mul_add, pow_add]
      rw [hpow, mul_comm i.val k.val]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum]
    rw [show (∑ k : ZMod n, ω ^ (k.val * i.val) * v k a c) = (S i) a c from (hSapply i a c).symm]
  have hR : ∀ (i : ZMod n) (a : Fin d) (j : ZMod n) (c : Fin d),
      (D * 𝓕) (i, a) (j, c) = ω ^ (i.val * j.val) * (S i) a c := by
    intro i a j c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner : ∀ l : ZMod n,
        (∑ b : Fin d, D (i, a) (l, b) * 𝓕 (l, b) (j, c))
          = (if i = l then S i a c * ω ^ (l.val * j.val) else 0) := by
      intro l
      have hb : ∀ b : Fin d,
          D (i, a) (l, b) * 𝓕 (l, b) (j, c)
            = (if b = c then (if i = l then S i a c else 0) * ω ^ (l.val * j.val) else 0) := by
        intro b
        rw [hDapply, h𝓕apply]
        by_cases h : b = c <;> simp [h, mul_comm]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_ite_eq']
      by_cases h : i = l <;> simp [h]
    rw [Finset.sum_congr rfl (fun l _ => hinner l), Finset.sum_ite_eq]
    simp [mul_comm]
  have hkey : 𝓕 * ons_blockCirculant n d v = D * 𝓕 := by
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, c⟩ := q
    rw [hL, hR]
  
  have hmul : 𝓕.det * (ons_blockCirculant n d v).det = D.det * 𝓕.det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hkey]
  have hcirc : (ons_blockCirculant n d v).det = D.det := by
    have h2 : (ons_blockCirculant n d v).det * 𝓕.det = D.det * 𝓕.det := by
      rw [mul_comm]; exact hmul
    exact mul_right_cancel₀ hdet𝓕 h2
  
  have hDreindex : D = Matrix.reindex (Equiv.prodComm (Fin d) (ZMod n))
      (Equiv.prodComm (Fin d) (ZMod n)) (Matrix.blockDiagonal S) := by
    ext p q
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, hDapply]
    simp [Equiv.prodComm]
  have hdetD : D.det = ∏ j : ZMod n, (S j).det := by
    rw [hDreindex, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  rw [hcirc, hdetD]

end StatMech.Onsager
