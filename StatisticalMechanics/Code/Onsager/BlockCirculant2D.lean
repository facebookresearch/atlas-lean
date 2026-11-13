/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.BlockCirculant















namespace StatMech.Onsager

open scoped Matrix Kronecker
open Matrix




def ons_blockCirculant2D (L d : ℕ) (v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ) :
    Matrix ((ZMod L × ZMod L) × Fin d) ((ZMod L × ZMod L) × Fin d) ℂ :=
  fun p q => v (p.1.1 - q.1.1, p.1.2 - q.1.2) p.2 q.2


noncomputable def ons_blockSymbol2D (L d : ℕ) [NeZero L] (ω : ℂ)
    (v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ) (j : ZMod L × ZMod L) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ k : ZMod L × ZMod L, ω ^ (k.1.val * j.1.val + k.2.val * j.2.val) • v k

theorem ons_det_blockCirculant2D (L d : ℕ) [NeZero L] (ω : ℂ) (hω : IsPrimitiveRoot ω L)
    (v : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ) :
    (ons_blockCirculant2D L d v).det = ∏ j : ZMod L × ZMod L, (ons_blockSymbol2D L d ω v j).det := by
  classical
  
  have hpm : ∀ x : ℕ, ω ^ (x % L) = ω ^ x := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x L]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
  
  set F1 : Matrix (ZMod L) (ZMod L) ℂ := fun i j => ω ^ (i.val * j.val) with hF1
  have hF1ij : ∀ i j : ZMod L, F1 i j = ω ^ (i.val * j.val) := fun _ _ => rfl
  
  have hinj : Function.Injective (fun a : Fin L => ω ^ (a.val)) := by
    intro a b h
    exact Fin.ext (hω.pow_inj a.isLt b.isLt h)
  set V : Matrix (Fin L) (Fin L) ℂ := Matrix.vandermonde (fun a : Fin L => ω ^ (a.val)) with hV
  have hdetV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hcard : Fintype.card (Fin L) = Fintype.card (ZMod L) := by
    rw [ZMod.card, Fintype.card_fin]
  have hfval : ∀ a : Fin L, ((a.val : ZMod L)).val = a.val := fun a => ZMod.val_natCast_of_lt a.isLt
  have hfinj : Function.Injective (fun a : Fin L => (a.val : ZMod L)) := by
    intro a b h
    apply Fin.ext
    have := congrArg ZMod.val h
    simpa [hfval] using this
  have hfbij : Function.Bijective (fun a : Fin L => (a.val : ZMod L)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hfinj, hcard⟩
  set e : Fin L ≃ ZMod L := Equiv.ofBijective _ hfbij with he
  have hesymm : ∀ i : ZMod L, (e.symm i).val = i.val := by
    intro i
    have h1 : ((e.symm i).val : ZMod L) = i := by
      change (fun a : Fin L => (a.val : ZMod L)) (e.symm i) = i
      change e (e.symm i) = i
      exact Equiv.apply_symm_apply e i
    calc (e.symm i).val = (((e.symm i).val : ZMod L)).val := (hfval _).symm
      _ = i.val := by rw [h1]
  have hF1eq : F1 = Matrix.reindex e e V := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hV, Matrix.vandermonde_apply, hF1ij,
      ← pow_mul, hesymm, hesymm]
  have hdetF1 : F1.det ≠ 0 := by
    rw [hF1eq, Matrix.det_reindex_self]; exact hdetV
  
  set expo : (ZMod L × ZMod L) → (ZMod L × ZMod L) → ℕ :=
    fun i j => i.1.val * j.1.val + i.2.val * j.2.val with hexpo
  
  set F2 : Matrix (ZMod L × ZMod L) (ZMod L × ZMod L) ℂ :=
    fun i j => ω ^ (expo i j) with hF2
  have hF2ij : ∀ i j : ZMod L × ZMod L, F2 i j = ω ^ (expo i j) := fun _ _ => rfl
  
  have hF2kron : F2 = F1 ⊗ₖ F1 := by
    ext i j
    rw [Matrix.kroneckerMap_apply, hF1ij, hF1ij, hF2ij, ← pow_add]
  have hdetF2 : F2.det ≠ 0 := by
    rw [hF2kron, Matrix.det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hdetF1) (pow_ne_zero _ hdetF1)
  
  set S : (ZMod L × ZMod L) → Matrix (Fin d) (Fin d) ℂ :=
    fun j => ons_blockSymbol2D L d ω v j with hS
  have hSapply : ∀ (i : ZMod L × ZMod L) (a c : Fin d),
      (S i) a c = ∑ k : ZMod L × ZMod L, ω ^ (expo k i) * (v k a c) := by
    intro i a c
    change (ons_blockSymbol2D L d ω v i) a c = _
    rw [ons_blockSymbol2D, Matrix.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Matrix.smul_apply, smul_eq_mul]
  set D : Matrix ((ZMod L × ZMod L) × Fin d) ((ZMod L × ZMod L) × Fin d) ℂ :=
    Matrix.of (fun p q => if p.1 = q.1 then S p.1 p.2 q.2 else 0) with hDdef
  have hDapply : ∀ (i : ZMod L × ZMod L) (a : Fin d) (l : ZMod L × ZMod L) (b : Fin d),
      D (i, a) (l, b) = if i = l then S i a b else 0 := fun _ _ _ _ => rfl
  
  set 𝓕 : Matrix ((ZMod L × ZMod L) × Fin d) ((ZMod L × ZMod L) × Fin d) ℂ :=
    F2 ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ) with h𝓕
  have h𝓕apply : ∀ (i : ZMod L × ZMod L) (a : Fin d) (l : ZMod L × ZMod L) (b : Fin d),
      𝓕 (i, a) (l, b) = ω ^ (expo i l) * (if a = b then 1 else 0) := by
    intro i a l b
    rw [h𝓕, Matrix.kroneckerMap_apply, hF2ij, Matrix.one_apply]
  
  have hdet𝓕 : 𝓕.det ≠ 0 := by
    rw [h𝓕, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
    exact pow_ne_zero _ hdetF2
  
  have hbc : ∀ (l : ZMod L × ZMod L) (b : Fin d) (j : ZMod L × ZMod L) (c : Fin d),
      ons_blockCirculant2D L d v (l, b) (j, c) = v (l - j) b c := fun _ _ _ _ => rfl
  
  have hL : ∀ (i : ZMod L × ZMod L) (a : Fin d) (j : ZMod L × ZMod L) (c : Fin d),
      (𝓕 * ons_blockCirculant2D L d v) (i, a) (j, c) = ω ^ (expo i j) * (S i) a c := by
    intro i a j c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner : ∀ l : ZMod L × ZMod L,
        (∑ b : Fin d, 𝓕 (i, a) (l, b) * ons_blockCirculant2D L d v (l, b) (j, c))
          = ω ^ (expo i l) * v (l - j) a c := by
      intro l
      have hb : ∀ b : Fin d,
          𝓕 (i, a) (l, b) * ons_blockCirculant2D L d v (l, b) (j, c)
            = (if a = b then ω ^ (expo i l) * v (l - j) b c else 0) := by
        intro b
        rw [h𝓕apply, hbc]
        by_cases h : a = b <;> simp [h]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_ite_eq]
      simp
    rw [Finset.sum_congr rfl (fun l _ => hinner l)]
    
    have hre : (∑ l : ZMod L × ZMod L, ω ^ (expo i l) * v (l - j) a c)
        = ∑ k : ZMod L × ZMod L, ω ^ (expo i (k + j)) * v k a c := by
      refine (Fintype.sum_equiv (Equiv.addRight j)
        (fun k : ZMod L × ZMod L => ω ^ (expo i (k + j)) * v k a c)
        (fun l : ZMod L × ZMod L => ω ^ (expo i l) * v (l - j) a c) ?_).symm
      intro k
      simp only [Equiv.coe_addRight]
      rw [add_sub_cancel_right]
    rw [hre]
    
    have hstep : ∀ k : ZMod L × ZMod L,
        ω ^ (expo i (k + j)) * v k a c
          = ω ^ (expo i j) * (ω ^ (expo k i) * v k a c) := by
      intro k
      have hcong : expo i (k + j) ≡ expo i k + expo i j [MOD L] := by
        simp only [hexpo]
        have h1 : (k + j).1.val ≡ k.1.val + j.1.val [MOD L] := by
          show (k.1 + j.1).val ≡ k.1.val + j.1.val [MOD L]
          rw [ZMod.val_add]; exact Nat.mod_modEq _ _
        have h2 : (k + j).2.val ≡ k.2.val + j.2.val [MOD L] := by
          show (k.2 + j.2).val ≡ k.2.val + j.2.val [MOD L]
          rw [ZMod.val_add]; exact Nat.mod_modEq _ _
        calc i.1.val * (k + j).1.val + i.2.val * (k + j).2.val
            ≡ i.1.val * (k.1.val + j.1.val) + i.2.val * (k.2.val + j.2.val) [MOD L] :=
              (h1.mul_left _).add (h2.mul_left _)
          _ = (i.1.val * k.1.val + i.2.val * k.2.val)
                + (i.1.val * j.1.val + i.2.val * j.2.val) := by ring
      have hpow : ω ^ (expo i (k + j)) = ω ^ (expo i k) * ω ^ (expo i j) := by
        rw [← hpm (expo i (k + j)),
          show expo i (k + j) % L = (expo i k + expo i j) % L from hcong,
          hpm (expo i k + expo i j), pow_add]
      rw [hpow, show expo i k = expo k i from by simp only [hexpo]; ring]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum]
    rw [show (∑ k : ZMod L × ZMod L, ω ^ (expo k i) * v k a c) = (S i) a c from (hSapply i a c).symm]
  have hR : ∀ (i : ZMod L × ZMod L) (a : Fin d) (j : ZMod L × ZMod L) (c : Fin d),
      (D * 𝓕) (i, a) (j, c) = ω ^ (expo i j) * (S i) a c := by
    intro i a j c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hinner : ∀ l : ZMod L × ZMod L,
        (∑ b : Fin d, D (i, a) (l, b) * 𝓕 (l, b) (j, c))
          = (if i = l then S i a c * ω ^ (expo l j) else 0) := by
      intro l
      have hb : ∀ b : Fin d,
          D (i, a) (l, b) * 𝓕 (l, b) (j, c)
            = (if b = c then (if i = l then S i a c else 0) * ω ^ (expo l j) else 0) := by
        intro b
        rw [hDapply, h𝓕apply]
        by_cases h : b = c <;> simp [h, mul_comm]
      rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_ite_eq']
      by_cases h : i = l <;> simp [h]
    rw [Finset.sum_congr rfl (fun l _ => hinner l), Finset.sum_ite_eq]
    simp [mul_comm]
  have hkey : 𝓕 * ons_blockCirculant2D L d v = D * 𝓕 := by
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, c⟩ := q
    rw [hL, hR]
  
  have hmul : 𝓕.det * (ons_blockCirculant2D L d v).det = D.det * 𝓕.det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hkey]
  have hcirc : (ons_blockCirculant2D L d v).det = D.det := by
    have h2 : (ons_blockCirculant2D L d v).det * 𝓕.det = D.det * 𝓕.det := by
      rw [mul_comm]; exact hmul
    exact mul_right_cancel₀ hdet𝓕 h2
  
  have hDreindex : D = Matrix.reindex (Equiv.prodComm (Fin d) (ZMod L × ZMod L))
      (Equiv.prodComm (Fin d) (ZMod L × ZMod L)) (Matrix.blockDiagonal S) := by
    ext p q
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, hDapply]
    simp [Equiv.prodComm]
  have hdetD : D.det = ∏ j : ZMod L × ZMod L, (S j).det := by
    rw [hDreindex, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  rw [hcirc, hdetD]

end StatMech.Onsager
