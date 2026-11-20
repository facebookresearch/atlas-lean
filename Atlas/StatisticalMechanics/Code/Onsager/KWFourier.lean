/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWMatrix
import Code.Onsager.BlockCirculant2D
import Code.Onsager.SymbolDet

namespace StatMech.Onsager

noncomputable def ons_KWblock (L : ℕ) (x ωt : ℂ) (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun a b => ons_KWmat L x ωt (g, a) (0, b)

theorem ons_KWmat_eq_blockCirc (L : ℕ) (x ωt : ℂ) :
    ons_KWmat L x ωt = ons_blockCirculant2D L 4 (ons_KWblock L x ωt) := by
  ext p q
  show ons_KWmat L x ωt p q
    = ons_KWmat L x ωt ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) ((0 : ZMod L × ZMod L), q.2)
  have key := ons_KWmat_translation_invariant L x ωt q.1
    ((0 : ZMod L × ZMod L), q.2)
    ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2)
  
  have hshift2 : ons_shiftDart L q.1 ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) = p := by
    simp only [ons_shiftDart, sub_add_cancel, Prod.mk.eta]
  have hshift1 : ons_shiftDart L q.1 ((0 : ZMod L × ZMod L), q.2) = q := by
    simp only [ons_shiftDart, Prod.fst_zero, Prod.snd_zero, zero_add, Prod.mk.eta]
  rw [hshift2, hshift1] at key
  exact key

theorem ons_KWblockSymbol_eq (L : ℕ) [NeZero L] [Fact (1 < L)] (x ωt ωL : ℂ)
    (hωt : ωt^2 = Complex.I) (hωL : IsPrimitiveRoot ωL L) (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 4 ωL
      (fun g => (if g = 0 then (1:Matrix (Fin 4) (Fin 4) ℂ) else 0) - ons_KWblock L x ωt g) j
      = ons_KWsymbolMat x ωt (ωL ^ j.1.val) (ωL ^ j.2.val) := by
  have hLne : L ≠ 0 := NeZero.ne L
  have hωLne : ωL ≠ 0 := hωL.ne_zero hLne
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hLne
    rw [ZMod.val_neg_one]
  have hbase : ωL ^ ((-1:ZMod L).val) = ωL⁻¹ := by
    have h1 : ωL ^ ((-1:ZMod L).val) * ωL = 1 := by
      rw [← pow_succ, hval, hωL.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left h1).symm
  have hinv : ∀ m : ℕ, ωL^((-1:ZMod L).val * m) = (ωL^m)⁻¹ := by
    intro m
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  
  have hid : (∑ k : ZMod L × ZMod L,
      ωL ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        (if k = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) a b)
      = (if a = b then 1 else 0 : ℂ) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp only [if_pos rfl]
      have : ((0 : ZMod L × ZMod L).1.val * j.1.val + (0 : ZMod L × ZMod L).2.val * j.2.val) = 0 := by
        simp
      rw [this, pow_zero, one_mul]
      simp [Matrix.one_apply]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  
  have hkw : (∑ k : ZMod L × ZMod L,
      ωL ^ (k.1.val * j.1.val + k.2.val * j.2.val) * ons_KWblock L x ωt k a b)
      = ωL ^ ((ons_dirStep L b 0).1.val * j.1.val + (ons_dirStep L b 0).2.val * j.2.val)
          * (x * ons_turnW ωt b a) := by
    have hentry : ∀ k : ZMod L × ZMod L, ons_KWblock L x ωt k a b
        = if k = ons_dirStep L b 0 then x * ons_turnW ωt b a else 0 := by
      intro k
      unfold ons_KWblock ons_KWmat
      rfl
    simp only [hentry]
    rw [Finset.sum_eq_single (ons_dirStep L b 0)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  
  have hωtne : ωt ≠ 0 := by
    intro h
    rw [h] at hωt
    simp at hωt
    exact Complex.I_ne_zero hωt.symm
  have hturn : ωt⁻¹ = -Complex.I * ωt := by
    have key : (-Complex.I * ωt) * ωt = 1 := by
      have e1 : (-Complex.I * ωt) * ωt = -Complex.I * ωt^2 := by ring
      rw [e1, hωt, neg_mul, Complex.I_mul_I, neg_neg]
    exact inv_eq_of_mul_eq_one_left key
  fin_cases b <;>
    simp only [ons_dirStep] <;>
    fin_cases a <;>
    simp only [ons_KWsymbolMat, ons_turnW, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val'] <;>
    simp_all [hinv, hturn, ZMod.val_one, one_mul, mul_one] <;> ring

theorem ons_KWmat_det_eq_prod (L : ℕ) [NeZero L] [Fact (1 < L)] (x ωt ωL : ℂ)
    (hωt : ωt^2 = Complex.I) (hωL : IsPrimitiveRoot ωL L) :
    (1 - ons_KWmat L x ωt).det
      = ∏ j : ZMod L × ZMod L,
          ((1 + x^2)^2 - x*(1 - x^2)*((ωL^j.1.val) + (ωL^j.1.val)⁻¹
            + (ωL^j.2.val) + (ωL^j.2.val)⁻¹)) := by
  have hLne : L ≠ 0 := NeZero.ne L
  have hωLne : ωL ≠ 0 := hωL.ne_zero hLne
  have hblock : (1 - ons_KWmat L x ωt)
      = ons_blockCirculant2D L 4
          (fun g => (if g = 0 then (1:Matrix (Fin 4) (Fin 4) ℂ) else 0)
            - ons_KWblock L x ωt g) := by
    rw [ons_KWmat_eq_blockCirc]
    ext p q
    simp only [Matrix.sub_apply]
    show (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) p q
        - ons_blockCirculant2D L 4 (ons_KWblock L x ωt) p q
        = ons_blockCirculant2D L 4
            (fun g => (if g = 0 then (1:Matrix (Fin 4) (Fin 4) ℂ) else 0)
              - ons_KWblock L x ωt g) p q
    unfold ons_blockCirculant2D
    simp only [Matrix.sub_apply]
    congr 1
    
    rw [Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      simp [Matrix.one_apply]
    · rw [if_neg hpq]
      have hp1 : ¬ (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0 ∨ ¬ p.2 = q.2 := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        apply hpq
        have hpair : (p.1.1 - q.1.1, p.1.2 - q.1.2) = ((0:ZMod L), (0:ZMod L)) := h1
        rw [Prod.ext_iff] at hpair
        obtain ⟨ha, hb⟩ := hpair
        apply Prod.ext
        · apply Prod.ext
          · dsimp only
            rw [sub_eq_zero] at ha; exact ha
          · dsimp only
            rw [sub_eq_zero] at hb; exact hb
        · exact h2
      rcases hp1 with h | h
      · rw [if_neg h]; simp
      · by_cases hg : (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0
        · rw [if_pos hg, Matrix.one_apply, if_neg h]
        · rw [if_neg hg]; simp
  rw [hblock, ons_det_blockCirculant2D L 4 ωL hωL]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_KWblockSymbol_eq L x ωt ωL hωt hωL j]
  rw [ons_symbol_det_z x ωt (ωL^j.1.val) (ωL^j.2.val) hωt
    (pow_ne_zero _ hωLne) (pow_ne_zero _ hωLne)]

end StatMech.Onsager
