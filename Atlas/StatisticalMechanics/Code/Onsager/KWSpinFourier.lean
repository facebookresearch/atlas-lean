/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWDetLimit

namespace StatMech.Onsager



noncomputable def ons_dirPhase (u v : ℂ) (mu : Fin 4) : ℂ :=
  match mu with
  | 0 => u
  | 1 => v
  | 2 => u⁻¹
  | 3 => v⁻¹

def ons_dirExponentX (mu : Fin 4) : ℤ :=
  match mu with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | 3 => 0

def ons_dirExponentY (mu : Fin 4) : ℤ :=
  match mu with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => -1

theorem ons_dirPhase_eq_zpow (u v : ℂ) (mu : Fin 4) :
    ons_dirPhase u v mu =
      u ^ ons_dirExponentX mu * v ^ ons_dirExponentY mu := by
  fin_cases mu <;> simp [ons_dirPhase, ons_dirExponentX, ons_dirExponentY]

private theorem prod_same_zpow {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (u : ℂ) (hu : u ≠ 0) (f : alpha → ℤ) :
    (∏ i ∈ s, u ^ f i) = u ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      exact (zpow_add₀ hu _ _).symm

theorem prod_ons_dirPhase {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (d : alpha → Fin 4) :
    (∏ i, ons_dirPhase u v (d i)) =
      u ^ (∑ i, ons_dirExponentX (d i)) *
        v ^ (∑ i, ons_dirExponentY (d i)) := by
  rw [← prod_same_zpow Finset.univ u hu (fun i => ons_dirExponentX (d i)),
    ← prod_same_zpow Finset.univ v hv (fun i => ons_dirExponentY (d i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact ons_dirPhase_eq_zpow u v (d i)


noncomputable def ons_KWmatPhase (L : ℕ) (x omega u v : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 => ons_dirPhase u v d1.2 * ons_KWmat L x omega d2 d1

noncomputable def ons_KWblockPhase (L : ℕ) (x omega u v : ℂ)
    (g : ZMod L × ZMod L) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun a b => ons_KWmatPhase L x omega u v (g, a) (0, b)

theorem ons_KWmatPhase_translation_invariant (L : ℕ) (x omega u v : ℂ)
    (t : ZMod L × ZMod L) (d1 d2 : ons_Dart L) :
    ons_KWmatPhase L x omega u v (ons_shiftDart L t d2) (ons_shiftDart L t d1) =
      ons_KWmatPhase L x omega u v d2 d1 := by
  unfold ons_KWmatPhase
  rw [ons_KWmat_translation_invariant]
  rfl

theorem ons_KWmatPhase_eq_blockCirc (L : ℕ) (x omega u v : ℂ) :
    ons_KWmatPhase L x omega u v =
      ons_blockCirculant2D L 4 (ons_KWblockPhase L x omega u v) := by
  ext p q
  show ons_KWmatPhase L x omega u v p q =
    ons_KWmatPhase L x omega u v
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) ((0 : ZMod L × ZMod L), q.2)
  have h := ons_KWmatPhase_translation_invariant L x omega u v q.1
    ((0 : ZMod L × ZMod L), q.2)
    ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2)
  simpa [ons_shiftDart] using h

theorem ons_KWblockPhaseSymbol_eq (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x omega u v root : ℂ) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 4 root
      (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
        ons_KWblockPhase L x omega u v g) j =
      ons_KWsymbolMat x omega (u * root ^ j.1.val) (v * root ^ j.2.val) := by
  have hLne : L ≠ 0 := NeZero.ne L
  have hrootne : root ≠ 0 := hroot.ne_zero hLne
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hLne
    rw [ZMod.val_neg_one]
  have hbase : root ^ ((-1 : ZMod L).val) = root⁻¹ := by
    have h1 : root ^ ((-1 : ZMod L).val) * root = 1 := by
      rw [← pow_succ, hval, hroot.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left h1).symm
  have hinv : ∀ m : ℕ, root ^ ((-1 : ZMod L).val * m) = (root ^ m)⁻¹ := by
    intro m
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hid : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        (if k = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) a b) =
      (if a = b then 1 else 0 : ℂ) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp [Matrix.one_apply]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hkw : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        ons_KWblockPhase L x omega u v k a b) =
      root ^ ((ons_dirStep L b 0).1.val * j.1.val +
        (ons_dirStep L b 0).2.val * j.2.val) *
        (ons_dirPhase u v b * (x * ons_turnW omega b a)) := by
    have hentry : ∀ k : ZMod L × ZMod L,
        ons_KWblockPhase L x omega u v k a b =
          if k = ons_dirStep L b 0 then
            ons_dirPhase u v b * (x * ons_turnW omega b a) else 0 := by
      intro k
      unfold ons_KWblockPhase ons_KWmatPhase ons_KWmat
      simp only [Prod.fst, Prod.snd]
      by_cases hk : k = ons_dirStep L b 0 <;> simp [hk] <;> ring
    simp only [hentry]
    rw [Finset.sum_eq_single (ons_dirStep L b 0)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  have homegane : omega ≠ 0 := by
    intro h
    rw [h] at homega
    simp at homega
    exact Complex.I_ne_zero homega.symm
  have hturn : omega⁻¹ = -Complex.I * omega := by
    have key : (-Complex.I * omega) * omega = 1 := by
      calc
        (-Complex.I * omega) * omega = -Complex.I * omega ^ 2 := by ring
        _ = 1 := by rw [homega, neg_mul, Complex.I_mul_I, neg_neg]
    exact inv_eq_of_mul_eq_one_left key
  fin_cases b <;>
    simp only [ons_dirStep, ons_dirPhase] <;>
    fin_cases a <;>
    simp only [ons_KWsymbolMat, ons_turnW, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val'] <;>
    simp_all [hinv, hturn, ZMod.val_one, one_mul, mul_one, mul_inv_rev] <;>
    field_simp <;> ring


theorem ons_KWmatPhase_det_eq_prod (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x omega u v root : ℂ) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 - ons_KWmatPhase L x omega u v).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) ^ 2 - x * (1 - x ^ 2) *
          (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹ +
            (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹))) := by
  have hblock : (1 - ons_KWmatPhase L x omega u v) =
      ons_blockCirculant2D L 4
        (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
          ons_KWblockPhase L x omega u v g) := by
    rw [ons_KWmatPhase_eq_blockCirc]
    ext p q
    simp only [Matrix.sub_apply]
    show (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) p q -
        ons_blockCirculant2D L 4 (ons_KWblockPhase L x omega u v) p q =
      ons_blockCirculant2D L 4
        (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
          ons_KWblockPhase L x omega u v g) p q
    unfold ons_blockCirculant2D
    simp only [Matrix.sub_apply]
    congr 1
    rw [Matrix.one_apply]
    by_cases hpq : p = q
    · subst p
      simp [Matrix.one_apply]
    · rw [if_neg hpq]
      by_cases hg : (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0
      · rw [if_pos hg, Matrix.one_apply]
        have hdir : p.2 ≠ q.2 := by
          intro hdir
          apply hpq
          apply Prod.ext
          · apply Prod.ext <;> dsimp only at hg ⊢
            · exact sub_eq_zero.mp (congrArg Prod.fst hg)
            · exact sub_eq_zero.mp (congrArg Prod.snd hg)
          · exact hdir
        rw [if_neg hdir]
      · rw [if_neg hg]
        simp
  rw [hblock, ons_det_blockCirculant2D L 4 root hroot]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_KWblockPhaseSymbol_eq L x omega u v root homega hroot hu hv j]
  rw [ons_symbol_det_z x omega _ _ homega
    (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))]
  ring


noncomputable def ons_spinPhase (L : ℕ) (a : Fin 2) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi * a.val / L : ℝ) : ℂ))

theorem ons_spinPhase_ne_zero (L : ℕ) (a : Fin 2) : ons_spinPhase L a ≠ 0 :=
  Complex.exp_ne_zero _

theorem ons_spinPhase_pow_side (L : ℕ) [NeZero L] (a : Fin 2) :
    ons_spinPhase L a ^ L = (-1 : ℂ) ^ a.val := by
  unfold ons_spinPhase
  rw [← Complex.exp_nat_mul]
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha with ha | ha
  · rw [ha]
    simp
  · rw [ha]
    norm_num only [Nat.cast_one, mul_one, one_mul]
    have harg : ((L : ℕ) : ℂ) *
        (Complex.I * (((Real.pi / L : ℝ)) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
      push_cast
      field_simp [hL]
    rw [harg, Complex.exp_pi_mul_I]

theorem ons_spinPhase_mul_spaceRoot_pow (L m : ℕ) (a : Fin 2) :
    ons_spinPhase L a * ons_spaceRoot L ^ m =
      Complex.exp (Complex.I * ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ)) := by
  rw [ons_spaceRoot_pow]
  unfold ons_spinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ons_spinPhase_spaceRoot_cos (L m : ℕ) (a : Fin 2) :
    ons_spinPhase L a * ons_spaceRoot L ^ m +
        (ons_spinPhase L a * ons_spaceRoot L ^ m)⁻¹ =
      2 * (Real.cos (2 * Real.pi * (m + (a.val : ℝ) / 2) / L) : ℂ) := by
  rw [ons_spinPhase_mul_spaceRoot_pow]
  have hinv :
      (Complex.exp (Complex.I *
        ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ)))⁻¹ =
      Complex.exp (-(Complex.I *
        ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ))) :=
    (Complex.exp_neg _).symm
  rw [hinv, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> ring


theorem prod_zmod_prod_eq_prod_range (L : ℕ) [NeZero L] (F : ℕ → ℕ → ℂ) :
    (∏ j : ZMod L × ZMod L, F j.1.val j.2.val) =
      ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  change (∏ j : Fin (q + 1) × Fin (q + 1), F j.1.val j.2.val) = _
  rw [Fintype.prod_prod_type]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  have hiL : i < q + 1 := Finset.mem_range.mp hi
  simp only [hiL, dite_true]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]



theorem ons_KWmatPhase_det_eq_spinDet (L : ℕ) [NeZero L] [Fact (1 < L)]
    (beta : ℝ) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
        (ons_spinDet L beta a b : ℂ) := by
  rw [ons_KWmatPhase_det_eq_prod L (Real.tanh beta : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  have hfactor : ∀ i j : ℕ,
      ((1 + (Real.tanh beta : ℂ) ^ 2) ^ 2 -
        (Real.tanh beta : ℂ) * (1 - (Real.tanh beta : ℂ) ^ 2) *
          (ons_spinPhase L a * ons_spaceRoot L ^ i +
            (ons_spinPhase L a * ons_spaceRoot L ^ i)⁻¹ +
            (ons_spinPhase L b * ons_spaceRoot L ^ j +
              (ons_spinPhase L b * ons_spaceRoot L ^ j)⁻¹))) =
        (ons_symbolDispersion beta
          (2 * Real.pi * (i + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * (j + (b.val : ℝ) / 2) / L) : ℂ) := by
    intro i j
    rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
    unfold ons_symbolDispersion
    norm_cast
    ring
  have hprod :
      (∏ j : ZMod L × ZMod L,
        ((1 + (Real.tanh beta : ℂ) ^ 2) ^ 2 -
          (Real.tanh beta : ℂ) * (1 - (Real.tanh beta : ℂ) ^ 2) *
            (ons_spinPhase L a * ons_spaceRoot L ^ j.1.val +
              (ons_spinPhase L a * ons_spaceRoot L ^ j.1.val)⁻¹ +
              (ons_spinPhase L b * ons_spaceRoot L ^ j.2.val +
                (ons_spinPhase L b * ons_spaceRoot L ^ j.2.val)⁻¹)))) =
      (∏ j : ZMod L × ZMod L,
        (ons_symbolDispersion beta
          (2 * Real.pi * (j.1.val + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : ℝ) / 2) / L) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hfactor j.1.val j.2.val
  rw [hprod]
  change (∏ z : ZMod L × ZMod L,
      (fun i j : ℕ =>
        (ons_symbolDispersion beta
          (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L) : ℂ))
        z.1.val z.2.val) = _
  let F : ℕ → ℕ → ℂ := fun i j =>
    (ons_symbolDispersion beta
      (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L)
      (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L) : ℂ)
  have hre : (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) =
      ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j :=
    prod_zmod_prod_eq_prod_range L F
  change (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) = _
  rw [hre]
  simp [F, ons_spinDet]

end StatMech.Onsager
