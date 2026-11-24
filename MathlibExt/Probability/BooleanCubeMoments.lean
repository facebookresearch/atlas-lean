/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Analysis.Fourier.BooleanCubeInfluence
public import MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boolean cube moment bounds

Upper bound on the fourth moment of the sign sum over the Boolean cube,
the moment comparison algebra turning two Cauchy-Schwarz bounds into a
third-moment comparison, and the resulting lower bound on the first
moment of the absolute sign sum.
-/

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- Second moment of the sign sum over all sign sequences, as the
constant-coefficient specialization of the checked Rademacher second
moment (`sum_rademacher_sq_real` at `a = 1`). -/
private theorem sum_cubeVal_sq (T : ℕ) :
    ∑ σ : Fin T → Bool, (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2
      = (2 : ℝ) ^ T * (T : ℝ) := by
  have h := MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype.sum_rademacher_sq_real
    T fun _ => (1 : ℝ)
  have hLHS : (∑ ε : Fin T → Bool, (∑ i, (if ε i then (1 : ℝ) else -1)) ^ 2)
      = ∑ σ : Fin T → Bool, (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2 := by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    cases σ t <;> rfl
  have hRHS : (∑ _i : Fin T, (1 : ℝ) ^ 2) = (T : ℝ) := by simp
  rw [← hLHS, ← hRHS]
  exact h

/-- Fourth-moment upper bound for the sign sum; the `≤` form suffices for
`khintchine_lower`. Proof route: induction that splits off the head
coordinate; for each tail sign sum, the two head choices contribute the sum
of the fourth powers at the tail sum plus one and at the tail sum minus
one, the odd terms cancel leaving twice the fourth power plus twelve
times the square plus two, and the induction hypothesis combines with the
constant-coefficient specialization of the checked Rademacher second
moment. -/
theorem sum_cubeVal_fourth_le (T : ℕ) :
    ∑ σ : Fin T → Bool, (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4
      ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := by
  induction T with
  | zero =>
    show (∑ σ : Fin 0 → Bool, (∑ t : Fin 0, BooleanCube.cubeVal (σ t)) ^ 4)
      ≤ (2 : ℝ) ^ (0 : ℕ) * (3 * ((0 : ℕ) : ℝ) ^ 2)
    have hL : (∑ σ : Fin 0 → Bool,
        (∑ t : Fin 0, BooleanCube.cubeVal (σ t)) ^ 4) = 0 := by
      simp
    have hR : (2 : ℝ) ^ (0 : ℕ) * (3 * ((0 : ℕ) : ℝ) ^ 2) = 0 := by simp
    rw [hL, hR]
  | succ n ih =>
    show (∑ σ : Fin (n + 1) → Bool,
          (∑ t : Fin (n + 1), BooleanCube.cubeVal (σ t)) ^ 4)
      ≤ (2 : ℝ) ^ (n + 1) * (3 * ((n + 1 : ℕ) : ℝ) ^ 2)
    set E : (Fin n → Bool) → Bool → ℝ := fun σ' b =>
      (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) ^ 4
        + 4 * (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) ^ 3 *
          BooleanCube.cubeVal b
        + 6 * (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) ^ 2
        + 4 * (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) *
          BooleanCube.cubeVal b + 1 with hEdef
    have hreindex : (∑ σ : Fin (n + 1) → Bool,
          (∑ t : Fin (n + 1), BooleanCube.cubeVal (σ t)) ^ 4)
        = ∑ p : Bool × (Fin n → Bool),
          (∑ t : Fin (n + 1),
            BooleanCube.cubeVal (((Fin.consEquiv fun _ => Bool) p) t)) ^ 4 :=
      (Equiv.sum_comp (Fin.consEquiv fun _ => Bool)
        (fun σ => (∑ t : Fin (n + 1), BooleanCube.cubeVal (σ t)) ^ 4)).symm
    simp only [Fin.consEquiv_apply] at hreindex
    have hsplit : ∀ p : Bool × (Fin n → Bool),
        (∑ t : Fin (n + 1),
            BooleanCube.cubeVal (Fin.cons (α := fun _ => Bool) p.1 p.2 t))
          = BooleanCube.cubeVal p.1
            + ∑ i : Fin n, BooleanCube.cubeVal (p.2 i) := fun p => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hexpand : ∀ p : Bool × (Fin n → Bool),
        (∑ t : Fin (n + 1),
            BooleanCube.cubeVal (Fin.cons (α := fun _ => Bool) p.1 p.2 t)) ^ 4
          = E p.2 p.1 := fun p => by
      have hsq1 : BooleanCube.cubeVal p.1 ^ 2 = 1 := by
        rw [pow_two]; exact BooleanCube.cubeVal_mul_self _
      have hs3 : BooleanCube.cubeVal p.1 ^ 3 = BooleanCube.cubeVal p.1 := by
        rw [show BooleanCube.cubeVal p.1 ^ 3
          = BooleanCube.cubeVal p.1 ^ 2 * BooleanCube.cubeVal p.1 from by ring,
          hsq1, one_mul]
      have hs4 : BooleanCube.cubeVal p.1 ^ 4 = 1 := by
        rw [show BooleanCube.cubeVal p.1 ^ 4
          = (BooleanCube.cubeVal p.1 ^ 2) ^ 2 from by ring, hsq1,
          one_pow]
      rw [hsplit]
      simp only [hEdef]
      rw [show (BooleanCube.cubeVal p.1
          + ∑ i : Fin n, BooleanCube.cubeVal (p.2 i)) ^ 4
        = BooleanCube.cubeVal p.1 ^ 4 + 4 * BooleanCube.cubeVal p.1 ^ 3
            * (∑ i : Fin n, BooleanCube.cubeVal (p.2 i))
          + 6 * BooleanCube.cubeVal p.1 ^ 2
            * (∑ i : Fin n, BooleanCube.cubeVal (p.2 i)) ^ 2
          + 4 * BooleanCube.cubeVal p.1
            * (∑ i : Fin n, BooleanCube.cubeVal (p.2 i)) ^ 3
          + (∑ i : Fin n, BooleanCube.cubeVal (p.2 i)) ^ 4 from by ring]
      rw [hs4, hs3, hsq1]
      ring
    have hbool : ∀ σ' : Fin n → Bool, (∑ b : Bool, E σ' b)
        = 2 * (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) ^ 4
          + 12 * (∑ i : Fin n, BooleanCube.cubeVal (σ' i)) ^ 2 + 2 :=
      fun σ' => by
      simp only [hEdef]
      rw [Fintype.sum_bool]
      simp only [BooleanCube.cubeVal]
      ring
    have hprod : (∑ p : Bool × (Fin n → Bool), E p.2 p.1)
        = ∑ b : Bool, ∑ σ' : Fin n → Bool, E σ' b :=
      Fintype.sum_prod_type _
    have hcomm : (∑ b : Bool, ∑ σ' : Fin n → Bool, E σ' b)
        = ∑ σ' : Fin n → Bool, ∑ b : Bool, E σ' b :=
      Finset.sum_comm
    have hcard2 : (∑ _σ' : Fin n → Bool, (2 : ℝ)) = (2 : ℝ) ^ n * 2 := by
      rw [Finset.sum_const, Finset.card_univ,
        MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype.card_sign_vectors,
        nsmul_eq_mul]
      simp [Nat.cast_pow]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    have hN : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by linarith : (0:ℝ) ≤ 2) n
    rw [hreindex]
    simp only [hexpand]
    rw [hprod, hcomm]
    simp only [hbool]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hcard2, pow_succ, hcast]
    linarith [ih, sum_cubeVal_sq n, hN]

/-- Moment algebra: two Cauchy-Schwarz bounds combine to `B ^ 3 ≤ A ^ 2 * C`. -/
theorem moment_algebra (A B C M : ℝ) (hAnn : 0 ≤ A) (hBnn : 0 ≤ B)
    (hCnn : 0 ≤ C) (_hMnn : 0 ≤ M) (hB2 : B ^ 2 ≤ A * M)
    (hM2 : M ^ 2 ≤ B * C) : B ^ 3 ≤ A ^ 2 * C := by
  have hBMC : (B * M) ^ 2 ≤ (A * C) * (B * M) := by
    have z1 : 0 ≤ B ^ 2 * (B * C - M ^ 2) :=
      mul_nonneg (sq_nonneg _) (by linarith [hM2])
    have z2 : 0 ≤ (B * C) * (A * M - B ^ 2) :=
      mul_nonneg (mul_nonneg hBnn hCnn) (by linarith [hB2])
    linarith [z1, z2]
  have hBM : B * M ≤ A * C := by
    nlinarith [hBMC, mul_nonneg hBnn _hMnn, mul_nonneg hAnn hCnn]
  have z1 : B * (B ^ 2 - A * M) ≤ 0 := by
    have h' : 0 ≤ B * (A * M - B ^ 2) :=
      mul_nonneg hBnn (by linarith [hB2])
    linarith [h']
  have z2 : A * (B * M - A * C) ≤ 0 := by
    have h' : 0 ≤ A * (A * C - B * M) :=
      mul_nonneg hAnn (by linarith [hBM])
    linarith [h']
  linarith [z1, z2]

/-- Khintchine-type lower bound: the mean absolute sign sum is at least
`√(T / 3)`. From the constant-coefficient specialization of the checked
Rademacher second moment and `sum_cubeVal_fourth_le` by
`Finset.sum_mul_sq_le_sq_mul_sq` applied twice, giving
`(∑ S ^ 2) ^ 3 ≤ (∑ |S|) ^ 2 * ∑ S ^ 4`. -/
theorem khintchine_lower (T : ℕ) :
    ∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
      ≥ (2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3) := by
  by_cases hT0 : T = 0
  · subst hT0
    show (∑ σ : Fin 0 → Bool, |∑ t : Fin 0, BooleanCube.cubeVal (σ t)|)
      ≥ (2 : ℝ) ^ (0 : ℕ) * Real.sqrt (((0 : ℕ) : ℝ) / 3)
    have hL : (∑ σ : Fin 0 → Bool,
        |∑ t : Fin 0, BooleanCube.cubeVal (σ t)|) = 0 := by
      simp
    have hR : (2 : ℝ) ^ (0 : ℕ) * Real.sqrt (((0 : ℕ) : ℝ) / 3) = 0 := by
      simp
    rw [hL, hR]
  · have hTpos : 0 < T := by omega
    have hB : (∑ σ : Fin T → Bool,
          (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2)
        = (2 : ℝ) ^ T * (T : ℝ) := sum_cubeVal_sq T
    have hC : (∑ σ : Fin T → Bool,
          (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4)
        ≤ (2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2) := sum_cubeVal_fourth_le T
    have hAnn : 0 ≤ ∑ σ : Fin T → Bool,
        |∑ t : Fin T, BooleanCube.cubeVal (σ t)| :=
      Finset.sum_nonneg (fun σ _ => abs_nonneg _)
    have hBnn : 0 ≤ ∑ σ : Fin T → Bool,
        (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2 :=
      Finset.sum_nonneg (fun σ _ => sq_nonneg _)
    have hCnn : 0 ≤ ∑ σ : Fin T → Bool,
        (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4 :=
      Finset.sum_nonneg (fun σ _ => by
        have h4 : (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4
            = ((∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) ^ 2 := by ring
        rw [h4]
        exact sq_nonneg _)
    have hMnn : 0 ≤ ∑ σ : Fin T → Bool,
        |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3 :=
      Finset.sum_nonneg (fun σ _ => by
        have h3 : |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3
            = |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2
              * |∑ t : Fin T, BooleanCube.cubeVal (σ t)| := by
          ring
        rw [h3]
        exact mul_nonneg (sq_nonneg _) (abs_nonneg _))
    have hCS1 : ((∑ σ : Fin T → Bool,
          |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
            * |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2)) ^ 2
        ≤ (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2) *
          (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hM2 : ((∑ σ : Fin T → Bool,
          |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3)) ^ 2
        ≤ (∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) *
          (∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4) := by
      have eL : (∑ σ : Fin T → Bool,
            |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
              * |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2)
          = ∑ σ : Fin T → Bool,
            |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3 :=
        Finset.sum_congr rfl (fun σ _ => by ring)
      have eR1 : (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2 :=
        Finset.sum_congr rfl (fun σ _ => sq_abs _)
      have eR2 : (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2) ^ 2)
          = ∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4 :=
        Finset.sum_congr rfl (fun σ _ => by rw [sq_abs]; ring)
      rw [eL, eR1, eR2] at hCS1
      exact hCS1
    have hCS2 : ((∑ σ : Fin T → Bool,
          Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
          * (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
            * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|))) ^ 2
        ≤ (∑ σ : Fin T → Bool,
            (Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2) *
          (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
              * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hB2 : ((∑ σ : Fin T → Bool,
          (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2)) ^ 2
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) *
          (∑ σ : Fin T → Bool,
            |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3) := by
      have eL : (∑ σ : Fin T → Bool,
            Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
            * (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
              * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|))
          = ∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2 := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        have hsq : (Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2
            = |∑ t : Fin T, BooleanCube.cubeVal (σ t)| :=
          Real.sq_sqrt (abs_nonneg _)
        have hss : Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
              * (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
                * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|)
              = |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 2 := by
          have e : Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
                * (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
                  * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|)
                = |∑ t : Fin T, BooleanCube.cubeVal (σ t)|
                  * (Real.sqrt |∑ t : Fin T,
                    BooleanCube.cubeVal (σ t)|) ^ 2 := by ring
          rw [e, hsq]
          ring
        rw [hss]
        exact sq_abs _
      have eR1 : (∑ σ : Fin T → Bool,
            (Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)| :=
        Finset.sum_congr rfl (fun σ _ => Real.sq_sqrt (abs_nonneg _))
      have eR2 : (∑ σ : Fin T → Bool,
            (|∑ t : Fin T, BooleanCube.cubeVal (σ t)|
              * Real.sqrt |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2)
          = ∑ σ : Fin T → Bool,
            |∑ t : Fin T, BooleanCube.cubeVal (σ t)| ^ 3 := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
        ring
      rw [eL, eR1, eR2] at hCS2
      exact hCS2
    have hB3 : (∑ σ : Fin T → Bool,
          (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) ^ 3
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2
          * (∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4) :=
      moment_algebra _ _ _ _ hAnn hBnn hCnn hMnn hB2 hM2
    have hST : (∑ t : Fin T,
        BooleanCube.cubeVal ((fun _ => true) t)) = (T : ℝ) := by
      simp only [BooleanCube.cubeVal, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hCpos : 0 < ∑ σ : Fin T → Bool,
        (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4 := by
      have hterm : ∀ σ : Fin T → Bool,
          0 ≤ (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4 := fun σ => by
        have h4 : (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4
            = ((∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) ^ 2 := by ring
        rw [h4]
        exact sq_nonneg _
      have hle := Finset.single_le_sum (fun σ _ => hterm σ)
        (Finset.mem_univ (fun _ => true))
      rw [hST] at hle
      have hT4 : 0 < (T : ℝ) ^ 4 := pow_pos (Nat.cast_pos.mpr hTpos) 4
      linarith [hle, hT4]
    have hTposR : 0 < (T : ℝ) := Nat.cast_pos.mpr hTpos
    have hA2 : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
        ≤ (∑ σ : Fin T → Bool, |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2 := by
      have h3 : (∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) ^ 3
          / (∑ σ : Fin T → Bool,
            (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4)
          ≤ (∑ σ : Fin T → Bool,
            |∑ t : Fin T, BooleanCube.cubeVal (σ t)|) ^ 2 := by
        rw [div_le_iff₀ hCpos]
        linarith [hB3]
      have h4 : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
          ≤ (∑ σ : Fin T → Bool,
              (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 2) ^ 3
            / (∑ σ : Fin T → Bool,
              (∑ t : Fin T, BooleanCube.cubeVal (σ t)) ^ 4) := by
        rw [hB, mul_pow, le_div_iff₀ hCpos]
        have ha0 : 0 ≤ ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3) :=
          mul_nonneg (sq_nonneg _)
            (div_nonneg (le_of_lt hTposR) (by linarith : (0:ℝ) ≤ 3))
        have hmul := mul_le_mul_of_nonneg_left hC ha0
        have heq : ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3)
            * ((2 : ℝ) ^ T * (3 * (T : ℝ) ^ 2))
            = ((2 : ℝ) ^ T) ^ 3 * (T : ℝ) ^ 3 := by ring
        rw [heq] at hmul
        exact hmul
      exact h4.trans h3
    have hX2 : ((2 : ℝ) ^ T * Real.sqrt ((T : ℝ) / 3)) ^ 2
        = ((2 : ℝ) ^ T) ^ 2 * ((T : ℝ) / 3) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hTposR)
        (by linarith : (0:ℝ) ≤ 3))]
    rw [← hX2] at hA2
    exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hAnn hA2

end MetaMathlibExt
