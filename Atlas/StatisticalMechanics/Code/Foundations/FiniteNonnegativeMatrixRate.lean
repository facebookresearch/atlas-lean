/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Matrix Filter Topology
open scoped Matrix.Norms.Operator NNReal

namespace StatMech

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma norm_mulVec_one (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ‖A‖ = ‖A *ᵥ (fun _ => (1 : ℝ))‖ := by
  rw [Matrix.linfty_opNorm_def, Pi.norm_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i hi
  simp only [Matrix.mulVec, dotProduct, mul_one]
  rw [Real.nnnorm_of_nonneg (Finset.sum_nonneg fun j _ => hA i j)]
  apply NNReal.eq
  simp [Real.norm_eq_abs, abs_of_nonneg, hA]

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma pow_self_pos (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (n : ℕ) (i : α) :
    0 < (A ^ n) i i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_pos'
      · intro j hj
        exact mul_nonneg (Matrix.pow_apply_nonneg hA n i j) (hA j i)
      · exact ⟨i, Finset.mem_univ i, mul_pos ih (hdiag i)⟩

lemma pow_nonneg (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (n : ℕ) (i j : α) : 0 ≤ (A ^ n) i j :=
  Matrix.pow_apply_nonneg hA n i j

lemma norm_pow_pos (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (n : ℕ) : 0 < ‖A ^ n‖ := by
  rw [norm_pos_iff]
  intro hzero
  let i : α := Classical.choice inferInstance
  have := pow_self_pos A hA hdiag n i
  rw [hzero] at this
  simp at this

lemma log_norm_pow_subadditive (A : Matrix α α ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i) :
    Subadditive (fun n => Real.log ‖A ^ n‖) := by
  intro m n
  dsimp only
  rw [pow_add]
  calc
    Real.log ‖A ^ m * A ^ n‖ ≤ Real.log (‖A ^ m‖ * ‖A ^ n‖) :=
      Real.log_le_log (by
        rw [← pow_add]
        exact norm_pow_pos A hA hdiag (m + n))
        (Matrix.linfty_opNorm_mul (A ^ m) (A ^ n))
    _ = Real.log ‖A ^ m‖ + Real.log ‖A ^ n‖ :=
      Real.log_mul (norm_pow_pos A hA hdiag m).ne'
        (norm_pow_pos A hA hdiag n).ne'

lemma pow_self_ge_diag_pow (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (n : ℕ) (i : α) : (A i i) ^ n ≤ (A ^ n) i i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply]
      exact le_trans (mul_le_mul_of_nonneg_right ih (hA i i))
        (Finset.single_le_sum
          (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hA n i j) (hA j i))
          (Finset.mem_univ i))

lemma log_norm_pow_ratio_bddBelow (A : Matrix α α ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hdiag : ∀ i, 0 < A i i) :
    BddBelow (Set.range fun n : ℕ => Real.log ‖A ^ n‖ / (n : ℝ)) := by
  let i : α := Classical.choice inferInstance
  refine ⟨min 0 (Real.log (A i i)), ?_⟩
  rintro x ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hentry : (A i i) ^ n ≤ ‖A ^ n‖ := by
      calc
        (A i i) ^ n ≤ (A ^ n) i i := pow_self_ge_diag_pow A hA n i
        _ = ‖(A ^ n) i i‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Matrix.pow_apply_nonneg hA n i i)]
        _ ≤ ‖A ^ n‖ := by
          rw [Matrix.linfty_opNorm_def]
          have hsingle : ‖(A ^ n) i i‖₊ ≤ ∑ j, ‖(A ^ n) i j‖₊ :=
            Finset.single_le_sum (s := Finset.univ)
              (f := fun j => ‖(A ^ n) i j‖₊) (fun j _ => bot_le)
              (Finset.mem_univ i)
          have hsup : (∑ j, ‖(A ^ n) i j‖₊) ≤
              Finset.univ.sup (fun r => ∑ j, ‖(A ^ n) r j‖₊) :=
            Finset.le_sup (f := fun r => ∑ j, ‖(A ^ n) r j‖₊) (Finset.mem_univ i)
          exact_mod_cast hsingle.trans hsup
    have hlog : (n : ℝ) * Real.log (A i i) ≤ Real.log ‖A ^ n‖ := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos (hdiag i) n) hentry
    exact (min_le_right _ _).trans ((le_div_iff₀ hnpos).2 (by simpa [mul_comm] using hlog))

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma norm_le_sum_of_nonneg (v : α → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ‖v‖ ≤ ∑ i, v i := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hv i)]
  exact Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)

lemma matrixCoefficient_pos (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (f : α → ℝ) (hf : ∀ i, 0 < f i)
    (start : α) (n : ℕ) :
    0 < ((A ^ n) *ᵥ f) start := by
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (Matrix.pow_apply_nonneg hA n start j) (hf j).le
  · exact ⟨start, Finset.mem_univ start,
      mul_pos (pow_self_pos A hA hdiag n start) (hf start)⟩

lemma matrixCoefficient_le_norm (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (start : α) (n : ℕ) :
    ((A ^ n) *ᵥ f) start ≤ ‖A ^ n‖ * ‖f‖ := by
  calc
    ((A ^ n) *ᵥ f) start ≤ ‖(A ^ n) *ᵥ f‖ := by
      have hc : 0 ≤ ((A ^ n) *ᵥ f) start := by
        rw [Matrix.mulVec, dotProduct]
        exact Finset.sum_nonneg fun j _ =>
          mul_nonneg (Matrix.pow_apply_nonneg hA n start j) (hf j)
      calc
        ((A ^ n) *ᵥ f) start = ‖((A ^ n) *ᵥ f) start‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hc]
        _ ≤ ‖(A ^ n) *ᵥ f‖ := norm_le_pi_norm _ start
    _ ≤ ‖A ^ n‖ * ‖f‖ := Matrix.linfty_opNorm_mulVec _ _

lemma matrixCoefficient_shift_ge_norm
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (f : α → ℝ) (hf : ∀ i, 0 < f i) (start : α)
    (K : ℕ) (haccess : ∀ i, 0 < (A ^ K) start i) (n : ℕ) :
    let p := Finset.univ.inf' Finset.univ_nonempty (fun i => (A ^ K) start i)
    let b := Finset.univ.inf' Finset.univ_nonempty f
    p * b * ‖A ^ n‖ ≤ ((A ^ (K + n)) *ᵥ f) start := by
  dsimp only
  let p := Finset.univ.inf' Finset.univ_nonempty (fun i => (A ^ K) start i)
  let b := Finset.univ.inf' Finset.univ_nonempty f
  have hp : 0 < p := (Finset.lt_inf'_iff Finset.univ_nonempty).2
    (fun i hi => haccess i)
  have hb : 0 < b := (Finset.lt_inf'_iff Finset.univ_nonempty).2
    (fun i hi => hf i)
  have hp_le (i : α) : p ≤ (A ^ K) start i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hb_le (i : α) : b ≤ f i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  let v : α → ℝ := (A ^ n) *ᵥ (fun _ => (1 : ℝ))
  have hv (i : α) : 0 ≤ v i := by
    dsimp [v, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => by
      simpa using Matrix.pow_apply_nonneg hA n i j
  have hinner (i : α) : b * v i ≤ ((A ^ n) *ᵥ f) i := by
    dsimp [v, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      by
        simpa [mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left (hb_le j) (Matrix.pow_apply_nonneg hA n i j)
  rw [pow_add, ← Matrix.mulVec_mulVec]
  calc
    p * b * ‖A ^ n‖ = p * b * ‖v‖ := by
      rw [norm_mulVec_one (A ^ n) (Matrix.pow_apply_nonneg hA n)]
    _ ≤ p * b * ∑ i, v i := by
      exact mul_le_mul_of_nonneg_left (norm_le_sum_of_nonneg v hv)
        (mul_nonneg hp.le hb.le)
    _ = ∑ i, p * (b * v i) := by
      simp only [Finset.mul_sum]
      ring
    _ ≤ ∑ i, (A ^ K) start i * (((A ^ n) *ᵥ f) i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (hp_le i) (hinner i) (mul_nonneg hb.le (hv i))
        (Matrix.pow_apply_nonneg hA K start i)
    _ = (A ^ K *ᵥ ((A ^ n) *ᵥ f)) start := by
      rfl

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma tendsto_natCast_div_natCast_add (K : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) / (K + n : ℕ)) atTop (nhds 1) := by
  have hden : Tendsto (fun n : ℕ => ((K + n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Function.comp_apply, Nat.add_comm] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat K) :
        Tendsto (fun n : ℕ => ((n + K : ℕ) : ℝ)) atTop atTop)
  have hsmall : Tendsto (fun n : ℕ => (K : ℝ) / (K + n : ℕ)) atTop
      (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hmain : Tendsto (fun n : ℕ => 1 - (K : ℝ) / (K + n : ℕ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hsmall
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hdenne : ((K + n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add]




theorem exists_matrixCoefficient_log_div_tendsto
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (f : α → ℝ) (hf : ∀ i, 0 < f i)
    (start : α) (K : ℕ) (haccess : ∀ i, 0 < (A ^ K) start i) :
    ∃ rate : ℝ, Tendsto (fun n : ℕ =>
      Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
  let u : ℕ → ℝ := fun n => Real.log ‖A ^ n‖
  have hsub : Subadditive u := log_norm_pow_subadditive A hA hdiag
  let rate := hsub.lim
  have hu : Tendsto (fun n => u n / (n : ℝ)) atTop (nhds rate) :=
    hsub.tendsto_lim (log_norm_pow_ratio_bddBelow A hA hdiag)
  let p := Finset.univ.inf' Finset.univ_nonempty (fun i => (A ^ K) start i)
  let b := Finset.univ.inf' Finset.univ_nonempty f
  have hp : 0 < p := (Finset.lt_inf'_iff Finset.univ_nonempty).2
    (fun i hi => haccess i)
  have hb : 0 < b := (Finset.lt_inf'_iff Finset.univ_nonempty).2
    (fun i hi => hf i)
  have hfne : f ≠ 0 := by
    intro hfzero
    let i : α := Classical.choice inferInstance
    have := hf i
    rw [hfzero] at this
    simp at this
  have hfnorm : 0 < ‖f‖ := norm_pos_iff.mpr hfne
  have hden : Tendsto (fun n : ℕ => ((K + n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Function.comp_apply, Nat.add_comm] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat K) :
        Tendsto (fun n : ℕ => ((n + K : ℕ) : ℝ)) atTop atTop)
  have hsmallLower : Tendsto (fun n : ℕ => Real.log (p * b) / (K + n : ℕ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hratio := tendsto_natCast_div_natCast_add K
  have huLowerCore : Tendsto (fun n : ℕ => u n / (K + n : ℕ))
      atTop (nhds rate) := by
    have hprod : Tendsto
        (fun n : ℕ => (u n / (n : ℝ)) * ((n : ℝ) / (K + n : ℕ)))
        atTop (nhds rate) := by simpa using hu.mul hratio
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (n : ℝ) ≠ 0 := by positivity
    have hdenreal : ((K + n : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hlowerT : Tendsto (fun n : ℕ =>
      (u n + Real.log (p * b)) / (K + n : ℕ)) atTop (nhds rate) := by
    convert huLowerCore.add hsmallLower using 1
    · funext n
      by_cases hdenzero : K + n = 0
      · simp [hdenzero]
      · have hdenreal : ((K + n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdenzero
        field_simp
    · ring
  have huUpper : Tendsto (fun n : ℕ => u (K + n) / (K + n : ℕ))
      atTop (nhds rate) := by
    have hshift := (tendsto_add_atTop_iff_nat K).2 hu
    simpa [Nat.add_comm] using hshift
  have hsmallUpper : Tendsto (fun n : ℕ => Real.log ‖f‖ / (K + n : ℕ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hupperT : Tendsto (fun n : ℕ =>
      (u (K + n) + Real.log ‖f‖) / (K + n : ℕ)) atTop (nhds rate) := by
    convert huUpper.add hsmallUpper using 1
    · funext n
      by_cases hdenzero : K + n = 0
      · simp [hdenzero]
      · have hdenreal : ((K + n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdenzero
        field_simp
    · ring
  have hsqueeze : Tendsto (fun n : ℕ =>
      Real.log (((A ^ (K + n)) *ᵥ f) start) / (K + n : ℕ))
      atTop (nhds rate) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerT hupperT
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hdenpos : (0 : ℝ) < (K + n : ℕ) := by positivity
      apply (div_le_div_iff_of_pos_right hdenpos).2
      have hlower := matrixCoefficient_shift_ge_norm A hA f hf start K haccess n
      have hnormpos := norm_pow_pos A hA hdiag n
      have hcoeffpos := matrixCoefficient_pos A hA hdiag f hf start (K + n)
      calc
        u n + Real.log (p * b) = Real.log (p * b * ‖A ^ n‖) := by
          dsimp [u]
          rw [Real.log_mul (mul_pos hp hb).ne' hnormpos.ne']
          ring
        _ ≤ Real.log (((A ^ (K + n)) *ᵥ f) start) :=
          Real.log_le_log (mul_pos (mul_pos hp hb) hnormpos) hlower
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hdenpos : (0 : ℝ) < (K + n : ℕ) := by positivity
      apply (div_le_div_iff_of_pos_right hdenpos).2
      have hupper := matrixCoefficient_le_norm A hA f (fun i => (hf i).le)
        start (K + n)
      have hcoeffpos := matrixCoefficient_pos A hA hdiag f hf start (K + n)
      have hnormpos := norm_pow_pos A hA hdiag (K + n)
      calc
        Real.log (((A ^ (K + n)) *ᵥ f) start) ≤
            Real.log (‖A ^ (K + n)‖ * ‖f‖) :=
          Real.log_le_log hcoeffpos hupper
        _ = u (K + n) + Real.log ‖f‖ := by
          dsimp [u]
          rw [Real.log_mul hnormpos.ne' hfnorm.ne']
  refine ⟨rate, ?_⟩
  apply (tendsto_add_atTop_iff_nat K).1
  simpa [Nat.add_comm] using hsqueeze

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def MatrixPositiveReachable (A : Matrix α α ℝ) (start target : α) : Prop :=
  ∃ n : ℕ, 0 < (A ^ n) start target

abbrev MatrixPositiveReachableState (A : Matrix α α ℝ) (start : α) :=
  {target : α // MatrixPositiveReachable A start target}

noncomputable instance (A : Matrix α α ℝ) (start : α) :
    DecidablePred (MatrixPositiveReachable A start) := Classical.decPred _

noncomputable instance (A : Matrix α α ℝ) (start : α) :
    DecidableEq (MatrixPositiveReachableState A start) := Classical.decEq _

def matrixPositiveReachableStart (A : Matrix α α ℝ) (start : α) :
    MatrixPositiveReachableState A start :=
  ⟨start, 0, by simp⟩

instance (A : Matrix α α ℝ) (start : α) :
    Nonempty (MatrixPositiveReachableState A start) :=
  ⟨matrixPositiveReachableStart A start⟩

def matrixPositiveReachableRestriction (A : Matrix α α ℝ) (start : α) :
    Matrix (MatrixPositiveReachableState A start)
      (MatrixPositiveReachableState A start) ℝ :=
  fun i j => A i.1 j.1

lemma MatrixPositiveReachable.trans_pow
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start x y : α)
    (hx : MatrixPositiveReachable A start x) {n : ℕ}
    (hxy : 0 < (A ^ n) x y) : MatrixPositiveReachable A start y := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m + n, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  apply lt_of_lt_of_le (mul_pos hm hxy)
  exact Finset.single_le_sum
    (fun z _ => mul_nonneg (Matrix.pow_apply_nonneg hA m start z)
      (Matrix.pow_apply_nonneg hA n z y))
    (Finset.mem_univ x)

lemma matrixPositiveReachableRestriction_pow_apply
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (n : ℕ) (x y : MatrixPositiveReachableState A start) :
    (matrixPositiveReachableRestriction A start ^ n) x y =
      (A ^ n) x.1 y.1 := by
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases hxy : x = y
      · have hval : x.1 = y.1 := congrArg Subtype.val hxy
        simp [hxy, hval]
      · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
        simp [hxy, hval]
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      change (∑ z : MatrixPositiveReachableState A start,
        (matrixPositiveReachableRestriction A start ^ n) x z * A z.1 y.1) = _
      simp_rw [ih]
      let s := Finset.univ.filter (MatrixPositiveReachable A start)
      calc
        (∑ z : MatrixPositiveReachableState A start,
            (A ^ n) x.1 z.1 * A z.1 y.1) =
            (∑ z ∈ s, (A ^ n) x.1 z * A z y.1) := by
              symm
              apply Finset.sum_subtype s
              intro z
              simp [s]
        _ = ∑ z, (A ^ n) x.1 z * A z y.1 := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro z hz hznot
              have hznotreach : ¬MatrixPositiveReachable A start z := by
                simpa [s] using hznot
              have hpowzero : (A ^ n) x.1 z = 0 := by
                apply le_antisymm
                · apply le_of_not_gt
                  intro hpos
                  exact hznotreach (MatrixPositiveReachable.trans_pow
                    A hA start x.1 z x.2 hpos)
                · exact Matrix.pow_apply_nonneg hA n x.1 z
              simp [hpowzero]

lemma matrixPositiveReachableRestriction_nonneg
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (i j : MatrixPositiveReachableState A start) :
    0 ≤ matrixPositiveReachableRestriction A start i j := hA i.1 j.1

lemma matrixPositiveReachableRestriction_diag_pos
    (A : Matrix α α ℝ) (hdiag : ∀ i, 0 < A i i) (start : α)
    (i : MatrixPositiveReachableState A start) :
    0 < matrixPositiveReachableRestriction A start i i := hdiag i.1

lemma matrixPositiveReachableRestriction_accessible
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (i : MatrixPositiveReachableState A start) :
    ∃ n : ℕ, 0 <
      (matrixPositiveReachableRestriction A start ^ n)
        (matrixPositiveReachableStart A start) i := by
  obtain ⟨n, hn⟩ := i.2
  refine ⟨n, ?_⟩
  rw [matrixPositiveReachableRestriction_pow_apply A hA]
  exact hn

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma exists_common_access_time
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (start : α)
    (haccess : ∀ i, ∃ n : ℕ, 0 < (A ^ n) start i) :
    ∃ K : ℕ, ∀ i, 0 < (A ^ K) start i := by
  let steps : α → ℕ := fun i => Classical.choose (haccess i)
  have hsteps (i : α) : 0 < (A ^ steps i) start i :=
    Classical.choose_spec (haccess i)
  let K := ∑ i, steps i
  refine ⟨K, fun i => ?_⟩
  have hle : steps i ≤ K := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsplit : K = steps i + (K - steps i) := by omega
  rw [hsplit, pow_add, Matrix.mul_apply]
  apply lt_of_lt_of_le
    (mul_pos (hsteps i) (pow_self_pos A hA hdiag (K - steps i) i))
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hA (steps i) start j)
      (Matrix.pow_apply_nonneg hA (K - steps i) j i))
    (Finset.mem_univ i)

lemma matrixPositiveReachableRestriction_coefficient
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (f : α → ℝ) (start : α) (n : ℕ) :
    ((matrixPositiveReachableRestriction A start ^ n) *ᵥ
        (fun i : MatrixPositiveReachableState A start => f i.1))
        (matrixPositiveReachableStart A start) =
      ((A ^ n) *ᵥ f) start := by
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  simp_rw [matrixPositiveReachableRestriction_pow_apply A hA]
  let s := Finset.univ.filter (MatrixPositiveReachable A start)
  calc
    (∑ i : MatrixPositiveReachableState A start, (A ^ n) start i.1 * f i.1) =
        ∑ i ∈ s, (A ^ n) start i * f i := by
          symm
          apply Finset.sum_subtype s
          intro i
          simp [s]
    _ = ∑ i, (A ^ n) start i * f i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hinot
      have hinotreach : ¬MatrixPositiveReachable A start i := by
        simpa [s] using hinot
      have hzero : (A ^ n) start i = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hpos => hinotreach ⟨n, hpos⟩)
        · exact Matrix.pow_apply_nonneg hA n start i
      simp [hzero]




theorem exists_matrixCoefficient_log_div_tendsto_of_nonnegative
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (f : α → ℝ) (hf : ∀ i, 0 < f i)
    (start : α) :
    ∃ rate : ℝ, Tendsto (fun n : ℕ =>
      Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
  let Ar := matrixPositiveReachableRestriction A start
  let sr := matrixPositiveReachableStart A start
  let fr : MatrixPositiveReachableState A start → ℝ := fun i => f i.1
  have hAr : ∀ i j, 0 ≤ Ar i j :=
    matrixPositiveReachableRestriction_nonneg A hA start
  have hArdiag : ∀ i, 0 < Ar i i :=
    matrixPositiveReachableRestriction_diag_pos A hdiag start
  have hreach : ∀ i, ∃ n : ℕ, 0 < (Ar ^ n) sr i := by
    intro i
    exact matrixPositiveReachableRestriction_accessible A hA start i
  obtain ⟨K, hK⟩ := exists_common_access_time Ar hAr hArdiag sr hreach
  obtain ⟨rate, hrate⟩ := exists_matrixCoefficient_log_div_tendsto
    Ar hAr hArdiag fr (fun i => hf i.1) sr K hK
  refine ⟨rate, hrate.congr' ?_⟩
  filter_upwards [] with n
  rw [matrixPositiveReachableRestriction_coefficient A hA]

end

noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]



theorem exists_matrixCoefficient_log_div_tendsto_of_reachable_diag
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (start : α)
    (hdiag : ∀ i, MatrixPositiveReachable A start i → 0 < A i i)
    (f : α → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ rate : ℝ, Tendsto (fun n : ℕ =>
      Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
  let Ar := matrixPositiveReachableRestriction A start
  let sr := matrixPositiveReachableStart A start
  let fr : MatrixPositiveReachableState A start → ℝ := fun i => f i.1
  have hAr : ∀ i j, 0 ≤ Ar i j :=
    matrixPositiveReachableRestriction_nonneg A hA start
  have hArdiag : ∀ i, 0 < Ar i i := fun i => hdiag i.1 i.2
  have hreach : ∀ i, ∃ n : ℕ, 0 < (Ar ^ n) sr i := by
    intro i
    exact matrixPositiveReachableRestriction_accessible A hA start i
  obtain ⟨K, hK⟩ := exists_common_access_time Ar hAr hArdiag sr hreach
  obtain ⟨rate, hrate⟩ := exists_matrixCoefficient_log_div_tendsto
    Ar hAr hArdiag fr (fun i => hf i.1) sr K hK
  refine ⟨rate, hrate.congr' ?_⟩
  filter_upwards [] with n
  rw [matrixPositiveReachableRestriction_coefficient A hA]

end

end StatMech
