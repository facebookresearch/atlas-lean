/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierC.IsingTransfer
open Matrix Polynomial
namespace StatMech.FrontierB
open StatMech.FrontierC
noncomputable def isingTransferProjectorPlus (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (isingTransferEigenPlus beta h - isingTransferEigenMinus beta h)⁻¹ •
    (isingTransferReal beta h - isingTransferEigenMinus beta h • 1)
noncomputable def isingTransferProjectorMinus (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (isingTransferEigenPlus beta h - isingTransferEigenMinus beta h)⁻¹ •
    (isingTransferEigenPlus beta h • 1 - isingTransferReal beta h)
lemma isingTransfer_eigen_gap_ne_zero (beta h : ℝ) :
    isingTransferEigenPlus beta h - isingTransferEigenMinus beta h ≠ 0 := by
  have := isingTransfer_abs_eigenMinus_lt beta h
  have hp := isingTransfer_eigenPlus_pos beta h
  intro heq
  have he := sub_eq_zero.mp heq
  rw [he] at this
  exact (lt_irrefl _ ((le_abs_self _).trans_lt this))
lemma isingTransferReal_charpoly (beta h : ℝ) :
 (isingTransferReal beta h).charpoly =
  (X-C (isingTransferEigenPlus beta h))*(X-C (isingTransferEigenMinus beta h)) := by
  let rhs : ℝ[X] :=
    (X-C (isingTransferEigenPlus beta h))*(X-C (isingTransferEigenMinus beta h))
  have hm : ((isingTransferReal beta h).charpoly).map (algebraMap ℝ ℂ) =
      rhs.map (algebraMap ℝ ℂ) := by
    calc
      ((isingTransferReal beta h).charpoly).map (algebraMap ℝ ℂ) =
          (isingTransfer beta h).charpoly := by
        rw [isingTransfer, Matrix.charpoly_map]
      _ = (X - C (isingTransferEigenPlus beta h : ℂ)) *
          (X - C (isingTransferEigenMinus beta h : ℂ)) :=
        isingTransfer_charpoly beta h
      _ = rhs.map (algebraMap ℝ ℂ) := by
        simp [rhs]
  exact (Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective) hm
lemma isingTransferReal_cayley_factor (beta h : ℝ) :
 (isingTransferReal beta h - isingTransferEigenPlus beta h • 1) *
 (isingTransferReal beta h - isingTransferEigenMinus beta h • 1) = 0 := by
  have hc := Matrix.aeval_self_charpoly (isingTransferReal beta h)
  rw [isingTransferReal_charpoly] at hc
  simpa [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.smul_def] using hc
lemma isingTransfer_projectors_add (beta h : ℝ) :
    isingTransferProjectorPlus beta h + isingTransferProjectorMinus beta h = 1 := by
  rw [isingTransferProjectorPlus, isingTransferProjectorMinus, ← smul_add]
  have hg := isingTransfer_eigen_gap_ne_zero beta h
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hg]
  · simp [hij]

lemma isingTransfer_mul_projectorPlus (beta h : ℝ) :
    isingTransferReal beta h * isingTransferProjectorPlus beta h =
      isingTransferEigenPlus beta h • isingTransferProjectorPlus beta h := by
  let A := isingTransferReal beta h
  let lp := isingTransferEigenPlus beta h
  let lm := isingTransferEigenMinus beta h
  have heig : A * (A - lm • 1) = lp • (A - lm • 1) := by
    apply sub_eq_zero.mp
    calc
      A * (A - lm • 1) - lp • (A - lm • 1) =
          (A - lp • 1) * (A - lm • 1) := by
        rw [sub_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := isingTransferReal_cayley_factor beta h
  rw [isingTransferProjectorPlus, Matrix.mul_smul, heig]
  simp only [smul_smul]
  rw [mul_comm]

theorem isingTransfer_spectral_decomposition (beta h : ℝ) :
    isingTransferReal beta h =
      isingTransferEigenPlus beta h • isingTransferProjectorPlus beta h +
      isingTransferEigenMinus beta h • isingTransferProjectorMinus beta h := by
  have hg := isingTransfer_eigen_gap_ne_zero beta h
  ext i j
  by_cases hij : i = j
  · subst j
    simp [isingTransferProjectorPlus, isingTransferProjectorMinus]
    field_simp
    ring
  · simp [isingTransferProjectorPlus, isingTransferProjectorMinus, hij]
    field_simp
    ring

lemma isingTransfer_mul_projectorMinus (beta h : ℝ) :
    isingTransferReal beta h * isingTransferProjectorMinus beta h =
      isingTransferEigenMinus beta h • isingTransferProjectorMinus beta h := by
  have hsum := isingTransfer_projectors_add beta h
  have hdec := isingTransfer_spectral_decomposition beta h
  calc
    isingTransferReal beta h * isingTransferProjectorMinus beta h =
        isingTransferReal beta h * (1 - isingTransferProjectorPlus beta h) := by
      congr 1
      rw [← hsum]
      abel
    _ = isingTransferReal beta h -
        isingTransferEigenPlus beta h • isingTransferProjectorPlus beta h := by
      rw [mul_sub, Matrix.mul_one, isingTransfer_mul_projectorPlus]
    _ = isingTransferEigenMinus beta h • isingTransferProjectorMinus beta h := by
      rw [hdec]
      abel

theorem isingTransfer_pow_spectral_decomposition (beta h : ℝ) (n : ℕ) :
    isingTransferReal beta h ^ n =
      isingTransferEigenPlus beta h ^ n • isingTransferProjectorPlus beta h +
      isingTransferEigenMinus beta h ^ n • isingTransferProjectorMinus beta h := by
  induction n with
  | zero => simpa using (isingTransfer_projectors_add beta h).symm
  | succ n ih =>
      rw [pow_succ', ih, mul_add, Matrix.mul_smul, Matrix.mul_smul,
        isingTransfer_mul_projectorPlus, isingTransfer_mul_projectorMinus]
      simp only [smul_smul, pow_succ]


lemma isingTransfer_eigen_gap_eq_disc (beta h : ℝ) :
    isingTransferEigenPlus beta h - isingTransferEigenMinus beta h =
      isingTransferDisc beta h := by
  rw [isingTransferEigenPlus, isingTransferEigenMinus]
  ring

lemma isingTransfer_disc_sq_exp (beta h : ℝ) :
    isingTransferDisc beta h ^ 2 =
      (Real.exp (beta + h) - Real.exp (beta - h)) ^ 2 +
        4 * Real.exp (-beta) ^ 2 := by
  simpa [isingTransferDisc] using isingTransfer_disc_sq beta h

lemma isingTransfer_eigenMinus_exp (beta h : ℝ) :
    isingTransferEigenMinus beta h =
      (Real.exp (beta + h) + Real.exp (beta - h) - isingTransferDisc beta h) / 2 := by
  rfl

set_option linter.flexible false in

theorem isingTransferProjectorPlus_pos (beta h : ℝ) (i j : Fin 2) :
    0 < isingTransferProjectorPlus beta h i j := by
  have hd : 0 < isingTransferDisc beta h := isingTransfer_disc_pos beta h
  have hdsq := isingTransfer_disc_sq_exp beta h
  have hb : 0 < Real.exp (-beta) := Real.exp_pos _
  have had : |Real.exp (beta + h) - Real.exp (beta - h)| <
      isingTransferDisc beta h := by
    rw [abs_lt]
    constructor <;>
      nlinarith [sq_nonneg (Real.exp (beta + h) - Real.exp (beta - h))]
  have hadLower := (abs_lt.mp had).1
  have hadUpper := (abs_lt.mp had).2
  rw [isingTransferProjectorPlus, isingTransfer_eigen_gap_eq_disc]
  fin_cases i <;> fin_cases j <;>
    simp [isingTransferReal, isingTransfer_eigenMinus_exp] <;>
    rw [inv_mul_eq_div] <;>
    apply div_pos <;> nlinarith [hadLower, hadUpper]


lemma isingTransfer_normalized_pow (beta h : ℝ) (n : ℕ) :
    (isingTransferEigenPlus beta h)⁻¹ ^ n • isingTransferReal beta h ^ n =
      isingTransferProjectorPlus beta h +
        (isingTransferEigenMinus beta h / isingTransferEigenPlus beta h) ^ n •
          isingTransferProjectorMinus beta h := by
  rw [isingTransfer_pow_spectral_decomposition, smul_add]
  simp only [smul_smul]
  have hp : isingTransferEigenPlus beta h ≠ 0 :=
    (isingTransfer_eigenPlus_pos beta h).ne'
  congr 1
  · rw [← mul_pow, inv_mul_cancel₀ hp, one_pow, one_smul]
  · congr 1
    rw [← mul_pow, div_eq_mul_inv, mul_comm]




theorem isingTransfer_normalized_pow_tendsto (beta h : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (isingTransferEigenPlus beta h)⁻¹ ^ n •
        isingTransferReal beta h ^ n)
      Filter.atTop (nhds (isingTransferProjectorPlus beta h)) := by
  have hr : Filter.Tendsto
      (fun n : ℕ => (isingTransferEigenMinus beta h /
        isingTransferEigenPlus beta h) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (isingTransfer_eigenRatio_abs_lt_one beta h)
  have hs := hr.smul_const (isingTransferProjectorMinus beta h)
  have hc : Filter.Tendsto (fun _ : ℕ => isingTransferProjectorPlus beta h) Filter.atTop
      (nhds (isingTransferProjectorPlus beta h)) := tendsto_const_nhds
  have hadd := hc.add hs
  simpa only [zero_smul, add_zero, isingTransfer_normalized_pow] using hadd



theorem isingTransfer_normalized_entry_tendsto (beta h : ℝ) (i j : Fin 2) :
    Filter.Tendsto
      (fun n : ℕ => ((isingTransferEigenPlus beta h)⁻¹ ^ n •
        isingTransferReal beta h ^ n) i j)
      Filter.atTop (nhds (isingTransferProjectorPlus beta h i j)) :=
  ((isingTransfer_normalized_pow_tendsto beta h).apply_nhds i).apply_nhds j



theorem isingTransfer_entry_ratio_tendsto (beta h : ℝ)
    (i j k l : Fin 2) :
    Filter.Tendsto
      (fun n : ℕ => (isingTransferReal beta h ^ n) i j /
        (isingTransferReal beta h ^ n) k l)
      Filter.atTop (nhds (isingTransferProjectorPlus beta h i j /
        isingTransferProjectorPlus beta h k l)) := by
  have hnum := isingTransfer_normalized_entry_tendsto beta h i j
  have hden := isingTransfer_normalized_entry_tendsto beta h k l
  have hratio := hnum.div hden (ne_of_gt (isingTransferProjectorPlus_pos beta h k l))
  refine hratio.congr' (Filter.Eventually.of_forall ?_)
  intro n
  simp only [Matrix.smul_apply]
  have hc : (isingTransferEigenPlus beta h)⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (isingTransfer_eigenPlus_pos beta h).ne')
  change (((isingTransferEigenPlus beta h)⁻¹ ^ n *
      (isingTransferReal beta h ^ n) i j) /
      ((isingTransferEigenPlus beta h)⁻¹ ^ n *
        (isingTransferReal beta h ^ n) k l)) = _
  simpa only [one_div] using mul_div_mul_left
    ((isingTransferReal beta h ^ n) i j)
    ((isingTransferReal beta h ^ n) k l) hc


lemma isingTransferProjectorPlus_det (beta h : ℝ) :
    (isingTransferProjectorPlus beta h).det = 0 := by
  have heval : (isingTransferReal beta h).charpoly.eval
      (isingTransferEigenMinus beta h) = 0 := by
    rw [isingTransferReal_charpoly]
    simp
  have hdet : (Matrix.scalar (Fin 2) (isingTransferEigenMinus beta h) -
      isingTransferReal beta h).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact heval
  rw [isingTransferProjectorPlus, Matrix.det_smul,
    show Fintype.card (Fin 2) = 2 by simp]
  have hneg :
      isingTransferReal beta h - isingTransferEigenMinus beta h • 1 =
        -(Matrix.scalar (Fin 2) (isingTransferEigenMinus beta h) -
          isingTransferReal beta h) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    abel
  rw [hneg, Matrix.det_neg, hdet]
  ring


lemma isingTransferProjectorPlus_cross (beta h : ℝ) (a s b : Fin 2) :
    isingTransferProjectorPlus beta h a s *
        isingTransferProjectorPlus beta h s b =
      isingTransferProjectorPlus beta h a b *
        isingTransferProjectorPlus beta h s s := by
  have hd := isingTransferProjectorPlus_det beta h
  rw [Matrix.det_fin_two] at hd
  fin_cases a <;> fin_cases s <;> fin_cases b <;>
    simp_all <;> ring_nf at * <;> linarith




theorem isingTransfer_central_state_weight_tendsto
    (beta h : ℝ) (a s b : Fin 2) :
    Filter.Tendsto
      (fun n : ℕ =>
        (isingTransferReal beta h ^ n) a s *
          (isingTransferReal beta h ^ n) s b /
            (isingTransferReal beta h ^ (2 * n)) a b)
      Filter.atTop (nhds (isingTransferProjectorPlus beta h s s)) := by
  let c := (isingTransferEigenPlus beta h)⁻¹
  let A := isingTransferReal beta h
  let P := isingTransferProjectorPlus beta h
  have hleft := isingTransfer_normalized_entry_tendsto beta h a s
  have hright := isingTransfer_normalized_entry_tendsto beta h s b
  have htwo : Filter.Tendsto (fun n : ℕ => 2 * n)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    omega
  have hden :=
    (isingTransfer_normalized_entry_tendsto beta h a b).comp htwo
  have hden' : Filter.Tendsto
      (fun n : ℕ => (c ^ (2 * n) • A ^ (2 * n)) a b)
      Filter.atTop (nhds (P a b)) := by
    simpa only [Function.comp_apply, c, A, P] using hden
  have hratio := (hleft.mul hright).div hden'
    (ne_of_gt (isingTransferProjectorPlus_pos beta h a b))
  have hlimit : P a s * P s b / P a b = P s s := by
    rw [isingTransferProjectorPlus_cross]
    exact mul_div_cancel_left₀ _
      (ne_of_gt (isingTransferProjectorPlus_pos beta h a b))
  rw [hlimit] at hratio
  refine hratio.congr' (Filter.Eventually.of_forall ?_)
  intro n
  simp only [Matrix.smul_apply]
  have hc : c ^ n ≠ 0 := pow_ne_zero _
    (inv_ne_zero (isingTransfer_eigenPlus_pos beta h).ne')
  have hpow : c ^ (2 * n) = (c ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  change ((c ^ n * (A ^ n) a s) * (c ^ n * (A ^ n) s b) /
      (c ^ (2 * n) * (A ^ (2 * n)) a b)) = _
  rw [hpow, pow_two]
  field_simp
  ring

end StatMech.FrontierB
