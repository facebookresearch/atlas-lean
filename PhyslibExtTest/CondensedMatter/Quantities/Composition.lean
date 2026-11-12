/-
Copyright (c) Meta Platforms, Inc. and affiliates.
-/

module

public import PhyslibExt.CondensedMatter.Quantities.Composition

/-!
# MS01 quantities: composition checks

Exact compiling checks for `PhyslibExt.CondensedMatter.Quantities.Composition`:
Arrhenius numeric instances, composition round trips, the dimension-kernel
example, and boundary/invalid-domain checks.
-/

open Matrix

-- Arrhenius numeric instance (lemmas 1-2): A = 1, E = 2, R = 1, T = 1,
-- y_ref = 1, so y = Real.exp (-2).
example : Real.log (Real.exp (-2) / (1:ℝ)) = -2 := by
  have h1 := arrhenius_log (y := Real.exp (-2)) (y_ref := 1) (A := 1) (T := 1)
    (R := 1) (E := 2) (by norm_num) (by norm_num) (Real.exp_pos _) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [div_one, Real.log_one, mul_one] at h1
  simp only [div_one]
  linear_combination h1

example : Real.logb 10 (Real.exp (-2) / (1:ℝ)) = -2 / Real.log 10 := by
  have h2 := arrhenius_log10 (y := Real.exp (-2)) (y_ref := 1) (A := 1) (T := 1)
    (R := 1) (E := 2) (by norm_num) (by norm_num) (Real.exp_pos _) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [div_one, Real.logb_one, mul_one, one_mul] at h2
  simp only [div_one]
  linear_combination h2

-- Composition numeric instance (lemma 3): Fin 2 with M = ![55.85, 16.00],
-- x = ![0.4, 0.6]; wtFrac values 1117/1597 and 480/1597 by exact arithmetic.
example : wtFrac (![55.85, 16.00] : Fin 2 → ℝ) (![0.4, 0.6] : Fin 2 → ℝ) 0
    = 1117 / 1597 := by
  simp only [wtFrac, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : wtFrac (![55.85, 16.00] : Fin 2 → ℝ) (![0.4, 0.6] : Fin 2 → ℝ) 1
    = 480 / 1597 := by
  simp only [wtFrac, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : moleFracOfWt (![55.85, 16.00] : Fin 2 → ℝ)
      (wtFrac (![55.85, 16.00] : Fin 2 → ℝ) (![0.4, 0.6] : Fin 2 → ℝ))
    = (![0.4, 0.6] : Fin 2 → ℝ) := by
  apply moleFrac_wtFrac
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

example : wtFrac (![55.85, 16.00] : Fin 2 → ℝ)
      (moleFracOfWt (![55.85, 16.00] : Fin 2 → ℝ)
        (![1117 / 1597, 480 / 1597] : Fin 2 → ℝ))
    = (![1117 / 1597, 480 / 1597] : Fin 2 → ℝ) := by
  apply wtFrac_moleFrac
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

-- Boundary checks: the positivity hypotheses are load-bearing. At T = 0 the
-- hypothesis `0 < T` required by `arrhenius_log`/`arrhenius_log10` is false,
-- so the lemmas do not apply (no identity at T = 0 is claimed).
example : ¬ (0:ℝ) < (0:ℝ) := lt_irrefl 0

-- With M = 0 the weight-fraction denominator vanishes, so no bijection claim
-- is made (the maps require `∀ i, 0 < M i`).
example (x : Fin 2 → ℝ) : ∑ j, (fun _ => (0:ℝ)) j * x j = 0 := by simp

-- Kernel example (lemma 5): D = !![1, 1, 0; 0, 1, 1] has rank 2 (upper bound
-- by height, lower bound by the det-1 leading 2x2 submatrix).
private lemma D_rank_test :
    (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ).rank = 2 := by
  apply le_antisymm (Matrix.rank_le_height _)
  have hsub : Matrix.submatrix (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ)
      id Fin.castSucc = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : (Matrix.submatrix (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ)
      id Fin.castSucc).det ≠ 0 := by
    rw [hsub, Matrix.det_fin_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 := Matrix.rank_of_det_ne_zero hdet
  rw [Fintype.card_fin] at h2
  have hle := Matrix.rank_submatrix_le
    (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ) id Fin.castSucc
  omega

-- The kernel of D is spanned by ![1, -1, 1] (coordinates verified in the
-- kernel by the reverse inclusion, computed entry by entry).
example : LinearMap.ker
      (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ).toLin'
    = Submodule.span ℚ {(![1, -1, 1] : Fin 3 → ℚ)} := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_span_singleton]
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    have h0 : x 0 + x 1 = 0 := by
      have h0' := congrFun hx 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0'
      linarith
    have h1 : x 1 + x 2 = 0 := by
      have h1' := congrFun hx 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1'
      linarith
    refine ⟨x 0, ?_⟩
    ext k
    fin_cases k
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero']
      rw [Fin.mk_zero]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_succ',
        Matrix.cons_val_zero']
      rw [Fin.mk_one]
      linarith
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_succ',
        Matrix.cons_val_zero']
      show x 0 * 1 = x 2
      linarith
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show (![1, -1, 1] : Fin 3 → ℚ) ∈ LinearMap.ker
      (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ).toLin'
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- finrank ker D = 3 - 2 = 1, via lemma 5 (`dim_kernel_finrank`).
example : Module.finrank ℚ (LinearMap.ker
      (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ).toLin') = 1 := by
  have h := dim_kernel_finrank
    (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ)
  rw [D_rank_test] at h
  norm_num at h
  exact h
