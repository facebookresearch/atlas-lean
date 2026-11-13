/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.Quantities.Composition
public import PhyslibExt.Chemistry.Amounts.MolarMassComposition
public import PhyslibExt.Chemistry.QuantityCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# MS01 quantities: composition checks

Exact compiling checks for `PhyslibExt.CondensedMatter.Quantities.Composition`:
typed Arrhenius numeric instances, composition round trips through the canonical
`Chemistry.Amounts` theorems, the dimension-kernel example through the canonical
`Chemistry.QuantityCalculus.finrank_ker_mulVecLin`, and boundary/invalid-domain
checks.
-/

open Matrix
open Units.QuantityDimensions PhyslibExt.CondensedMatter.Quantities.Composition

/-- Dimension of a first-order rate constant, `time⁻¹`, for the typed Arrhenius instances. -/
private abbrev rateDim : Dimension ISQDimensionBase := (Dimension.single .time)⁻¹

-- Arrhenius numeric instance (lemmas 1-2): A = 1, E = 2, R = 1, T = 1,
-- y_ref = 1 as typed quantities, so y = Real.exp (-2).
example : logRatio (⟨Real.exp (-2)⟩ : WithDim rateDim ℝ) ⟨1⟩ (Real.exp_pos _) one_pos
    = -2 := by
  have h1 := arrhenius_log (y := (⟨Real.exp (-2)⟩ : WithDim rateDim ℝ)) (y_ref := ⟨1⟩)
    (A := ⟨1⟩) (E := ⟨2⟩) (R := ⟨1⟩) (T := ⟨1⟩) one_pos one_pos (Real.exp_pos _) one_pos
    one_pos (by rw [expScaledEnergy_val]; norm_num)
  rw [h1, logRatio_self]
  norm_num

-- The base-10 form on the same instance, read as `Real.logb 10` on coordinates.
example : Real.logb 10 (Real.exp (-2) / (1:ℝ)) = -2 / Real.log 10 := by
  have h2 := arrhenius_log10 (y := (⟨Real.exp (-2)⟩ : WithDim rateDim ℝ)) (y_ref := ⟨1⟩)
    (A := ⟨1⟩) (E := ⟨2⟩) (R := ⟨1⟩) (T := ⟨1⟩) one_pos one_pos (Real.exp_pos _) one_pos
    one_pos (by rw [expScaledEnergy_val]; norm_num)
  rw [logRatio_val, logRatio_val] at h2
  simp only [div_one, Real.log_one, zero_div, mul_one, one_mul, zero_sub] at h2
  rw [← Real.log_div_log, div_one, h2, neg_div]

-- The typed identity keeps the raw-real content: wrapping arbitrary reals as typed
-- quantities recovers the coordinate form `log (y / y_ref) = log (A / y_ref) - E / (R * T)`.
example {y y_ref A T R E : ℝ} (hy_ref : 0 < y_ref) (hA : 0 < A) (hy : 0 < y) (hT : 0 < T)
    (hR : 0 < R) (h : y = A * Real.exp (-E / (R * T))) :
    Real.log (y / y_ref) = Real.log (A / y_ref) - E / (R * T) := by
  have h1 := arrhenius_log (y := (⟨y⟩ : WithDim rateDim ℝ)) (y_ref := ⟨y_ref⟩) (A := ⟨A⟩)
    (E := ⟨E⟩) (R := ⟨R⟩) (T := ⟨T⟩) hy_ref hA hy hT hR
    (by rw [expScaledEnergy_val, ← neg_div]; exact h)
  simpa only [logRatio_val] using h1

-- Composition numeric instance: Fin 2 with M = ![55.85, 16.00],
-- x = ![0.4, 0.6]; massFraction values 1117/1597 and 480/1597 by exact
-- arithmetic (55.85 * 0.4 = 22.34, 16.00 * 0.6 = 9.6, sum 31.94;
-- 22.34 / 31.94 = 1117 / 1597, 9.6 / 31.94 = 480 / 1597).
example : Chemistry.Amounts.massFraction (![55.85, 16.00] : Fin 2 → ℝ)
      (![0.4, 0.6] : Fin 2 → ℝ) 0 = 1117 / 1597 := by
  simp only [Chemistry.Amounts.massFraction, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : Chemistry.Amounts.massFraction (![55.85, 16.00] : Fin 2 → ℝ)
      (![0.4, 0.6] : Fin 2 → ℝ) 1 = 480 / 1597 := by
  simp only [Chemistry.Amounts.massFraction, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

example : Chemistry.Amounts.moleFractionOfMassFraction
      (![55.85, 16.00] : Fin 2 → ℝ)
      (Chemistry.Amounts.massFraction (![55.85, 16.00] : Fin 2 → ℝ)
        (![0.4, 0.6] : Fin 2 → ℝ))
    = (![0.4, 0.6] : Fin 2 → ℝ) := by
  apply Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

example : Chemistry.Amounts.massFraction (![55.85, 16.00] : Fin 2 → ℝ)
      (Chemistry.Amounts.moleFractionOfMassFraction (![55.85, 16.00] : Fin 2 → ℝ)
        (![1117 / 1597, 480 / 1597] : Fin 2 → ℝ))
    = (![1117 / 1597, 480 / 1597] : Fin 2 → ℝ) := by
  apply Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · intro i
    fin_cases i <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

-- Percent round trip: same numeric instance in percent form,
-- exercising `wtPct` / `atPct` / `wtPct_atPct` in both directions.
example : wtPct (![55.85, 16.00] : Fin 2 → ℝ)
        (Chemistry.Amounts.moleFractionOfMassFraction
          (![55.85, 16.00] : Fin 2 → ℝ)
          (fun i => (![100 * (1117 / 1597), 100 * (480 / 1597)] : Fin 2 → ℝ) i / 100))
      = (![100 * (1117 / 1597), 100 * (480 / 1597)] : Fin 2 → ℝ)
    ∧ atPct (Chemistry.Amounts.moleFractionOfMassFraction
          (![55.85, 16.00] : Fin 2 → ℝ)
          (Chemistry.Amounts.massFraction (![55.85, 16.00] : Fin 2 → ℝ)
            (![0.4, 0.6] : Fin 2 → ℝ)))
        = atPct (![0.4, 0.6] : Fin 2 → ℝ) := by
  have hM : ∀ i, 0 < (![55.85, 16.00] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · apply (wtPct_atPct hM).1
    · intro i
      fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
  · apply (wtPct_atPct hM).2
    · intro i
      fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num

-- Boundary checks: the positivity hypotheses are load-bearing. At T = 0 the
-- hypothesis `0 < T.val` required by `arrhenius_log`/`arrhenius_log10` (and by
-- `expScaledEnergy`) is false, so the lemmas do not apply (no identity at T = 0 is claimed).
example : ¬ (0:ℝ) < (0:ℝ) := lt_irrefl 0

-- With M = 0 the mass-fraction denominator `∑ j, x j * M j` vanishes, so no
-- bijection claim is made (the maps require `∀ i, 0 < M i`).
example (x : Fin 2 → ℝ) : ∑ j, x j * (fun _ => (0:ℝ)) j = 0 := by simp

-- Kernel example: D = !![1, 1, 0; 0, 1, 1] has rank 2 (upper bound
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

-- finrank ker D = 3 - 2 = 1, via the canonical
-- `Chemistry.QuantityCalculus.finrank_ker_mulVecLin`.
example : Module.finrank ℚ (LinearMap.ker
      (!![1, 1, 0; 0, 1, 1] : Matrix (Fin 2) (Fin 3) ℚ).toLin') = 1 := by
  rw [Matrix.toLin'_apply', Chemistry.QuantityCalculus.finrank_ker_mulVecLin, D_rank_test]
