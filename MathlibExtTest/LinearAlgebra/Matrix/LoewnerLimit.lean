/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.LoewnerLimit
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Matrix.Mul

open Filter Topology Matrix

-- Constant sequence: the identity matrix, bounded by itself. The limit
-- supplied by the theorem is the identity, by uniqueness of limits.
example : ∃ L : Matrix (Fin 2) (Fin 2) ℝ, L = 1 ∧
    (∀ n : ℕ, (L - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef) := by
  obtain ⟨L, -, hdom, hlim⟩ :=
    Matrix.tendsto_of_monotone_loewner (A := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (B := 1)
      (fun _ => Matrix.isHermitian_one)
      (fun i j _ => by
        rw [sub_self]
        exact ⟨Matrix.isHermitian_zero, by simp⟩)
      (fun _ => by
        rw [sub_self]
        exact ⟨Matrix.isHermitian_zero, by simp⟩)
  exact ⟨L, Matrix.ext fun i j => by
    have h := hlim i j
    simpa using tendsto_nhds_unique h tendsto_const_nhds, fun n => hdom n⟩

-- Diagonal sequence on `Fin 1`: `A n = diagonal (n / (n+1))`, bounded by
-- `1`. The theorem's limit has `L 0 0 = 1`, the limit of `n / (n+1)`.
example : ∃ L : Matrix (Fin 1) (Fin 1) ℝ, L.IsHermitian ∧ L 0 0 = 1 ∧
    (∀ n : ℕ, ((n : ℝ) / (n + 1)) ≤ L 0 0) := by
  classical
  set A : ℕ → Matrix (Fin 1) (Fin 1) ℝ :=
    fun n => Matrix.diagonal (fun _ => (n : ℝ) / (n + 1)) with hAdef
  have hmono_val : ∀ i j : ℕ, i ≤ j → (i : ℝ) / (i + 1) ≤ (j : ℝ) / (j + 1) := by
    intro i j hij
    have e : ∀ n : ℕ, (n : ℝ) / (n + 1) = 1 - 1 / ((n : ℝ) + 1) := by
      intro n
      field_simp
      ring
    rw [e i, e j]
    have h : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hij 1
    linarith
  have hdiag_psd : ∀ d : Fin 1 → ℝ, (∀ i, 0 ≤ d i) →
      (Matrix.diagonal d).PosSemidef := fun d hd =>
    Matrix.posSemidef_diagonal_iff.mpr hd
  obtain ⟨L, hLh, hdom, hlim⟩ :=
    Matrix.tendsto_of_monotone_loewner (A := A) (B := 1)
      (fun n => Matrix.isHermitian_diagonal _)
      (fun i j hij => by
        have : A j - A i =
            Matrix.diagonal (fun _ => (j : ℝ) / (j + 1) - (i : ℝ) / (i + 1)) := by
          rw [hAdef]
          ext a b
          by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
        rw [this]
        exact hdiag_psd _ (fun _ => sub_nonneg.mpr (hmono_val i j hij)))
      (fun n => by
        have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) - A n =
            Matrix.diagonal (fun _ => 1 - (n : ℝ) / (n + 1)) := by
          ext a b
          fin_cases a <;> fin_cases b <;> simp [hAdef, Matrix.diagonal]
        rw [h1]
        refine hdiag_psd _ (fun _ => sub_nonneg.mpr ?_)
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.le_succ n)
  have hlim1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    have hfun : (fun n : ℕ => (n : ℝ) / (n + 1)) =
        fun n : ℕ => 1 - 1 / ((n : ℝ) + 1) := by
      funext n
      field_simp
      ring
    rw [hfun]
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.sub h0
  have hL00 : L 0 0 = 1 := by
    have h := hlim 0 0
    rw [hAdef] at h
    simp only [Matrix.diagonal_apply_eq] at h
    exact tendsto_nhds_unique h hlim1
  refine ⟨L, hLh, hL00, fun n => ?_⟩
  have hnn := (hdom n).dotProduct_mulVec_nonneg (Pi.single 0 1)
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at hnn
  simpa [star_trivial, single_one_dotProduct, Matrix.mulVec_single_one,
    hAdef] using hnn

#print axioms Matrix.tendsto_of_monotone_loewner
