/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.SpectralRadiusSummableReal
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Operations
import Mathlib.Tactic

@[expose] public section

open scoped ENNReal Matrix NNReal

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private def T2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 0, 0]

private def E2 : Fin 2 → ℝ := fun _ => 1

private theorem T2_sq_eq_zero : (T2 ^ 2 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, T2]

private theorem T2_map_sq_eq_zero :
    ((T2.map Complex.ofReal) ^ 2 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, T2]

private theorem T2_spectralRadius_eq_zero :
    spectralRadius ℂ (T2.map Complex.ofReal) = 0 := by
  have hle :=
    spectrum.spectralRadius_pow_le (𝕜 := ℂ) (T2.map Complex.ofReal) 2 (by norm_num)
  rw [T2_map_sq_eq_zero, spectrum.spectralRadius_zero] at hle
  have heq : (spectralRadius ℂ (T2.map Complex.ofReal)) ^ 2 = 0 :=
    le_antisymm hle zero_le
  by_contra hne
  have hpos : 0 < spectralRadius ℂ (T2.map Complex.ofReal) :=
    lt_of_le_of_ne zero_le (Ne.symm hne)
  have hpos2 := ENNReal.pow_pos hpos 2
  rw [heq] at hpos2
  exact lt_irrefl _ hpos2

private theorem T2_spectralRadius_lt_one :
    spectralRadius ℂ (T2.map Complex.ofReal) < 1 := by
  rw [T2_spectralRadius_eq_zero]
  exact zero_lt_one

private theorem T2_summable_entry (i j : Fin 2) :
    Summable fun n => (T2 ^ n) i j :=
  summable_pow_apply_of_spectralRadius_map_lt_one T2 T2_spectralRadius_lt_one i j

private theorem T2_summable : Summable fun n => (T2 ^ n).mulVec E2 0 :=
  summable_pow_mulVec_apply_of_spectralRadius_map_lt_one T2 T2_spectralRadius_lt_one E2 0

private theorem T2_tsum : (∑' n, (T2 ^ n).mulVec E2 0) = 3 := by
  have h0 : (T2 ^ 0).mulVec E2 0 = 1 := by simp [pow_zero, Matrix.one_mulVec, E2]
  have h1 : (T2 ^ 1).mulVec E2 0 = 2 := by
    rw [pow_one]
    change ∑ j, T2 0 j * E2 j = 2
    simp [Fin.sum_univ_two, T2, E2]
  have hz : ∀ n, 2 ≤ n → (T2 ^ n).mulVec E2 0 = 0 := by
    intro n hn
    rw [pow_eq_zero_of_le hn T2_sq_eq_zero]
    simp
  have hsupp : ∀ b ∉ ({0, 1} : Finset ℕ), (T2 ^ b).mulVec E2 0 = 0 := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    exact hz b (by omega)
  have hH := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := ({0, 1} : Finset ℕ)) hsupp
  rw [hH.tsum_eq, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), h0, h1]
  norm_num

private noncomputable def T1 : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1 / 2

private theorem T1_spectralRadius_lt_one :
    spectralRadius ℂ (T1.map Complex.ofReal) < 1 := by
  have hle := spectralRadius_le_nnnorm (𝕜 := ℂ) (T1.map Complex.ofReal)
  have h2 : ‖Complex.ofReal (1 / 2 : ℝ)‖₊ = (1 / 2 : ℝ≥0) := by
    ext
    simp
  have hnorm : ‖T1.map Complex.ofReal‖₊ < 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    have huniv : (Finset.univ : Finset (Fin 1)) = {0} := by decide
    rw [huniv, Finset.sup_singleton]
    change (∑ j ∈ ({0} : Finset (Fin 1)), ‖(T1.map Complex.ofReal) 0 j‖₊) < 1
    rw [Finset.sum_singleton, Matrix.map_apply]
    change ‖Complex.ofReal (1 / 2 : ℝ)‖₊ < 1
    exact lt_of_le_of_lt h2.le (by norm_num)
  have hnormEN : ((‖T1.map Complex.ofReal‖₊ : ℝ≥0) : ℝ≥0∞) < 1 := by
    exact_mod_cast hnorm
  exact lt_of_le_of_lt hle hnormEN

private theorem T1_pow : ∀ n, (T1 ^ n) 0 0 = (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, T1, pow_succ]

private theorem T1_summable (E : Fin 1 → ℝ) :
    Summable fun n => (T1 ^ n).mulVec E 0 :=
  summable_pow_mulVec_apply_of_spectralRadius_map_lt_one T1 T1_spectralRadius_lt_one E 0

private theorem T1_tsum (E : Fin 1 → ℝ) : (∑' n, (T1 ^ n).mulVec E 0) = 2 * E 0 := by
  have hmv : ∀ n, (T1 ^ n).mulVec E 0 = (1 / 2 : ℝ) ^ n * E 0 := by
    intro n
    change ∑ j, (T1 ^ n) 0 j * E j = _
    rw [Fin.sum_univ_one, T1_pow]
  have hcongr : (fun n => (T1 ^ n).mulVec E 0) = fun n => (1 / 2 : ℝ) ^ n * E 0 :=
    funext hmv
  rw [hcongr, tsum_mul_right, tsum_geometric_two]

end
end
public section
