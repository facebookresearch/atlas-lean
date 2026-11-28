/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.SpectralRadiusSummable
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

@[expose] public section

open scoped ENNReal

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private noncomputable def entryLin {S : Type*} [Fintype S] [DecidableEq S] (i j : S) :
    Matrix S S ℂ →ₗ[ℂ] ℂ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem entry_norm_le {S : Type*} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℂ) (i j : S) : ‖A i j‖ ≤ ‖A‖ := by
  have h1 : ‖A i j‖₊ ≤ ∑ j', ‖A i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (s := (Finset.univ : Finset S))
      (fun (x : S) (_ : x ∈ Finset.univ) => (zero_le : 0 ≤ ‖A i x‖₊))
      (Finset.mem_univ j)
  have h2 : (∑ j', ‖A i j'‖₊) ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  have hle : ‖A i j‖₊ ≤ ‖A‖₊ := h1.trans h2
  exact_mod_cast hle

private noncomputable def entryCLM {S : Type*} [Fintype S] [DecidableEq S] (i j : S) :
    Matrix S S ℂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous (entryLin i j) 1 (fun A => by
    have hle := entry_norm_le A i j
    change ‖A i j‖ ≤ 1 * ‖A‖
    rw [one_mul]
    exact hle)

private theorem map_pow_eq {S : Type*} [Fintype S] [DecidableEq S]
    (T : Matrix S S ℝ) (k : ℕ) :
    (T.map Complex.ofReal) ^ k = (T ^ k).map Complex.ofReal := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact (Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one).symm
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    exact (Matrix.map_mul (L := T ^ k) (M := T) (f := Complex.ofRealHom)).symm

/-- Entrywise summability of real matrix powers whose complexified spectral
radius is below 1. -/
theorem summable_pow_apply_of_spectralRadius_map_lt_one {S : Type*} [Fintype S]
    [DecidableEq S] (T : Matrix S S ℝ)
    (h : spectralRadius ℂ (T.map Complex.ofReal) < 1) (i j : S) :
    Summable fun n => (T ^ n) i j := by
  have hC := summable_of_spectralRadius_lt_one (T.map Complex.ofReal) h
  have hE := (entryCLM i j).summable hC
  have hpt : ∀ k, entryCLM i j ((T.map Complex.ofReal) ^ k)
      = Complex.ofReal ((T ^ k) i j) := by
    intro k
    rw [map_pow_eq T k]
    rfl
  have hC' : Summable (fun k => Complex.ofReal ((T ^ k) i j)) _ := hE.congr hpt
  exact Complex.summable_ofReal.mp hC'

/-- Summability of the real Neumann terms applied to a vector, from the
complexified spectral radius condition. -/
theorem summable_pow_mulVec_apply_of_spectralRadius_map_lt_one {S : Type*}
    [Fintype S] [DecidableEq S] (T : Matrix S S ℝ)
    (h : spectralRadius ℂ (T.map Complex.ofReal) < 1) (E : S → ℝ) (i : S) :
    Summable fun n => (T ^ n).mulVec E i := by
  have h1 : ∀ j, Summable (fun n => (T ^ n) i j * E j) _ :=
    fun j => (summable_pow_apply_of_spectralRadius_map_lt_one T h i j).mul_right (E j)
  have h2 := summable_sum (s := (Finset.univ : Finset S))
    (f := fun j n => (T ^ n) i j * E j) (fun j _ => h1 j)
  refine h2.congr (fun n => ?_)
  rfl

end
end
public section
