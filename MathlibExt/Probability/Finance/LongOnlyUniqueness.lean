/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.LongOnlyAttainment
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Uniqueness of the long-only constrained variance minimizer

Under positivity of the quadratic form on every nonzero feasible
difference (`existsUnique_isMinOn_targetSlice_of_pair_pos`), the minimizer
from `MathlibExt.Probability.Finance.LongOnlyAttainment` is unique: two
distinct minimizers would make their midpoint, which stays in the slice,
strictly better by the midpoint identity. Positive definiteness is a
sufficient specialization (`existsUnique_isMinOn_targetSlice_of_posDef`),
not an equivalent condition.
-/

open MathlibExt.Probability.Finance.LongOnlyAttainment
open Matrix

namespace MathlibExt.Probability.Finance.LongOnlyUniqueness

/-- Parallelogram identity for the quadratic form, no symmetry needed. -/
private theorem quad_parallelogram {ι : Type*} [Fintype ι]
    (Sigma : Matrix ι ι ℝ) (w v : ι → ℝ) :
    (w + v) ⬝ᵥ (Sigma *ᵥ (w + v)) + (w - v) ⬝ᵥ (Sigma *ᵥ (w - v))
      = 2 * ((w ⬝ᵥ (Sigma *ᵥ w)) + (v ⬝ᵥ (Sigma *ᵥ v))) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, dotProduct_sub]
  ring

/-- Quadratic homogeneity at scale `1 / 2`. -/
private theorem quad_half_smul {ι : Type*} [Fintype ι]
    (Sigma : Matrix ι ι ℝ) (x : ι → ℝ) :
    ((1 / 2 : ℝ) • x) ⬝ᵥ (Sigma *ᵥ ((1 / 2 : ℝ) • x))
      = (x ⬝ᵥ (Sigma *ᵥ x)) / 4 := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- The midpoint `(1 / 2) • (w + v)` of feasible weights is feasible. -/
private theorem mid_mem_targetSlice {ι : Type*} [Fintype ι]
    (μv : ι → ℝ) (m : ℝ) (w v : ι → ℝ)
    (hw : w ∈ targetSlice μv m) (hv : v ∈ targetSlice μv m) :
    (1 / 2 : ℝ) • (w + v) ∈ targetSlice μv m := by
  obtain ⟨hwge, hws, hwd⟩ := hw
  obtain ⟨hvge, hvs, hvd⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    exact mul_nonneg (by norm_num) (add_nonneg (hwge i) (hvge i))
  · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hws, hvs]
    norm_num
  · rw [dotProduct_smul, dotProduct_add, hwd, hvd, smul_eq_mul]
    ring

theorem existsUnique_isMinOn_targetSlice_of_pair_pos {ι : Type*} [Fintype ι]
    (Sigma : Matrix ι ι ℝ) (μv : ι → ℝ) (m : ℝ)
    (hne : (targetSlice μv m).Nonempty)
    (hpos : ∀ w ∈ targetSlice μv m, ∀ v ∈ targetSlice μv m, w ≠ v →
      0 < (w - v) ⬝ᵥ (Sigma *ᵥ (w - v))) :
    ∃! w, w ∈ targetSlice μv m ∧
      IsMinOn (fun w => w ⬝ᵥ (Sigma *ᵥ w)) (targetSlice μv m) w := by
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := exists_isMinOn_targetSlice Sigma μv m hne
  refine ⟨w₀, ⟨hw₀mem, hw₀min⟩, ?_⟩
  intro v hv
  obtain ⟨hvmem, hvmin⟩ := hv
  by_contra hne'
  have hdiff : w₀ ≠ v := fun h => hne' h.symm
  have hQd : 0 < (w₀ - v) ⬝ᵥ (Sigma *ᵥ (w₀ - v)) :=
    hpos w₀ hw₀mem v hvmem hdiff
  have humem : (1 / 2 : ℝ) • (w₀ + v) ∈ targetSlice μv m :=
    mid_mem_targetSlice μv m w₀ v hw₀mem hvmem
  have hle1 : w₀ ⬝ᵥ (Sigma *ᵥ w₀) ≤ v ⬝ᵥ (Sigma *ᵥ v) := hw₀min hvmem
  have hle2 : v ⬝ᵥ (Sigma *ᵥ v) ≤ w₀ ⬝ᵥ (Sigma *ᵥ w₀) := hvmin hw₀mem
  have hleu : w₀ ⬝ᵥ (Sigma *ᵥ w₀)
      ≤ ((1 / 2 : ℝ) • (w₀ + v)) ⬝ᵥ (Sigma *ᵥ ((1 / 2 : ℝ) • (w₀ + v))) :=
    hw₀min humem
  have heq : w₀ ⬝ᵥ (Sigma *ᵥ w₀) = v ⬝ᵥ (Sigma *ᵥ v) := le_antisymm hle1 hle2
  have hpar := quad_parallelogram Sigma w₀ v
  have hhom := quad_half_smul Sigma (w₀ + v)
  have hlt : ((1 / 2 : ℝ) • (w₀ + v)) ⬝ᵥ (Sigma *ᵥ ((1 / 2 : ℝ) • (w₀ + v)))
      < w₀ ⬝ᵥ (Sigma *ᵥ w₀) := by
    linarith [hpar, hhom, hQd, heq]
  exact not_lt_of_ge hleu hlt

/-- Positivity specialization: if `Sigma` is positive definite, the
distinct-pair positivity hypothesis above is satisfied. -/
theorem existsUnique_isMinOn_targetSlice_of_posDef {ι : Type*} [Fintype ι]
    (Sigma : Matrix ι ι ℝ) (μv : ι → ℝ) (m : ℝ)
    (hne : (targetSlice μv m).Nonempty) (hSigma : Sigma.PosDef) :
    ∃! w, w ∈ targetSlice μv m ∧
      IsMinOn (fun w => w ⬝ᵥ (Sigma *ᵥ w)) (targetSlice μv m) w := by
  apply existsUnique_isMinOn_targetSlice_of_pair_pos Sigma μv m hne
  intro w hw v hv hne'
  have hsub : w - v ≠ 0 := sub_ne_zero.mpr hne'
  have h := hSigma.dotProduct_mulVec_pos hsub
  rwa [star_trivial] at h


end MathlibExt.Probability.Finance.LongOnlyUniqueness
