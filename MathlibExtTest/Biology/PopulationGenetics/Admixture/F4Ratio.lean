/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.F4Ratio
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory
open MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.F4Ratio

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ4` is averaging over the four outcomes. -/
theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Two orthogonal drift increments, each with second moment `1/16`. -/
noncomputable def incr4 : Fin 2 → Fin 4 → ℝ :=
  ![![1 / 4, 1 / 4, -1 / 4, -1 / 4], ![1 / 4, -1 / 4, 1 / 4, -1 / 4]]

/-- Drift-model witness for the split-reference example. Populations are
`0 = A`, `1 = O`, `2 = X`, `3 = Y`, `4 = B`, `5 = C`, with
`X = (3/4) Y + (1/4) C` in lineage weights. -/
noncomputable def M : DriftModel μ4 (Fin 2) (Fin 6) where
  root := fun _ => 1 / 2
  incr := incr4
  len := fun _ => 1 / 16
  weight := ![![1, 1], ![0, 0], ![3 / 4, 3 / 4], ![1, 1], ![1, 0], ![0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, incr4] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, incr4] <;> norm_num

theorem weight_X :
    M.weight 2 = (3 / 4 : ℝ) • M.weight 3 + (1 - 3 / 4 : ℝ) • M.weight 5 := by
  ext e
  fin_cases e <;> simp [M] <;> norm_num

theorem f4_B : f4 μ4 M.freq 0 1 4 5 = 1 / 16 := by
  rw [M.f4_freq]
  simp [M, Fin.sum_univ_two]

theorem f4_Y : f4 μ4 M.freq 0 1 3 5 = 1 / 8 := by
  rw [M.f4_freq]
  simp [M, Fin.sum_univ_two]
  norm_num

theorem f4_B_ne_zero : f4 μ4 M.freq 0 1 4 5 ≠ 0 := by
  rw [f4_B]
  norm_num

/-- The principal bias-factor API on the concrete model. -/
example :
    f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 =
      (3 / 4) * (f4 μ4 M.freq 0 1 3 5 / f4 μ4 M.freq 0 1 4 5) :=
  M.f4_ratio_eq_mul_div weight_X f4_B_ne_zero

/-- The principal iff API detects the failed f4 equality on the concrete
model: the ratio is not `α = 3/4`. -/
example : ¬ f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 = 3 / 4 := by
  have hiff := M.f4_ratio_eq_iff weight_X f4_B_ne_zero
  intro h
  rcases hiff.mp h with hα | hEq
  · norm_num at hα
  · rw [f4_Y, f4_B] at hEq
    norm_num at hEq

/-- With `α = 3/4`, the misspecified ratio is `3/2`, outside `[0, 1]`. -/
example : f4 μ4 M.freq 0 1 2 5 / f4 μ4 M.freq 0 1 4 5 = 3 / 2 := by
  have h := M.f4_ratio_eq_two_mul_of_split_reference (A := 0) (O := 1) (X := 2)
    (Y := 3) (B := 4) (C := 5) (α := 3 / 4) (ℓ := 1 / 16)
    (by norm_num)
    (by ext e; fin_cases e <;> simp [M])
    rfl rfl rfl rfl rfl weight_X
  rw [h]
  norm_num

/-- Scalar boundary probe through the iff API: at `α = 0`, the ratio is `α`
even when f4 equality fails; this is why the iff has the `α = 0` disjunct. -/
example :
    ((0 : ℝ) * 2) / 1 = 0 ∧ ¬((2 : ℝ) = 1) := by
  have h := (MathlibExt.Biology.PopulationGenetics.Admixture.ratio_eq_iff_of_eq_mul
    (α := (0 : ℝ)) (fX := (0 : ℝ)) (fY := (2 : ℝ)) (fB := (1 : ℝ))
    (by norm_num) (by norm_num)).mpr (Or.inl rfl)
  exact ⟨by simpa using h, by norm_num⟩

end MathlibExtTest.Biology.PopulationGenetics.Admixture.F4Ratio
