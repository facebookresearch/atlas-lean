/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.TreeFStatistics

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.TreeFStatistics
open scoped ENNReal

namespace MathlibExtTest.Biology.PopulationGenetics.TreeFStatistics

/-- The uniform probability measure on `Fin 4`. -/
noncomputable def μ4 : Measure (Fin 4) := (4⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ4 :=
  ⟨by simpa [μ4] using ENNReal.inv_mul_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

theorem integral_μ4 (f : Fin 4 → ℝ) : ∫ ω, f ω ∂μ4 = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp only [μ4, integral_smul_measure, integral_count, Fin.sum_univ_four]
  norm_num
  ring

/-- Three orthogonal mean-zero increments `±1/8` (drift length `1/64` each). -/
noncomputable def incr3 : Fin 3 → Fin 4 → ℝ :=
  ![![1/8, 1/8, -1/8, -1/8], ![1/8, -1/8, 1/8, -1/8], ![1/8, -1/8, -1/8, 1/8]]

/-! ### Outgroup f3 on a tree

Edge `0` leads from the root to the outgroup `O = 0`; edge `1` is the stem shared by `A = 1`
and `B = 2`; edge `2` is private to `A`; population `3` is the root. -/

/-- The tree witness. -/
noncomputable def T : DriftModel μ4 (Fin 3) (Fin 4) where
  root := fun _ => 1/2
  incr := incr3
  len := fun _ => 1/64
  weight := ![![1, 0, 0], ![0, 1, 1], ![0, 1, 0], ![0, 0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ4, incr3] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ4, incr3] <;> norm_num

theorem T_binary : T.HasBinaryLoadings := by
  intro X e
  fin_cases X <;> fin_cases e <;> simp [T]

theorem lineage_O : T.lineage 0 = {0} := by
  ext e; fin_cases e <;> simp [DriftModel.lineage, T]

theorem lineage_A : T.lineage 1 = {1, 2} := by
  ext e; fin_cases e <;> simp [DriftModel.lineage, T]

theorem lineage_B : T.lineage 2 = {1} := by
  ext e; fin_cases e <;> simp [DriftModel.lineage, T]

/-- Outgroup `f3`: drift from the outgroup to the root (`1/64`) plus the shared stem (`1/64`). -/
example : f3 μ4 T.freq 0 1 2 = 1 / 32 := by
  rw [f3_outgroup T T_binary (by rw [lineage_O, lineage_A]; decide)
    (by rw [lineage_O, lineage_B]; decide), lineage_O, lineage_A, lineage_B]
  simp [T]
  norm_num

/-- The same value by direct computation of the integral. -/
example : f3 μ4 T.freq 0 1 2 = 1 / 32 := by
  simp [f3, integral_μ4, DriftModel.freq, T, incr3, Fin.sum_univ_three]
  norm_num

/-! ### An admixed branch

Populations `A = 0`, `B = 1`, `X = 2` sit at the root; `Mx = 3` mixes the endpoints of edges
`a = 0` and `b = 1` in proportions `1/2 : 1/2` and then drifts on `c = 2`. -/

/-- The admixed-branch witness. -/
noncomputable def Ma : DriftModel μ4 (Fin 3) (Fin 4) :=
  { T with weight := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1/2, 1/2, 1]] }

theorem Ma_weight : Ma.weight 3 = (1/2 : ℝ) • (Ma.weight 0 + Pi.single 0 1) +
    (1 - 1/2 : ℝ) • (Ma.weight 1 + Pi.single 1 1) + Pi.single 2 1 := by
  funext e
  fin_cases e <;> simp [Ma, Matrix.vecHead, Matrix.vecTail]
  norm_num

/-- `f2 Mx X = mixedDrift (1/2) (1/64) (1/64) (1/64) = 3/128`. -/
example : f2 μ4 Ma.freq 3 2 = 3 / 128 := by
  rw [f2_admixedBranch Ma (by decide) (by decide) (by decide) Ma_weight
    (fun e _ => by fin_cases e <;> simp [Ma]) (fun e _ => by fin_cases e <;> simp [Ma])
    (fun e _ => by fin_cases e <;> simp [Ma])]
  rw [Ma.f2_freq, Ma.f2_freq, Ma.f2_freq]
  simp [Ma, T, mixedDrift]
  norm_num

/-- The same value by direct computation. -/
example : f2 μ4 Ma.freq 3 2 = 3 / 128 := by
  rw [Ma.f2_freq]
  simp [Ma, T, Fin.sum_univ_three]
  norm_num

#print axioms f3_outgroup
#print axioms f2_admixedBranch
#print axioms alpha_eq_of_f2

end MathlibExtTest.Biology.PopulationGenetics.TreeFStatistics
