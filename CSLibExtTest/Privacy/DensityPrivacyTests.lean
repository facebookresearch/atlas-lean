/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DensityPrivacy

/-!
# Density-privacy tests on a two-outcome example

Nonvacuity checks for the general density argument: two databases over
counting measure on `Fin 2`, with swapped `1/3` vs `2/3` densities (ratio
two) and `ε = log 2`. The density bound, the event bound on every event in
both database orders, the kernel values, and kernel privacy are verified.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.DifferentialPrivacy

open MeasureTheory ProbabilityTheory CSLibExt.Privacy.DifferentialPrivacy
open scoped ENNReal NNReal

instance : MeasurableSpace (Fin 2) := ⊤

instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩

/-- Base measure: counting measure on two outcomes. -/
noncomputable def μ₂ : Measure (Fin 2) := Measure.count

instance : SigmaFinite μ₂ := Measure.count.instSigmaFinite

instance : SFinite μ₂ := inferInstance

/-- Swap densities: `1/3` on the diagonal, `2/3` off it. -/
noncomputable def ρ₂ (d x : Fin 2) : ℝ≥0∞ :=
  ↑(if d = x then (1/3 : ℝ≥0) else (2/3 : ℝ≥0))

/-- The density kernel over the constant base kernel. -/
noncomputable def κ₂ : Kernel (Fin 2) (Fin 2) :=
  Kernel.withDensity (Kernel.const (Fin 2) μ₂) ρ₂

/-- Distinct databases are adjacent. -/
noncomputable def adj₂ : Fin 2 → Fin 2 → Prop := fun d d' => d ≠ d'

/-- Privacy budget: `exp ε = 2` matches the density ratio. -/
noncomputable def ε₂ : ℝ := Real.log 2

theorem meas_ρ₂ : Measurable (Function.uncurry ρ₂) := measurable_of_countable _

theorem exp_ε₂ : ENNReal.ofReal (Real.exp ε₂) = 2 := by
  simp only [ε₂]
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

theorem ρ₂_diag (d : Fin 2) : ρ₂ d d = ((1/3 : ℝ≥0) : ℝ≥0∞) := by simp [ρ₂]

theorem ρ₂_zero_one : ρ₂ 0 1 = ((2/3 : ℝ≥0) : ℝ≥0∞) := by
  have h : (0:Fin 2) ≠ 1 := by decide
  simp only [ρ₂, h, ite_false]

theorem ρ₂_one_zero : ρ₂ 1 0 = ((2/3 : ℝ≥0) : ℝ≥0∞) := by
  have h : (1:Fin 2) ≠ 0 := by decide
  simp only [ρ₂, h, ite_false]

theorem atom_add : ((1/3 : ℝ≥0) : ℝ≥0∞) + ((2/3 : ℝ≥0) : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add]
  have e : ((1/3 : ℝ≥0) + 2/3) = 1 := by norm_num
  rw [e, ENNReal.coe_one]

theorem atom_le_1 : ((1/3 : ℝ≥0) : ℝ≥0∞) ≤ 2 * ((2/3 : ℝ≥0) : ℝ≥0∞) := by
  have c2 : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  rw [c2, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  norm_num

theorem atom_le_2 : ((2/3 : ℝ≥0) : ℝ≥0∞) ≤ 2 * ((1/3 : ℝ≥0) : ℝ≥0∞) := by
  have c2 : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := by norm_cast
  rw [c2, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  norm_num

theorem norm_ρ₂ (d : Fin 2) : ∫⁻ x, ρ₂ d x ∂μ₂ = 1 := by
  simp only [μ₂]
  rw [lintegral_count, tsum_fintype, Fin.sum_univ_two]
  fin_cases d <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [ρ₂_diag, ρ₂_zero_one, atom_add]
  · rw [ρ₂_one_zero, ρ₂_diag, add_comm, atom_add]

instance : IsMarkovKernel κ₂ :=
  density_kernel_isMarkov μ₂ ρ₂ meas_ρ₂ norm_ρ₂

theorem hκ₂ (d : Fin 2) : κ₂ d = μ₂.withDensity (ρ₂ d) :=
  density_kernel_apply μ₂ ρ₂ meas_ρ₂ d

theorem hε₂ : 0 ≤ ε₂ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)

theorem bound_ρ₂ : ∀ d d', adj₂ d d' →
    ∀ᵐ x ∂μ₂, ρ₂ d x ≤ ENNReal.ofReal (Real.exp ε₂) * ρ₂ d' x := by
  intro d d' hadj
  simp only [μ₂]
  rw [exp_ε₂, Measure.ae_count_iff]
  fin_cases d <;> fin_cases d' <;> simp only [Fin.mk_zero, Fin.mk_one]
  · simp only [adj₂] at hadj
    exact (hadj rfl).elim
  · intro x
    fin_cases x <;> simp only [Fin.mk_zero, Fin.mk_one]
    · rw [ρ₂_diag, ρ₂_one_zero]
      exact atom_le_1
    · rw [ρ₂_zero_one, ρ₂_diag]
      exact atom_le_2
  · intro x
    fin_cases x <;> simp only [Fin.mk_zero, Fin.mk_one]
    · rw [ρ₂_one_zero, ρ₂_diag]
      exact atom_le_2
    · rw [ρ₂_diag, ρ₂_zero_one]
      exact atom_le_1
  · simp only [adj₂] at hadj
    exact (hadj rfl).elim

theorem κ₂_zero_zero : κ₂ 0 {0} = ((1/3 : ℝ≥0) : ℝ≥0∞) := by
  rw [hκ₂ 0, withDensity_apply _ (measurableSet_singleton 0), lintegral_singleton]
  simp only [μ₂]
  rw [Measure.count_singleton, ρ₂_diag, mul_one]

theorem κ₂_one_zero : κ₂ 1 {0} = ((2/3 : ℝ≥0) : ℝ≥0∞) := by
  rw [hκ₂ 1, withDensity_apply _ (measurableSet_singleton 0), lintegral_singleton]
  simp only [μ₂]
  rw [Measure.count_singleton, ρ₂_one_zero, mul_one]

theorem κ₂_zero_one : κ₂ 0 {1} = ((2/3 : ℝ≥0) : ℝ≥0∞) := by
  rw [hκ₂ 0, withDensity_apply _ (measurableSet_singleton 1), lintegral_singleton]
  simp only [μ₂]
  rw [Measure.count_singleton, ρ₂_zero_one, mul_one]

theorem κ₂_one_one : κ₂ 1 {1} = ((1/3 : ℝ≥0) : ℝ≥0∞) := by
  rw [hκ₂ 1, withDensity_apply _ (measurableSet_singleton 1), lintegral_singleton]
  simp only [μ₂]
  rw [Measure.count_singleton, ρ₂_diag, mul_one]

theorem κ₂_empty (d : Fin 2) : κ₂ d ∅ = 0 := by
  rw [hκ₂ d, withDensity_apply _ MeasurableSet.empty, setLIntegral_empty]

theorem κ₂_univ (d : Fin 2) : κ₂ d Set.univ = 1 := by
  rw [hκ₂ d, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact norm_ρ₂ d

theorem event_empty_01 :
    κ₂ 0 ∅ ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 1 ∅ :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 0 1
    (show (0:Fin 2) ≠ 1 from by decide) ∅ MeasurableSet.empty

theorem event_empty_10 :
    κ₂ 1 ∅ ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 0 ∅ :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 1 0
    (show (1:Fin 2) ≠ 0 from by decide) ∅ MeasurableSet.empty

theorem event_zero_01 :
    κ₂ 0 {0} ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 1 {0} :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 0 1
    (show (0:Fin 2) ≠ 1 from by decide) {0} (measurableSet_singleton 0)

theorem event_zero_10 :
    κ₂ 1 {0} ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 0 {0} :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 1 0
    (show (1:Fin 2) ≠ 0 from by decide) {0} (measurableSet_singleton 0)

theorem event_one_01 :
    κ₂ 0 {1} ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 1 {1} :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 0 1
    (show (0:Fin 2) ≠ 1 from by decide) {1} (measurableSet_singleton 1)

theorem event_one_10 :
    κ₂ 1 {1} ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 0 {1} :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 1 0
    (show (1:Fin 2) ≠ 0 from by decide) {1} (measurableSet_singleton 1)

theorem event_univ_01 :
    κ₂ 0 Set.univ ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 1 Set.univ :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 0 1
    (show (0:Fin 2) ≠ 1 from by decide) Set.univ MeasurableSet.univ

theorem event_univ_10 :
    κ₂ 1 Set.univ ≤ ENNReal.ofReal (Real.exp ε₂) * κ₂ 0 Set.univ :=
  density_event_bound μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂ 1 0
    (show (1:Fin 2) ≠ 0 from by decide) Set.univ MeasurableSet.univ

theorem isMeasureDP_κ₂ : IsMeasureDP κ₂ adj₂ ε₂ 0 :=
  isMeasureDP_of_density μ₂ κ₂ ρ₂ adj₂ ε₂ meas_ρ₂ hκ₂ hε₂ bound_ρ₂

end CSLibExtTest.Privacy.DifferentialPrivacy
