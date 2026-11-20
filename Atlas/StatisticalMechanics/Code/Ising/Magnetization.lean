/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Ising.Gibbs
import Code.Percolation.Theta

open MeasureTheory

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}






theorem measurable_spin (x : Site d) :
    Measurable (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hmeas : Measurable (fun ω : ConfigSpace (Site d) => ω x) := measurable_pi_apply x
  simp only [spin]
  exact Measurable.ite (hmeas (measurableSet_singleton true)) measurable_const measurable_const



theorem integrable_spin (x : Site d) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    Integrable (fun ω : ConfigSpace (Site d) => spin ω x) μ := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    (measurable_spin x).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa using abs_spin_le_one ω x







noncomputable def magnetization (d : ℕ) (β : ℝ) : ℝ :=
  ∫ ω, spin ω (origin d) ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))



theorem abs_magnetization_le_one (d : ℕ) (β : ℝ) : |magnetization d β| ≤ 1 := by
  rw [magnetization, ← Real.norm_eq_abs]
  haveI : IsProbabilityMeasure (plusState d β 0 : Measure (ConfigSpace (Site d))) :=
    (plusState d β 0).2
  calc ‖∫ ω, spin ω (origin d) ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))‖
      ≤ 1 * (plusState d β 0 : Measure (ConfigSpace (Site d))).real Set.univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards with ω
        simpa using abs_spin_le_one ω (origin d)
    _ = 1 := by simp


theorem magnetization_le_one (d : ℕ) (β : ℝ) : magnetization d β ≤ 1 :=
  (abs_le.mp (abs_magnetization_le_one d β)).2


theorem neg_one_le_magnetization (d : ℕ) (β : ℝ) : -1 ≤ magnetization d β :=
  (abs_le.mp (abs_magnetization_le_one d β)).1





def positiveMagnetizationSet (d : ℕ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ 0 < magnetization d β}

@[simp]
theorem mem_positiveMagnetizationSet {d : ℕ} {β : ℝ} :
    β ∈ positiveMagnetizationSet d ↔ 0 ≤ β ∧ 0 < magnetization d β :=
  Iff.rfl



noncomputable def betaC (d : ℕ) : ℝ :=
  sInf (positiveMagnetizationSet d)

end Ising

end StatMech
