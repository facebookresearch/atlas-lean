/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TotalExpectation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open MeasureTheory ProbabilityTheory

/-! Tests for `MathlibExt.Probability.TotalExpectation`: concrete instances with exact values. -/

namespace MathlibExtTest.Probability.TotalExpectation

open _root_.MathlibExt.Probability.TotalExpectation

/-! ## Test section: two-cell singleton partition of `Fin 2` with counting measure.

Total integral `4`, cell masses `1, 1`, conditional means `1, 3`.
-/

theorem test_measSet (i : Fin 2) : MeasurableSet ({i} : Set (Fin 2)) :=
  measurableSet_singleton i

theorem test_disj :
    Pairwise (Function.onFun Disjoint fun i : Fin 2 => ({i} : Set (Fin 2))) := by
  intro i j hne
  exact Set.disjoint_singleton.mpr hne

theorem test_cover : ⋃ (i : Fin 2), ({i} : Set (Fin 2)) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ]
  exact iff_true_intro ⟨x, rfl⟩

theorem test_int_fin2 :
    Integrable (![1, 3] : Fin 2 → ℝ) (Measure.count : Measure (Fin 2)) := by
  refine Integrable.of_bound ?_ 3 ?_
  · exact (measurable_of_countable _).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    fin_cases x <;> simp

theorem test_total_fin2 :
    ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2)) = 4 := by
  rw [integral_count, Fin.sum_univ_two]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem test_mass_fin2 (i : Fin 2) :
    (Measure.count : Measure (Fin 2)).real {i} = 1 := by
  show ((Measure.count : Measure (Fin 2)) {i}).toReal = 1
  rw [Measure.count_singleton]
  exact ENNReal.toReal_one

theorem test_condmean_fin2 (i : Fin 2) :
    ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))[|{i}]
      = (![1, 3] : Fin 2 → ℝ) i := by
  have hcond : ∀ s : Set (Fin 2),
      (Measure.count : Measure (Fin 2))[|s]
        = ((Measure.count : Measure (Fin 2)) s)⁻¹
          • (Measure.count : Measure (Fin 2)).restrict s :=
    fun s => rfl
  rw [hcond, Measure.count_singleton, inv_one, one_smul, Measure.restrict_singleton,
    Measure.count_singleton, one_smul]
  exact integral_dirac _ _

theorem test_sum_fin2 :
    ∑ i : Fin 2, (Measure.count : Measure (Fin 2)).real {i}
        * ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))[|{i}] = 4 := by
  rw [Fin.sum_univ_two, test_mass_fin2 0, test_condmean_fin2 0, test_mass_fin2 1,
    test_condmean_fin2 1]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem test_partition_fin2 :
    ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))
      = ∑ i : Fin 2, (Measure.count : Measure (Fin 2)).real {i}
        * ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))[|{i}] :=
  integral_eq_sum_measureReal_mul_integral_cond_partition
    (B := fun i : Fin 2 => ({i} : Set (Fin 2)))
    test_measSet test_disj test_cover test_int_fin2

theorem test_fiberfib_fin2 (x : Fin 2) : id ⁻¹' ({x} : Set (Fin 2)) = {x} := rfl

theorem test_fiber_fin2 :
    ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))
      = ∑ x : Fin 2, (Measure.count : Measure (Fin 2)).real (id ⁻¹' {x})
        * ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))[|id ← x] :=
  integral_eq_sum_measureReal_mul_integral_cond_fiber measurable_id test_int_fin2

theorem test_fibersum_fin2 :
    ∑ x : Fin 2, (Measure.count : Measure (Fin 2)).real (id ⁻¹' {x})
        * ∫ ω, (![1, 3] : Fin 2 → ℝ) ω ∂(Measure.count : Measure (Fin 2))[|id ← x] = 4 := by
  simp only [test_fiberfib_fin2]
  exact test_sum_fin2

end MathlibExtTest.Probability.TotalExpectation
