/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Factorial
public import MathlibExt.Probability.Causality.CausalIdentification
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tests for 2x2 factorial unbiasedness

Nonadditive and additive population fixtures, normalization of the cell-assignment law
and its zero-measure behavior on infeasible margins, the one-unit-per-cell use case, and the
empty-cell-size exclusion.
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Statistics.Experiment

open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

-- Test-local verbatim copies of production-private helpers, kept private
-- per the body (the production file owns the canonical versions).

/-- The per-unit categorical law is a probability measure under nonnegativity and
per-unit normalization. -/
private theorem isProbabilityMeasure_bernoulliCell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : ι → Fin 4 → ℝ) (i : ι)
    (hnn : ∀ i c, 0 ≤ π i c) (hnorm : ∀ i, ∑ c, π i c = 1) :
    IsProbabilityMeasure (bernoulliCell π i) := by
  constructor
  rw [bernoulliCell, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hnn i c), hnorm i,
    ENNReal.ofReal_one]

/-- The IPW cell mean as a sum of single-unit contributions. -/
private theorem ipwCellMean_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ι → ℝ) (π : ι → Fin 4 → ℝ) (c : Fin 4) (f : ι → Fin 4) :
    ipwCellMean Y π c f =
      ∑ i, (if f i = c then Y i / ((Fintype.card ι : ℝ) * π i c) else 0) := by
  rw [ipwCellMean, Finset.sum_filter]


theorem popMean_const_fin4 (c : ℝ) : popMean (fun _ : Fin 4 => c) = c := by
  unfold popMean
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Normalization: each main effect is a difference of two arm averages. -/
example (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) :
    mainEffectA m₀₀ m₀₁ m₁₀ m₁₁ = (m₁₀ + m₁₁) / 2 - (m₀₀ + m₀₁) / 2 ∧
      mainEffectB m₀₀ m₀₁ m₁₀ m₁₁ = (m₀₁ + m₁₁) / 2 - (m₀₀ + m₁₀) / 2 :=
  ⟨by unfold mainEffectA; ring, by unfold mainEffectB; ring⟩

/-- Normalization: twice the interaction is the unhalved difference-in-differences. -/
example (m₀₀ m₀₁ m₁₀ m₁₁ : ℝ) :
    2 * interactionAB m₀₀ m₀₁ m₁₀ m₁₁ = (m₁₁ - m₀₁) - (m₁₀ - m₀₀) := by
  unfold interactionAB
  ring

/-- Nonadditive population fixture: constant surfaces `1, 0, 0, 1` give
population main effects `0` and interaction `1`. -/
example : mainEffectA (popMean (fun _ : Fin 4 => (1 : ℝ)))
    (popMean (fun _ : Fin 4 => (0 : ℝ))) (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) = 0 := by
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

example : interactionAB (popMean (fun _ : Fin 4 => (1 : ℝ)))
    (popMean (fun _ : Fin 4 => (0 : ℝ))) (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) = 1 := by
  simp only [popMean_const_fin4, interactionAB]
  norm_num

/-- Additive population fixture: constant surfaces `0, 1, 2, 3` give
interaction `0` while the main effects recover the additive shifts. -/
example : interactionAB (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) (popMean (fun _ : Fin 4 => (2 : ℝ)))
    (popMean (fun _ : Fin 4 => (3 : ℝ))) = 0 := by
  simp only [popMean_const_fin4, interactionAB]
  norm_num

example : mainEffectA (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) (popMean (fun _ : Fin 4 => (2 : ℝ)))
    (popMean (fun _ : Fin 4 => (3 : ℝ))) = 2 := by
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

/-- Normalization: with one unit per cell the cell-assignment law is a probability measure. -/
example : IsProbabilityMeasure (cellAssignment (ι := Fin 4) fun _ => 1) :=
  isProbabilityMeasure_cellAssignment (Fin 4) (fun _ => 1) (fun _ => one_pos) (by decide)

/-- Infeasible margins: no assignment of four units puts two units in every cell, so the
cell-assignment law is the zero measure. -/
example : cellAssignment (ι := Fin 4) (fun _ => 2) = 0 := by
  have hempty : cellAssignSpace (ι := Fin 4) (fun _ => 2) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun f hf => ?_
    simp only [cellAssignSpace, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
      (t := Finset.univ) fun x _ => Finset.mem_univ (f x)
    simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    omega
  rw [cellAssignment_eq, hempty]
  simp [Measure.uniformOfFinset]

/-- Use case: one unit per cell, the per-cell unbiasedness instance. -/
example (y : Fin 4 → ℝ) :
    ∫ f, factorialCellMean y 0 f ∂(cellAssignment fun _ => 1) =
      popMean y := by
  exact integral_factorialCellMean y 0 (fun _ => 1) (fun _ => one_pos) (by decide)

/-- Negative: the all-ones-except-cell-zero size function violates the
positivity hypothesis, so unbiasedness is not claimed for it. -/
example : ¬ ∀ c, 0 < (![0, 1, 1, 1] : Fin 4 → ℕ) c := by
  intro h
  have h0 := h 0
  simp at h0

/-- Main-effect A unbiasedness applied to the constant nonadditive fixture
(effect `0`). -/
example : (∫ f, mainEffectA (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 0 := by
  rw [integral_mainEffectA _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

/-- Main-effect B unbiasedness applied to the constant additive fixture
(effect `1`). -/
example : (∫ f, mainEffectB (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (2 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (3 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 1 := by
  rw [integral_mainEffectB _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, mainEffectB]
  norm_num

/-- Interaction unbiasedness applied to the constant nonadditive fixture
(interaction `1`). -/
example : (∫ f, interactionAB (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 1 := by
  rw [integral_interactionAB _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, interactionAB]
  norm_num

/-- Empty realized cell: on `Fin 2` with uniform cell probabilities, the
assignment sending both units to cell `0` leaves cell `1` empty, yet the
expectation identity for cell `1` holds. -/
example (Y : Fin 2 → ℝ) :
    ∫ f, ipwCellMean Y (fun _ _ => (1 / 4 : ℝ)) 1 f
      ∂(Measure.pi fun i : Fin 2 =>
        bernoulliCell (fun _ _ => (1 / 4 : ℝ)) i) =
      popMean Y := by
  have hpos : ∀ (i : Fin 2) (c : Fin 4), 0 < (fun _ _ => (1 / 4 : ℝ)) i c :=
    fun _ _ => by norm_num
  have hnorm : ∀ i : Fin 2, ∑ c : Fin 4, (fun _ _ => (1 / 4 : ℝ)) i c = 1 := by
    intro i
    norm_num [Fin.sum_univ_four]
  have hN : 0 < Fintype.card (Fin 2) := by simp
  exact integral_ipwCellMean Y (fun _ _ => (1 / 4 : ℝ)) hpos hnorm hN 1

/-- The empty cell is realized: the constant assignment `fun _ => 0` has
positive probability under the joint law above, so the boundary is
non-vacuous. -/
example :
    (Measure.pi fun i : Fin 2 =>
      bernoulliCell (fun _ _ => (1 / 4 : ℝ)) i) {(fun _ => (0 : Fin 4))} > 0 := by
  have hpos : ∀ (i : Fin 2) (c : Fin 4), 0 < (fun _ _ => (1 / 4 : ℝ)) i c :=
    fun _ _ => by norm_num
  have hnorm : ∀ i : Fin 2, ∑ c : Fin 4, (fun _ _ => (1 / 4 : ℝ)) i c = 1 := by
    intro i
    norm_num [Fin.sum_univ_four]
  have _hprob : ∀ i : Fin 2,
      IsProbabilityMeasure (bernoulliCell (fun _ _ => (1 / 4 : ℝ)) i) :=
    fun i => isProbabilityMeasure_bernoulliCell (fun _ _ => (1 / 4 : ℝ)) i
      (fun i c => le_of_lt (hpos i c)) hnorm
  have hfactor : ∀ (i : Fin 2) (a : Fin 4),
      0 < (bernoulliCell (fun _ _ => (1 / 4 : ℝ)) i) {a} := by
    intro i a
    rw [bernoulliCell, Measure.finsetSum_apply]
    simp only [Measure.smul_apply]
    have hnn : ∀ c ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ (ENNReal.ofReal ((fun _ _ => (1 / 4 : ℝ)) i c)) • (Measure.dirac c {a}) :=
      fun c _ => zero_le
    have hle := Finset.single_le_sum hnn (Finset.mem_univ a)
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton a)] at hle
    have hpos' : 0 < (ENNReal.ofReal ((fun _ _ => (1 / 4 : ℝ)) i a)) • (1 : ENNReal) := by
      show 0 < (ENNReal.ofReal (1 / 4 : ℝ)) • (1 : ENNReal)
      rw [smul_eq_mul, mul_one]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact lt_of_lt_of_le hpos' hle
  have hset : ({fun _ => (0 : Fin 4)} : Set (Fin 2 → Fin 4))
      = Set.pi Set.univ (fun i : Fin 2 => ({((fun _ => (0 : Fin 4)) i)} : Set (Fin 4))) := by
    ext f
    simp only [Set.mem_singleton_iff, Set.mem_pi]
    constructor
    · intro h i _
      rw [h]
    · intro h
      funext i
      exact Set.mem_singleton_iff.mp (h i (Set.mem_univ i))
  rw [hset, Measure.pi_pi, Fin.prod_univ_two, gt_iff_lt]
  exact ENNReal.mul_pos (pos_iff_ne_zero.mp (hfactor 0 _))
    (pos_iff_ne_zero.mp (hfactor 1 _))

/-- Positivity counterexample: with `π 0 0 = 0` while unit `0` carries a
nonzero outcome, the IPW cell mean is biased for the population cell mean.
The pinned statement is that the unbiasedness conclusion fails, i.e. the
integral differs from `popMean`. -/
example (Y : Fin 2 → ℝ) (hY : Y 0 = 2 ∧ Y 1 = 0) :
    ∫ f, ipwCellMean Y
      (![![0, 1 / 2, 1 / 4, 1 / 4], ![1 / 4, 1 / 4, 1 / 4, 1 / 4]] :
        Fin 2 → Fin 4 → ℝ) 0 f
      ∂(Measure.pi fun i =>
        bernoulliCell (![![0, 1 / 2, 1 / 4, 1 / 4],
          ![1 / 4, 1 / 4, 1 / 4, 1 / 4]] : Fin 2 → Fin 4 → ℝ) i) ≠
      popMean Y := by
  set M : Fin 2 → Fin 4 → ℝ :=
    (![![0, 1 / 2, 1 / 4, 1 / 4], ![1 / 4, 1 / 4, 1 / 4, 1 / 4]] :
      Fin 2 → Fin 4 → ℝ) with hM
  have hM00 : M 0 0 = 0 := by
    simp [hM, Matrix.cons_val_zero]
  have hnorm : ∀ i : Fin 2, ∑ c : Fin 4, M i c = 1 := by
    intro i
    fin_cases i
    · norm_num [hM, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one]
    · norm_num [hM, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hnn : ∀ (i : Fin 2) (c : Fin 4), 0 ≤ M i c := by
    intro i c
    fin_cases i <;> fin_cases c <;>
      norm_num [hM, Matrix.cons_val_zero, Matrix.cons_val_one]
  have _hprobM : ∀ i : Fin 2, IsProbabilityMeasure (bernoulliCell M i) :=
    fun i => isProbabilityMeasure_bernoulliCell M i hnn hnorm
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      Integrable (fun f : Fin 2 → Fin 4 =>
        if f i = 0 then Y i / ((Fintype.card (Fin 2) : ℝ) * M i 0) else 0)
        (Measure.pi fun i => bernoulliCell M i) := by
    intro i _
    exact integrable_comp_eval (μ := fun j => bernoulliCell M j) (i := i)
      (f := fun a => if a = 0 then Y i / ((Fintype.card (Fin 2) : ℝ) * M i 0) else 0)
      (Integrable.of_finite)
  have hfun0 : (fun a : Fin 4 =>
      if a = 0 then Y 0 / ((Fintype.card (Fin 2) : ℝ) * M 0 0) else 0) = 0 := by
    funext a
    by_cases ha : a = 0
    · simp [ha, hY.1, hM00]
    · simp [ha]
  have hfun1 : (fun a : Fin 4 =>
      if a = 0 then Y 1 / ((Fintype.card (Fin 2) : ℝ) * M 1 0) else 0) = 0 := by
    funext a
    by_cases ha : a = 0
    · simp [ha, hY.2]
    · simp [ha]
  have hTerm0 : (∫ f, (if f 0 = 0 then Y 0 / ((Fintype.card (Fin 2) : ℝ) * M 0 0) else 0)
      ∂(Measure.pi fun i => bernoulliCell M i)) = 0 := by
    have hcomp := integral_comp_eval (μ := fun j => bernoulliCell M j) (i := 0)
      (f := fun a => if a = 0 then Y 0 / ((Fintype.card (Fin 2) : ℝ) * M 0 0) else 0)
      (Measurable.of_discrete.aestronglyMeasurable)
    have hzero : (∫ a, (if a = 0 then Y 0 / ((Fintype.card (Fin 2) : ℝ) * M 0 0) else 0)
        ∂(bernoulliCell M 0)) = 0 := by
      rw [hfun0]
      simp
    exact hcomp.trans hzero
  have hTerm1 : (∫ f, (if f 1 = 0 then Y 1 / ((Fintype.card (Fin 2) : ℝ) * M 1 0) else 0)
      ∂(Measure.pi fun i => bernoulliCell M i)) = 0 := by
    have hcomp := integral_comp_eval (μ := fun j => bernoulliCell M j) (i := 1)
      (f := fun a => if a = 0 then Y 1 / ((Fintype.card (Fin 2) : ℝ) * M 1 0) else 0)
      (Measurable.of_discrete.aestronglyMeasurable)
    have hzero : (∫ a, (if a = 0 then Y 1 / ((Fintype.card (Fin 2) : ℝ) * M 1 0) else 0)
        ∂(bernoulliCell M 1)) = 0 := by
      rw [hfun1]
      simp
    exact hcomp.trans hzero
  have hLHS : (∫ f, ipwCellMean Y M 0 f ∂(Measure.pi fun i => bernoulliCell M i)) = 0 := by
    simp only [ipwCellMean_eq_sum]
    rw [integral_finsetSum Finset.univ hInt]
    simp only [Fin.sum_univ_two, hTerm0, hTerm1, add_zero]
  have hRHS : popMean Y = 1 := by
    unfold popMean
    simp only [Fin.sum_univ_two, Fintype.card_fin, hY.1, hY.2]
    norm_num
  rw [hLHS, hRHS]
  norm_num

end MathlibExtTest.Probability.Statistics.Experiment
