/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.AWGNCapacityValue

@[expose] public section

open MathlibExt.InformationTheory.AWGNCapacityValue MeasureTheory ProbabilityTheory
  InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.AWGNCapacityValue

/-- `P = 0` gives capacity `0` for any noise variance, with no hypothesis. -/
example : awgnCapacity 0 3 = 0 :=
  awgnCapacity_zero_power 3

/-- The headline at `P = 0` with both hypotheses discharged: the converse from the zero-power
value, Gaussian attainment vacuously. -/
example (N : ℝ≥0) (hN : 0 < N) :
    awgnCapacity 0 N = ENNReal.ofReal (Real.log (1 + 0 / N) / (2 * Real.log 2)) := by
  refine awgnCapacity_eq le_rfl hN (fun p hp => ?_) (fun h => absurd h (lt_irrefl 0))
  have h := le_powerCapacity (awgnKernel N) hp
  rw [powerCapacity_zero] at h
  exact h.trans bot_le

/-- `P = N` gives `1 / 2` bit, with the converse and Gaussian attainment supplied. -/
example (hconv : ∀ p ∈ inputFeasible ((2 : ℝ≥0) : ℝ),
      measureMutualInformation (channelJoint (awgnKernel 2) p) ≤
        ENNReal.ofReal (Real.log (1 + ((2 : ℝ≥0) : ℝ) / (2 : ℝ≥0)) / (2 * Real.log 2)))
    (hgauss : 0 < ((2 : ℝ≥0) : ℝ) → measureMutualInformation (channelJoint (awgnKernel 2)
        (gaussianInput ((2 : ℝ≥0) : ℝ))) =
      ENNReal.ofReal (Real.log (1 + ((2 : ℝ≥0) : ℝ) / (2 : ℝ≥0)) / (2 * Real.log 2))) :
    awgnCapacity ((2 : ℝ≥0) : ℝ) 2 = ENNReal.ofReal (1 / 2) :=
  awgnCapacity_self two_pos hconv hgauss

/-- `P = N` gives `1 / 2` bit from the converse alone: Gaussian attainment is proved. -/
example (N : ℝ≥0) (hN : 0 < N)
    (hconv : ∀ p ∈ inputFeasible N, measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + (N : ℝ) / N) / (2 * Real.log 2))) :
    awgnCapacity N N = ENNReal.ofReal (1 / 2) :=
  awgnCapacity_self hN hconv fun _ =>
    measureMutualInformation_channelJoint_gaussianInput (NNReal.coe_nonneg N) hN

/-- At signal-to-noise ratio `1` the Gaussian input carries exactly `1 / 2` bit, unconditionally. -/
example : measureMutualInformation (channelJoint (awgnKernel 1) (gaussianInput 1)) =
    ENNReal.ofReal (1 / 2) := by
  rw [measureMutualInformation_channelJoint_gaussianInput zero_le_one one_pos]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  congr 1
  norm_num
  field_simp

/-- At signal-to-noise ratio `3` the capacity is `1` bit, with no hypothesis. -/
example (N : ℝ≥0) (hN : 0 < N) : awgnCapacity (3 * N) N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hN)
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  rw [awgnCapacity_eq_ofReal_log (by positivity) hN, ← ENNReal.ofReal_one]
  congr 1
  rw [show 1 + 3 * (N : ℝ) / N = 2 ^ 2 by field_simp; ring, Real.log_pow]
  push_cast
  field_simp

/-- The converse on input laws, with no hypothesis: the antipodal law at `±2`, which is not
Gaussian, carries at most `1 / 2` bit through the channel of noise variance `4`. -/
example : measureMutualInformation (channelJoint (awgnKernel 4) (antipodalLaw (Real.sqrt 4))) ≤
    ENNReal.ofReal (1 / 2) := by
  refine (measureMutualInformation_channelJoint_le (by norm_num)
    (antipodalLaw_mem_inputFeasible (by norm_num : (0 : ℝ) ≤ 4))).trans_eq ?_
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  congr 1
  norm_num
  field_simp

/-- The assembly hypotheses are jointly satisfiable with a nonempty feasible set at `P = 1`: for
the useless channel `κ x = N(0, 1)` every input carries zero information. -/
example : powerCapacity (Kernel.const ℝ (gaussianReal 0 1)) 1 = 0 := by
  have hmi : ∀ p : ProbabilityMeasure ℝ,
      measureMutualInformation (channelJoint (Kernel.const ℝ (gaussianReal 0 1)) p) = 0 := by
    intro p
    unfold measureMutualInformation channelJoint
    change klDiv ((p : Measure ℝ) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1))
      ((((p : Measure ℝ) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1)).map Prod.fst).prod
        (((p : Measure ℝ) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1)).map Prod.snd)) /
          ENNReal.ofReal (Real.log 2) = 0
    rw [Measure.compProd_const, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
      measure_univ, one_smul, one_smul, klDiv_self, ENNReal.zero_div]
  exact powerCapacity_eq_of_le_of_attains _ (fun p _ => (hmi p).le)
    (gaussianInput_mem_inputFeasible zero_le_one) (hmi _)

/-- `P ≥ 0` is necessary: at `P = -3N` both hypotheses hold vacuously but the conclusion fails. -/
example (N : ℝ≥0) (hN : 0 < N) :
    (∀ p ∈ inputFeasible (-3 * N), measureMutualInformation (channelJoint (awgnKernel N) p) ≤
      ENNReal.ofReal (Real.log (1 + (-3 * N : ℝ) / N) / (2 * Real.log 2))) ∧
    (0 < (-3 * N : ℝ) → measureMutualInformation (channelJoint (awgnKernel N)
        (gaussianInput (-3 * N))) =
      ENNReal.ofReal (Real.log (1 + (-3 * N : ℝ) / N) / (2 * Real.log 2))) ∧
    awgnCapacity (-3 * N) N ≠
      ENNReal.ofReal (Real.log (1 + (-3 * N : ℝ) / N) / (2 * Real.log 2)) := by
  have hneg : -3 * (N : ℝ) < 0 := by
    have : (0 : ℝ) < N := NNReal.coe_pos.mpr hN
    linarith
  obtain ⟨h0, hv⟩ := awgnCapacity_neg_power_ne hN
  refine ⟨fun p hp => ?_, fun h => absurd h (not_lt.mpr hneg.le), ?_⟩
  · rw [inputFeasible_eq_empty_of_neg hneg] at hp
    exact absurd hp (Set.notMem_empty p)
  · rw [h0, hv]
    exact (ENNReal.ofReal_pos.mpr (by norm_num)).ne

/-- The converse hypothesis fails for the noiseless channel, so `N > 0` enters through it. -/
example : ¬ (∀ p ∈ inputFeasible 1, measureMutualInformation (channelJoint (awgnKernel 0) p) ≤
      ENNReal.ofReal (Real.log (1 + 1 / ((0 : ℝ≥0) : ℝ)) / (2 * Real.log 2))) := by
  intro hconv
  exact awgnCapacity_ne_top hconv (awgnCapacity_noiseless one_pos).1

/-- A nonzero constant input is feasible and carries zero information; the antipodal law is
feasible. -/
example : diracInput 2 ∈ inputFeasible 4 ∧
    measureMutualInformation (channelJoint (awgnKernel 1) (diracInput 2)) = 0 ∧
    antipodalLaw (Real.sqrt 4) ∈ inputFeasible 4 :=
  ⟨diracInput_mem_inputFeasible (by norm_num),
    measureMutualInformation_channelJoint_dirac _ 2,
    antipodalLaw_mem_inputFeasible (by norm_num)⟩

end MathlibExtTest.InformationTheory.AWGNCapacityValue
