/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-! # Binary symmetric channel capacity computation

For the binary symmetric channel with crossover `δ` and uniform
input, the input-output mutual information (in bits, via the
repository's `InformationTheory.finiteMutualInformation`) is
`1 - h δ / log 2`, where `h` is Mathlib's binary entropy function
`Real.binEntropy` (in nats). Equivalently, in nats, it is
`log 2 - h δ`. This is the BSC case of roadmap package QCI-34 of
the Atlas TCS canon roadmap.

Source: Cover and Thomas, Elements of Information Theory (2006),
Section 7.1.
-/

namespace InformationTheory

open Finset
open scoped ENNReal

/-- The joint law of input and output of the binary symmetric
channel with crossover probability `δ ≤ 1` under input PMF `p`. -/
noncomputable def bscJoint (δ : ℝ≥0∞) (hδ : δ ≤ 1) (p : PMF (Fin 2)) :
    PMF (Fin 2 × Fin 2) :=
  p.bind fun x => (PMF.ofFintype
    (fun y => if y = x then 1 - δ else δ) (by
      fin_cases x <;> simp [Finset.sum] <;>
        (first | exact tsub_add_cancel_of_le hδ |
          rw [add_comm]; exact tsub_add_cancel_of_le hδ))).map fun y => (x, y)

private theorem uniformFin2_apply (x : Fin 2) :
    (PMF.uniformFintype (Fin 2)) x = (1 / 2 : ℝ≥0∞) := by
  simp [PMF.uniformFintype_apply]

/-- Joint probabilities of the BSC with uniform input. -/
theorem bscJoint_apply_uniform {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x y : Fin 2) :
    (bscJoint δ hδ (PMF.uniformFintype (Fin 2))) (x, y) =
      (1 / 2) * (if y = x then 1 - δ else δ) := by
  simp only [bscJoint, PMF.bind_apply, PMF.map_apply, PMF.ofFintype_apply,
    uniformFin2_apply, PMF.ofFintype_apply]
  rw [tsum_fintype, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> simp [tsum_fintype]

private theorem toReal_sub_one {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    (1 - δ).toReal = 1 - δ.toReal := by
  rw [ENNReal.toReal_sub_of_le hδ ENNReal.one_ne_top, ENNReal.toReal_one]

private theorem joint_toReal {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x y : Fin 2) :
    ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))) (x, y)).toReal =
      (1 / 2 : ℝ) * (if y = x then 1 - δ.toReal else δ.toReal) := by
  rw [bscJoint_apply_uniform hδ x y, ENNReal.toReal_mul]
  have hhalf : ((1 / 2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by simp
  rw [hhalf, apply_ite ENNReal.toReal, toReal_sub_one hδ]

private theorem margX {δ : ℝ≥0∞} (hδ : δ ≤ 1) (x : Fin 2) :
    (∑ y, ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))) (x, y)).toReal) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  rw [joint_toReal hδ x 0, joint_toReal hδ x 1]
  fin_cases x <;> simp <;> ring

private theorem margY {δ : ℝ≥0∞} (hδ : δ ≤ 1) (y : Fin 2) :
    (∑ x, ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))) (x, y)).toReal) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  rw [joint_toReal hδ 0 y, joint_toReal hδ 1 y]
  fin_cases y <;> simp <;> ring

private theorem negMulLog_half : Real.negMulLog (1 / 2 : ℝ) = (1 / 2) * Real.log 2 := by
  rw [Real.negMulLog, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

private theorem shannonEntropy_marginals {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    shannonEntropy ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))).map Prod.fst) = 1 ∧
      shannonEntropy ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))).map Prod.snd) = 1 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hfst : ∀ x : Fin 2,
      (((bscJoint δ hδ (PMF.uniformFintype (Fin 2))).map Prod.fst) x).toReal = 1 / 2 := by
    intro x
    rw [toReal_map_fst_apply, margX hδ x]
  have hsnd : ∀ y : Fin 2,
      (((bscJoint δ hδ (PMF.uniformFintype (Fin 2))).map Prod.snd) y).toReal = 1 / 2 := by
    intro y
    rw [toReal_map_snd_apply, margY hδ y]
  refine ⟨?_, ?_⟩
  · unfold shannonEntropy
    simp only [hfst]
    rw [Fin.sum_univ_two, negMulLog_half]
    field_simp
    ring
  · unfold shannonEntropy
    simp only [hsnd]
    rw [Fin.sum_univ_two, negMulLog_half]
    field_simp
    ring

private theorem shannonEntropy_joint {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    shannonEntropy (bscJoint δ hδ (PMF.uniformFintype (Fin 2))) =
      (Real.log 2 + Real.binEntropy δ.toReal) / Real.log 2 := by
  have hsum : ∑ a : Fin 2 × Fin 2,
      Real.negMulLog ((bscJoint δ hδ (PMF.uniformFintype (Fin 2))) a).toReal =
        Real.log 2 + Real.binEntropy δ.toReal := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [joint_toReal hδ 0 0, joint_toReal hδ 0 1, joint_toReal hδ 1 0, joint_toReal hδ 1 1]
    simp only [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide,
      ite_true, ite_false]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_mul, negMulLog_half]
    ring
  unfold shannonEntropy
  rw [hsum]

/-- Binary symmetric channel with uniform input: the mutual
information between input and output, in bits, is
`1 - h δ / log 2`. -/
theorem bsc_finiteMutualInformation_uniform {δ : ℝ≥0∞} (hδ : δ ≤ 1) :
    finiteMutualInformation (bscJoint δ hδ (PMF.uniformFintype (Fin 2))) =
      1 - Real.binEntropy δ.toReal / Real.log 2 := by
  obtain ⟨hX, hY⟩ := shannonEntropy_marginals hδ
  rw [finiteMutualInformation_eq, hX, hY, shannonEntropy_joint hδ]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp
  ring

end InformationTheory
