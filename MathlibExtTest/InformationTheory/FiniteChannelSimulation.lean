/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

public import MathlibExt.InformationTheory.FiniteChannelSimulation
public import MathlibExt.InformationTheory.FunctionalRepresentation
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Actual-law channel-simulation tests

The deterministic case exercises the infimum and its information-slice supremum.
The correlated fair-bit case distinguishes admissible singleton randomness from
an auxiliary carrying the input itself.
-/

@[expose] public section

namespace MathlibExtTest.InformationTheory

open _root_.InformationTheory MeasureTheory

/-- An actual singleton joint PMF. -/
noncomputable abbrev deterministicLaw : FiniteJointLaw :=
  ⟨1, 1, by decide, by decide, PMF.pure (0, 0)⟩

/-- An actual deterministic extension with the required XY marginal. -/
noncomputable abbrev deterministicExtension : FiniteExtension deterministicLaw :=
  ⟨1, by decide, PMF.pure ((0, 0), 0), by simp [deterministicLaw, PMF.pure_map]⟩

/-- The actual singleton joint PMF has zero information. -/
theorem deterministicLaw_information : deterministicLaw.mutualInformation = 0 := by
  simp [FiniteJointLaw.mutualInformation, FiniteJointLaw.inputLaw,
    FiniteJointLaw.outputLaw, deterministicLaw, PMF.pure_map]

/-- The actual fixed-law optimizer is attained at zero for a singleton output. -/
theorem deterministicLaw_optimum : conditionalPrefixOptimum deterministicLaw = 0 := by
  exact conditionalPrefixOptimum_eq_zero_of_output_subsingleton deterministicLaw

/-- This actual law inhabits the zero-information slice of the global supremum. -/
theorem zero_le_worstCaseOptimum_zero : (0 : EReal) ≤ worstCaseOptimum 0 := by
  simpa only [deterministicLaw_information, deterministicLaw_optimum] using
    conditionalPrefixOptimum_le_worstCaseOptimum deterministicLaw

/-- An actual fair bit copied into both coordinates. -/
noncomputable def binaryCopyLaw : FiniteJointLaw :=
  ⟨2, 2, by decide, by decide,
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))⟩

/-- The copied fair-bit law has the actual fair-bit input marginal. -/
theorem binaryCopyLaw_input : binaryCopyLaw.inputLaw = Cslib.Probability.PMF.uniformOfFintype (Fin 2) := by
  change ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map Prod.fst = _
  rw [PMF.map_comp]
  exact PMF.map_id _

/-- The copied fair-bit law has the actual fair-bit output marginal. -/
theorem binaryCopyLaw_output : binaryCopyLaw.outputLaw = Cslib.Probability.PMF.uniformOfFintype (Fin 2) := by
  change ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map Prod.snd = _
  rw [PMF.map_comp]
  exact PMF.map_id _

/-- The actual fair-bit Shannon sum is one bit. -/
theorem fairBitEntropy : shannonEntropy (Cslib.Probability.PMF.uniformOfFintype (Fin 2)) = 1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [shannonEntropy, Cslib.Probability.PMF.uniformOfFintype_apply, Fin.sum_univ_two,
    Real.negMulLog, Real.log_div, hlog]
  field_simp [hlog]

/-- Copying a fair bit does not create additional joint entropy. -/
theorem binaryCopyLaw_entropy : shannonEntropy binaryCopyLaw.law = 1 := by
  change shannonEntropy ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))) = 1
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [shannonEntropy, PMF.map_apply, Cslib.Probability.PMF.uniformOfFintype_apply,
    tsum_fintype, Fintype.sum_prod_type, Fin.sum_univ_two,
    Real.negMulLog, Real.log_div, hlog]
  field_simp [hlog]
  norm_num

/-- The input coordinate of the actual copied bit has one bit of entropy. -/
theorem binaryCopyLaw_inputEntropy : shannonEntropy binaryCopyLaw.inputLaw = 1 := by
  change shannonEntropy (((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map
    Prod.fst) = 1
  rw [PMF.map_comp]
  change shannonEntropy ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map id) = 1
  rw [PMF.map_id]
  exact fairBitEntropy

/-- The output coordinate of the actual copied bit has one bit of entropy. -/
theorem binaryCopyLaw_outputEntropy : shannonEntropy binaryCopyLaw.outputLaw = 1 := by
  change shannonEntropy (((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map
    Prod.snd) = 1
  rw [PMF.map_comp]
  change shannonEntropy ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map id) = 1
  rw [PMF.map_id]
  exact fairBitEntropy

/-- The actual copied fair bit has one bit of mutual information. -/
theorem binaryCopyLaw_information : binaryCopyLaw.mutualInformation = 1 := by
  unfold FiniteJointLaw.mutualInformation
  rw [binaryCopyLaw_inputEntropy, binaryCopyLaw_outputEntropy, binaryCopyLaw_entropy]
  norm_num

/-- An actual extension whose auxiliary is the input, not independent randomness. -/
noncomputable def correlatedAuxiliary : FiniteExtension binaryCopyLaw where
  ns := 2
  ns_pos := by decide
  law := binaryCopyLaw.law.map (fun z => (z, z.1))
  marginal_eq := by
    rw [PMF.map_comp]
    exact PMF.map_id _

/-- The correlated auxiliary carries one actual bit. -/
theorem correlatedAuxiliary_entropy : shannonEntropy correlatedAuxiliary.auxiliaryLaw = 1 := by
  change shannonEntropy ((((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map
    (fun z => (z, z.1))).map Prod.snd) = 1
  rw [PMF.map_comp, PMF.map_comp]
  change shannonEntropy ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map id) = 1
  rw [PMF.map_id]
  exact fairBitEntropy

/-- The correlated input/auxiliary pair has the entropy of the original copied bit. -/
theorem correlatedAuxiliary_inputEntropy :
    shannonEntropy correlatedAuxiliary.inputAuxiliaryLaw = 1 := by
  change shannonEntropy ((((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (fun b => (b, b))).map
    (fun z => (z, z.1))).map (fun z => (z.1.1, z.2))) = 1
  rw [PMF.map_comp, PMF.map_comp]
  exact binaryCopyLaw_entropy

/-- This actual auxiliary violates the zero-information admissibility condition. -/
theorem correlatedAuxiliary_information : correlatedAuxiliary.auxiliaryInformation = 1 := by
  unfold FiniteExtension.auxiliaryInformation
  rw [binaryCopyLaw_inputEntropy, correlatedAuxiliary_entropy,
    correlatedAuxiliary_inputEntropy]
  norm_num

/-- An actual nontrivial probability measure for the general Shannon tests. -/
noncomputable def fairBitProbability : ProbabilityMeasure (Fin 2) :=
  ⟨(Cslib.Probability.PMF.uniformOfFintype (Fin 2)).toMeasure, inferInstance⟩

/-- The nonconstant measurable fair-bit observation has one bit without conditioning. -/
theorem fairBitQuantizedEntropy :
    quantizedConditionalEntropy fairBitProbability ⟨⊥, bot_le⟩ id measurable_id = 1 := by
  classical
  have hi (i : Fin 2) : Integrable (fun z : Fin 2 => if z = i then (1 : ℝ) else 0)
      fairBitProbability.toMeasure := by
    have h : (fun z : Fin 2 => if z = i then (1 : ℝ) else 0) =
        ({i} : Set (Fin 2)).indicator (fun _ => (1 : ℝ)) := by
      funext z
      simp only [Set.indicator_apply, Set.mem_singleton_iff]
    rw [h]
    exact (integrable_const (μ := fairBitProbability.toMeasure) (1 : ℝ)).indicator
      (MeasurableSet.singleton i)
  have hmass (i : Fin 2) :
      (∫ z, (if z = i then (1 : ℝ) else 0) ∂fairBitProbability.toMeasure) = 1 / 2 := by
    rw [integral_fintype (hi i)]
    simp [Measure.real, fairBitProbability, Cslib.Probability.PMF.uniformOfFintype_apply, smul_eq_mul]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [quantizedConditionalEntropy, condExp_bot, hmass, Fin.sum_univ_two,
    Real.negMulLog, Real.log_div, hlog]
  field_simp [hlog]

/-- Identity quantization gives the actual fair-bit Shannon supremum at least one bit. -/
theorem fairBitShannonEntropy_ge_one :
    (1 : ENNReal) ≤ conditionalShannonEntropy fairBitProbability ⟨⊥, bot_le⟩ id
      measurable_id := by
  apply le_sSup
  refine ⟨2, id, measurable_id, ?_⟩
  norm_num [Function.comp_def, fairBitQuantizedEntropy]

example : deterministicExtension.auxiliaryInformation = 0 := by
  simp [FiniteExtension.auxiliaryInformation, FiniteExtension.auxiliaryLaw,
    FiniteExtension.inputAuxiliaryLaw, FiniteJointLaw.inputLaw,
    deterministicExtension, deterministicLaw, PMF.pure_map]

example : deterministicExtension.conditionalEntropy = 0 := by
  simp [FiniteExtension.conditionalEntropy, FiniteExtension.auxiliaryLaw,
    FiniteExtension.outputAuxiliaryLaw, deterministicExtension, PMF.pure_map]

example : deterministicExtension.inputAuxiliaryLaw.map Prod.fst = deterministicLaw.inputLaw :=
  deterministicExtension.inputAuxiliaryLaw_map_fst

example : deterministicExtension.outputAuxiliaryLaw.map Prod.fst = deterministicLaw.outputLaw :=
  deterministicExtension.outputAuxiliaryLaw_map_fst

example : (FiniteExtension.trivial binaryCopyLaw).auxiliaryInformation = 0 :=
  FiniteExtension.trivial_auxiliaryInformation binaryCopyLaw

example : (FiniteExtension.trivial binaryCopyLaw).conditionalEntropy = 1 := by
  rw [FiniteExtension.trivial_conditionalEntropy]
  exact binaryCopyLaw_outputEntropy

example : conditionalPrefixOptimum binaryCopyLaw ≤ (1 : EReal) := by
  have hrec :
      (FiniteExtension.trivial binaryCopyLaw).outputGivenInputAuxiliaryEntropy
        = 0 := by
    have e1 : shannonEntropy (FiniteExtension.trivial binaryCopyLaw).law
        = 1 := by
      show shannonEntropy
          (binaryCopyLaw.law.map (fun z => (z, (0 : Fin 1)))) = 1
      rw [shannonEntropy_map_prod_singleton, binaryCopyLaw_entropy]
    have e2 : shannonEntropy
        (FiniteExtension.trivial binaryCopyLaw).inputAuxiliaryLaw = 1 := by
      have hmap : (FiniteExtension.trivial binaryCopyLaw).inputAuxiliaryLaw
          = binaryCopyLaw.inputLaw.map (fun x => (x, (0 : Fin 1))) := by
        simp [FiniteExtension.inputAuxiliaryLaw, FiniteExtension.trivial,
          FiniteJointLaw.inputLaw, PMF.map_comp, Function.comp_def]
      rw [hmap]
      exact (shannonEntropy_map_prod_singleton binaryCopyLaw.inputLaw).trans
        binaryCopyLaw_inputEntropy
    rw [FiniteExtension.outputGivenInputAuxiliaryEntropy, e1, e2]
    norm_num
  simpa only [FiniteExtension.trivial_conditionalEntropy,
    binaryCopyLaw_outputEntropy, EReal.coe_one] using
    conditionalPrefixOptimum_le (FiniteExtension.trivial binaryCopyLaw)
      (FiniteExtension.trivial_auxiliaryInformation binaryCopyLaw) hrec

example : correlatedAuxiliary.auxiliaryInformation ≠ 0 := by
  rw [correlatedAuxiliary_information]
  norm_num

example : correlatedAuxiliary.inputAuxiliaryLaw.map Prod.fst = binaryCopyLaw.inputLaw :=
  correlatedAuxiliary.inputAuxiliaryLaw_map_fst

example : correlatedAuxiliary.outputAuxiliaryLaw.map Prod.fst = binaryCopyLaw.outputLaw :=
  correlatedAuxiliary.outputAuxiliaryLaw_map_fst

example : correlatedAuxiliary.inputAuxiliaryLaw.map Prod.snd = correlatedAuxiliary.auxiliaryLaw :=
  correlatedAuxiliary.inputAuxiliaryLaw_map_snd

example : correlatedAuxiliary.outputAuxiliaryLaw.map Prod.snd = correlatedAuxiliary.auxiliaryLaw :=
  correlatedAuxiliary.outputAuxiliaryLaw_map_snd

example : shannonEntropy ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map (Equiv.swap (0 : Fin 2) 1)) = 1 := by
  simpa only [fairBitEntropy] using shannonEntropy_map_equiv
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2)) (Equiv.swap (0 : Fin 2) 1)

example : quantizedConditionalEntropy fairBitProbability ⟨⊥, bot_le⟩
    (fun _ : Fin 2 => (0 : Fin 2)) measurable_const = 0 :=
  quantizedConditionalEntropy_const fairBitProbability ⟨⊥, bot_le⟩ 0

example : conditionalShannonEntropy fairBitProbability ⟨⊥, bot_le⟩
    (fun _ : Fin 2 => (0 : Fin 2)) measurable_const = 0 :=
  conditionalShannonEntropy_const fairBitProbability ⟨⊥, bot_le⟩ 0

/--
error: Type mismatch
  quantizedConditionalEntropy μ m f
has type
  Measurable f → ℝ
but is expected to have type
  ℝ
-/
#guard_msgs in
noncomputable example {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (m : {m : MeasurableSpace Ω // m ≤ mΩ}) {n : ℕ} (f : Ω → Fin n) : ℝ :=
  quantizedConditionalEntropy μ m f

/--
error: Type mismatch
  conditionalShannonEntropy μ m output
has type
  Measurable output → ENNReal
but is expected to have type
  ENNReal
-/
#guard_msgs in
noncomputable example {Ω Y : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : ProbabilityMeasure Ω) (m : {m : MeasurableSpace Ω // m ≤ mΩ})
    (output : Ω → Y) : ENNReal :=
  conditionalShannonEntropy μ m output

end MathlibExtTest.InformationTheory
