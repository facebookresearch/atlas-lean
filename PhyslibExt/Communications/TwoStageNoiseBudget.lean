/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-stage noise budget

## i. Overview

Two cascaded receiver stages with power gains `G1, G2` and
stage-added noises. From uncorrelated noise-power addition, the
cascade noise factor is the Friis formula
`F = F1 + (F2 - 1) / G1`, with Boltzmann's constant an explicit
positive parameter. The general variance formula keeps the
covariance terms; anticorrelated stage noises break the Friis
form.

## ii. Key results

- `noiseFactor_twoStageOutput_of_uncorrelated`: the Friis
  cascade noise factor from zero covariances.
- `snr_ratio_twoStageOutput_of_uncorrelated`: the SNR
  degradation equals the same factor.
- `variance_twoStageOutput`: the covariance-corrected variance.

## iii. Table of contents

- A. Two-stage noise budget

## iv. References

- D. M. Pozar, *Microwave Engineering*, fourth edition, Wiley,
  2012: cascade noise figure (Friis formula).

## A. Two-stage noise budget

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
namespace PhyslibExt.Communications.TwoStageNoiseBudget

/-- Available thermal noise power `N0 = kB T0 B` of the reference source at temperature `T0`
in the fixed bandwidth `B`; `kB` is the coordinate of the Boltzmann constant in the chosen
unit system. -/
def thermalNoisePower (kB T0 B : ℝ) : ℝ :=
  kB * T0 * B

/-- Output-referred noise power `G (F - 1) N0` added by a stage of power gain `G` and noise
factor `F`, for reference input noise power `N0`. -/
def addedNoisePower (G F N0 : ℝ) : ℝ :=
  G * (F - 1) * N0

/-- Output noise power of two cascaded stages when noise powers add:
`G2 (G1 N0 + N1) + N2`. -/
def twoStageOutputNoisePower (G1 G2 N0 N1 N2 : ℝ) : ℝ :=
  G2 * (G1 * N0 + N1) + N2

/-- Noise factor of a chain of total power gain `G`: output noise power over the gain times
the reference input noise power, `Nout / (G Nin)`. -/
noncomputable def noiseFactor (G Nin Nout : ℝ) : ℝ :=
  Nout / (G * Nin)

/-- Signal-to-noise power ratio `S / N`. -/
noncomputable def snr (S N : ℝ) : ℝ :=
  S / N

/-- Output noise of two matched power-gain stages: the input noise `X₀` passes stage 1
(amplitude factor `√G1`, added noise `W₁`), then stage 2 (amplitude factor `√G2`, added
noise `W₂`). -/
noncomputable def twoStageOutput {Ω : Type*} (G1 G2 : ℝ) (X₀ W₁ W₂ : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω) + W₂ ω

/-- Covariance-corrected output noise power of the two-stage chain, for arbitrary (possibly
correlated) square-integrable noises. -/
lemma variance_twoStageOutput {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (G1 G2 : ℝ) (hG1 : 0 < G1) (hG2 : 0 < G2) (X₀ W₁ W₂ : Ω → ℝ)
    (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ) (hW₂ : MemLp W₂ 2 μ) :
    Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] =
      twoStageOutputNoisePower G1 G2 Var[X₀; μ] Var[W₁; μ] Var[W₂; μ] +
        2 * Real.sqrt G1 * G2 * cov[X₀, W₁; μ] +
        2 * Real.sqrt G1 * Real.sqrt G2 * cov[X₀, W₂; μ] +
        2 * Real.sqrt G2 * cov[W₁, W₂; μ] := by
  have hA : MemLp (fun ω => Real.sqrt G1 * X₀ ω) 2 μ := hX₀.const_mul _
  have hAB : MemLp (fun ω => Real.sqrt G1 * X₀ ω + W₁ ω) 2 μ := hA.add hW₁
  have hC : MemLp (fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω)) 2 μ :=
    hAB.const_mul _
  have hOut : twoStageOutput G1 G2 X₀ W₁ W₂
      = (fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω)) + W₂ := rfl
  have hAB' : (fun ω => Real.sqrt G1 * X₀ ω + W₁ ω)
      = (fun ω => Real.sqrt G1 * X₀ ω) + W₁ := rfl
  have hVarC : Var[(fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω)); μ]
      = G2 * Var[(fun ω => Real.sqrt G1 * X₀ ω + W₁ ω); μ] := by
    have h := variance_const_mul (Real.sqrt G2)
      (fun ω => Real.sqrt G1 * X₀ ω + W₁ ω) μ
    rw [Real.sq_sqrt hG2.le] at h
    exact h
  have hVarAB : Var[(fun ω => Real.sqrt G1 * X₀ ω + W₁ ω); μ]
      = Var[(fun ω => Real.sqrt G1 * X₀ ω); μ]
        + 2 * cov[(fun ω => Real.sqrt G1 * X₀ ω), W₁; μ] + Var[W₁; μ] := by
    rw [hAB']
    exact variance_add hA hW₁
  have hVarA : Var[(fun ω => Real.sqrt G1 * X₀ ω); μ] = G1 * Var[X₀; μ] := by
    have h := variance_const_mul (Real.sqrt G1) X₀ μ
    rw [Real.sq_sqrt hG1.le] at h
    exact h
  have hCovAB : cov[(fun ω => Real.sqrt G1 * X₀ ω), W₁; μ]
      = Real.sqrt G1 * cov[X₀, W₁; μ] :=
    covariance_const_mul_left _
  have hCovCD : cov[(fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω)), W₂; μ]
      = Real.sqrt G2 * (Real.sqrt G1 * cov[X₀, W₂; μ] + cov[W₁, W₂; μ]) := by
    have h1 : cov[(fun ω => Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω)), W₂; μ]
        = Real.sqrt G2 * cov[(fun ω => Real.sqrt G1 * X₀ ω + W₁ ω), W₂; μ] :=
      covariance_const_mul_left _
    have h2 : cov[(fun ω => Real.sqrt G1 * X₀ ω + W₁ ω), W₂; μ]
        = cov[(fun ω => Real.sqrt G1 * X₀ ω), W₂; μ] + cov[W₁, W₂; μ] := by
      rw [hAB']
      exact covariance_add_left hA hW₁ hW₂
    have h3 : cov[(fun ω => Real.sqrt G1 * X₀ ω), W₂; μ]
        = Real.sqrt G1 * cov[X₀, W₂; μ] :=
      covariance_const_mul_left _
    rw [h1, h2, h3]
  rw [hOut, variance_add hC hW₂, hVarC, hCovCD, hVarAB, hVarA, hCovAB]
  unfold twoStageOutputNoisePower
  ring

/-- **Uncorrelated noise-power addition** through the two-stage chain. -/
lemma variance_twoStageOutput_of_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (G1 G2 : ℝ) (hG1 : 0 < G1) (hG2 : 0 < G2)
    (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ) (hW₂ : MemLp W₂ 2 μ)
    (h₀₁ : cov[X₀, W₁; μ] = 0) (h₀₂ : cov[X₀, W₂; μ] = 0) (h₁₂ : cov[W₁, W₂; μ] = 0) :
    Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] =
      twoStageOutputNoisePower G1 G2 Var[X₀; μ] Var[W₁; μ] Var[W₂; μ] := by
  have h := variance_twoStageOutput G1 G2 hG1 hG2 X₀ W₁ W₂ hX₀ hW₁ hW₂
  rw [h, h₀₁, h₀₂, h₁₂]
  ring

/-- Power-level two-stage noise factor `F = F1 + (F2 - 1)/G1` once noise powers add. -/
lemma noiseFactor_twoStageOutputNoisePower (kB T0 B G1 G2 F1 F2 : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) :
    noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
        (twoStageOutputNoisePower G1 G2 (thermalNoisePower kB T0 B)
          (addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
          (addedNoisePower G2 F2 (thermalNoisePower kB T0 B))) =
      F1 + (F2 - 1) / G1 := by
  unfold noiseFactor twoStageOutputNoisePower addedNoisePower thermalNoisePower
  have hG1' : G1 ≠ 0 := ne_of_gt hG1
  have hG2' : G2 ≠ 0 := ne_of_gt hG2
  have hN0' : kB * T0 * B ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hkB) (ne_of_gt hT0)) (ne_of_gt hB)
  have hD' : (G1 * G2) * (kB * T0 * B) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hG1' hG2') hN0'
  field_simp
  ring

/-- **Two-stage noise factor from uncorrelated noise-power addition.** For matched stages of
power gains `G1, G2 > 0` and noise factors `F1, F2 ≥ 1`, reference input noise of power
`N0 = kB T0 B > 0`, and pairwise uncorrelated square-integrable noises with powers
`N0`, `N1 = G1 (F1 - 1) N0`, `N2 = G2 (F2 - 1) N0`, the total noise factor is
`F1 + (F2 - 1)/G1`. -/
lemma noiseFactor_twoStageOutput_of_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ)
    (hW₂ : MemLp W₂ 2 μ) (h₀₁ : cov[X₀, W₁; μ] = 0) (h₀₂ : cov[X₀, W₂; μ] = 0)
    (h₁₂ : cov[W₁, W₂; μ] = 0) (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[W₂; μ] = addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
        Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] =
      F1 + (F2 - 1) / G1 := by
  have hV := variance_twoStageOutput_of_uncorrelated G1 G2 hG1 hG2 X₀ W₁ W₂ hX₀ hW₁
    hW₂ h₀₁ h₀₂ h₁₂
  rw [hV, hN₀, hN₁, hN₂]
  exact noiseFactor_twoStageOutputNoisePower kB T0 B G1 G2 F1 F2 hkB hT0 hB hG1 hG2
    hF1 hF2

/-- Independence suffices: the two-stage noise factor for pairwise independent noises. -/
lemma noiseFactor_twoStageOutput_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ)
    (hW₂ : MemLp W₂ 2 μ) (h₀₁ : IndepFun X₀ W₁ μ) (h₀₂ : IndepFun X₀ W₂ μ)
    (h₁₂ : IndepFun W₁ W₂ μ) (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[W₂; μ] = addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
        Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] =
      F1 + (F2 - 1) / G1 := by
  have h₀₁' : cov[X₀, W₁; μ] = 0 := h₀₁.covariance_eq_zero hX₀ hW₁
  have h₀₂' : cov[X₀, W₂; μ] = 0 := h₀₂.covariance_eq_zero hX₀ hW₂
  have h₁₂' : cov[W₁, W₂; μ] = 0 := h₁₂.covariance_eq_zero hW₁ hW₂
  exact noiseFactor_twoStageOutput_of_uncorrelated kB T0 B G1 G2 F1 F2 hkB hT0 hB hG1
    hG2 hF1 hF2 X₀ W₁ W₂ hX₀ hW₁ hW₂ h₀₁' h₀₂' h₁₂' hN₀ hN₁ hN₂

private theorem outputNoisePower_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ)
    (hW₂ : MemLp W₂ 2 μ) (h₀₁ : cov[X₀, W₁; μ] = 0) (h₀₂ : cov[X₀, W₂; μ] = 0)
    (h₁₂ : cov[W₁, W₂; μ] = 0) (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[W₂; μ] = addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    0 < Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] := by
  have hV := variance_twoStageOutput_of_uncorrelated G1 G2 hG1 hG2 X₀ W₁ W₂ hX₀ hW₁
    hW₂ h₀₁ h₀₂ h₁₂
  rw [hV, hN₀, hN₁, hN₂]
  show (0 : ℝ) < G2 * (G1 * (kB * T0 * B) + G1 * (F1 - 1) * (kB * T0 * B))
    + G2 * (F2 - 1) * (kB * T0 * B)
  have hN0 : (0 : ℝ) < kB * T0 * B := mul_pos (mul_pos hkB hT0) hB
  have hN1 : (0 : ℝ) ≤ G1 * (F1 - 1) * (kB * T0 * B) :=
    mul_nonneg (mul_nonneg (le_of_lt hG1) (by linarith)) (le_of_lt hN0)
  have hN2 : (0 : ℝ) ≤ G2 * (F2 - 1) * (kB * T0 * B) :=
    mul_nonneg (mul_nonneg (le_of_lt hG2) (by linarith)) (le_of_lt hN0)
  have hMid : (0 : ℝ) < G1 * (kB * T0 * B) + G1 * (F1 - 1) * (kB * T0 * B) := by
    have hCore : (0 : ℝ) < G1 * (kB * T0 * B) := mul_pos hG1 hN0
    linarith
  have hFst : (0 : ℝ)
      < G2 * (G1 * (kB * T0 * B) + G1 * (F1 - 1) * (kB * T0 * B)) :=
    mul_pos hG2 hMid
  linarith

/-- **SNR transfer.** For positive input signal power `S`, the input SNR over the output SNR
(output signal power `G1 G2 S`) equals the two-stage noise factor `F1 + (F2 - 1)/G1`. -/
lemma snr_ratio_twoStageOutput_of_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 S : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) (hS : 0 < S) (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ)
    (hW₁ : MemLp W₁ 2 μ) (hW₂ : MemLp W₂ 2 μ) (h₀₁ : cov[X₀, W₁; μ] = 0)
    (h₀₂ : cov[X₀, W₂; μ] = 0) (h₁₂ : cov[W₁, W₂; μ] = 0)
    (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[W₂; μ] = addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    snr S (thermalNoisePower kB T0 B) /
        snr (G1 * G2 * S) Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] =
      F1 + (F2 - 1) / G1 := by
  have hF := noiseFactor_twoStageOutput_of_uncorrelated kB T0 B G1 G2 F1 F2 hkB hT0
    hB hG1 hG2 hF1 hF2 X₀ W₁ W₂ hX₀ hW₁ hW₂ h₀₁ h₀₂ h₁₂ hN₀ hN₁ hN₂
  have hF' : Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ]
      / ((G1 * G2) * thermalNoisePower kB T0 B) = F1 + (F2 - 1) / G1 := hF
  have hN0 : (0 : ℝ) < thermalNoisePower kB T0 B := by
    show (0 : ℝ) < kB * T0 * B
    exact mul_pos (mul_pos hkB hT0) hB
  have hD' : (G1 * G2) * thermalNoisePower kB T0 B ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos hG1 hG2) hN0)
  have hEq : Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ]
      = (F1 + (F2 - 1) / G1) * ((G1 * G2) * thermalNoisePower kB T0 B) :=
    (div_eq_iff hD').mp hF'
  have hN0' : thermalNoisePower kB T0 B ≠ 0 := ne_of_gt hN0
  have hP' : G1 * G2 * S ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hG1) (ne_of_gt hG2)) (ne_of_gt hS)
  show (S / thermalNoisePower kB T0 B)
      / ((G1 * G2 * S) / Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ])
      = F1 + (F2 - 1) / G1
  rw [hEq, div_div_eq_mul_div, div_eq_iff hP', div_mul_eq_mul_div, div_eq_iff hN0']
  ring

/-- **SNR degradation.** For positive input signal power `S`, the output SNR of the two-stage
chain does not exceed the input SNR. -/
lemma snr_twoStageOutput_le_of_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 S : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) (hS : 0 < S) (X₀ W₁ W₂ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ)
    (hW₁ : MemLp W₁ 2 μ) (hW₂ : MemLp W₂ 2 μ) (h₀₁ : cov[X₀, W₁; μ] = 0)
    (h₀₂ : cov[X₀, W₂; μ] = 0) (h₁₂ : cov[W₁, W₂; μ] = 0)
    (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[W₂; μ] = addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    snr (G1 * G2 * S) Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] ≤
      snr S (thermalNoisePower kB T0 B) := by
  have hRatio := snr_ratio_twoStageOutput_of_uncorrelated kB T0 B G1 G2 F1 F2 S hkB
    hT0 hB hG1 hG2 hF1 hF2 hS X₀ W₁ W₂ hX₀ hW₁ hW₂ h₀₁ h₀₂ h₁₂ hN₀ hN₁ hN₂
  have hFge : (1 : ℝ) ≤ F1 + (F2 - 1) / G1 := by
    have hnn : (0 : ℝ) ≤ (F2 - 1) / G1 := div_nonneg (by linarith) (le_of_lt hG1)
    linarith
  have hN0 : (0 : ℝ) < thermalNoisePower kB T0 B := by
    show (0 : ℝ) < kB * T0 * B
    exact mul_pos (mul_pos hkB hT0) hB
  have hNout : (0 : ℝ) < Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] :=
    outputNoisePower_pos kB T0 B G1 G2 F1 F2 hkB hT0 hB hG1 hG2 hF1 hF2 X₀ W₁ W₂
      hX₀ hW₁ hW₂ h₀₁ h₀₂ h₁₂ hN₀ hN₁ hN₂
  have hOutPos : (0 : ℝ)
      < snr (G1 * G2 * S) Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] := by
    show (0 : ℝ) < (G1 * G2 * S) / Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ]
    exact div_pos (mul_pos (mul_pos hG1 hG2) hS) hNout
  have h1 : (1 : ℝ) ≤ snr S (thermalNoisePower kB T0 B)
      / snr (G1 * G2 * S) Var[twoStageOutput G1 G2 X₀ W₁ W₂; μ] := by
    rw [hRatio]
    exact hFge
  exact (one_le_div hOutPos).mp h1

/-- Validation, unity first-stage gain `G1 = 1`: `F = F1 + F2 - 1`. -/
lemma noiseFactor_twoStageOutputNoisePower_unity_gain (kB T0 B G2 F1 F2 : ℝ)
    (hkB : 0 < kB) (hT0 : 0 < T0) (hB : 0 < B) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) :
    noiseFactor (1 * G2) (thermalNoisePower kB T0 B)
        (twoStageOutputNoisePower 1 G2 (thermalNoisePower kB T0 B)
          (addedNoisePower 1 F1 (thermalNoisePower kB T0 B))
          (addedNoisePower G2 F2 (thermalNoisePower kB T0 B))) =
      F1 + F2 - 1 := by
  have h := noiseFactor_twoStageOutputNoisePower kB T0 B 1 G2 F1 F2 hkB hT0 hB one_pos
    hG2 hF1 hF2
  rw [h]
  ring

/-- Validation, large first-stage gain: as `G1 → ∞` the two-stage noise factor tends to the
first stage's `F1`. -/
lemma tendsto_noiseFactor_twoStageOutputNoisePower_atTop (kB T0 B G2 F1 F2 : ℝ)
    (hkB : 0 < kB) (hT0 : 0 < T0) (hB : 0 < B) (hG2 : 0 < G2) (hF1 : 1 ≤ F1)
    (hF2 : 1 ≤ F2) :
    Tendsto
      (fun G1 : ℝ =>
        noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
          (twoStageOutputNoisePower G1 G2 (thermalNoisePower kB T0 B)
            (addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
            (addedNoisePower G2 F2 (thermalNoisePower kB T0 B))))
      atTop (𝓝 F1) := by
  have hEq : (fun G1 : ℝ => F1 + (F2 - 1) / G1) =ᶠ[atTop]
      (fun G1 : ℝ =>
        noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
          (twoStageOutputNoisePower G1 G2 (thermalNoisePower kB T0 B)
            (addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
            (addedNoisePower G2 F2 (thermalNoisePower kB T0 B)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with G1 hG1
    exact (noiseFactor_twoStageOutputNoisePower kB T0 B G1 G2 F1 F2 hkB hT0 hB hG1
      hG2 hF1 hF2).symm
  have hLim : Tendsto (fun G1 : ℝ => F1 + (F2 - 1) / G1) atTop (𝓝 F1) := by
    have h0 : Tendsto (fun G1 : ℝ => (F2 - 1) / G1) atTop (𝓝 0) := by
      have heq : (fun G1 : ℝ => (F2 - 1) / G1) = fun G1 : ℝ => (F2 - 1) * G1⁻¹ := by
        funext G1
        exact div_eq_mul_inv _ _
      rw [heq]
      simpa using tendsto_inv_atTop_zero.const_mul (F2 - 1)
    simpa using tendsto_const_nhds.add h0
  exact Tendsto.congr' hEq hLim

/-- Validation, zero signal: the SNR ratio with `S = 0` is not the noise factor (it is Lean's
junk value `0`), so `S > 0` is needed for the SNR transfer. -/
lemma snr_ratio_zero_signal_ne (kB T0 B G1 G2 F1 F2 Nout : ℝ) (hG1 : 0 < G1)
    (hF1 : 1 ≤ F1) (hF2 : 1 ≤ F2) :
    snr 0 (thermalNoisePower kB T0 B) / snr (G1 * G2 * 0) Nout ≠ F1 + (F2 - 1) / G1 := by
  have hLHS : snr 0 (thermalNoisePower kB T0 B) / snr (G1 * G2 * 0) Nout = 0 := by
    unfold snr
    rw [mul_zero, zero_div, zero_div]
  rw [hLHS]
  have hnn : (0 : ℝ) ≤ (F2 - 1) / G1 := div_nonneg (by linarith) (le_of_lt hG1)
  have hpos : (0 : ℝ) < F1 + (F2 - 1) / G1 := by linarith
  exact ne_of_lt hpos

/-- Validation, correlated noises: if the second stage's noise is `W₂ = -√G2 W₁`, which
cancels the first stage's added noise, the chain's noise factor is not
`F1 + (F2 - 1)/G1` whenever `F1 > 1`; covariance terms cannot be dropped. -/
lemma noiseFactor_twoStageOutput_anticorrelated_ne {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (kB T0 B G1 G2 F1 F2 : ℝ) (hkB : 0 < kB)
    (hT0 : 0 < T0) (hB : 0 < B) (hG1 : 0 < G1) (hG2 : 0 < G2) (hF1 : 1 < F1)
    (hF2 : 1 ≤ F2) (X₀ W₁ : Ω → ℝ) (hX₀ : MemLp X₀ 2 μ) (hW₁ : MemLp W₁ 2 μ)
    (h₀₁ : cov[X₀, W₁; μ] = 0) (hN₀ : Var[X₀; μ] = thermalNoisePower kB T0 B)
    (hN₁ : Var[W₁; μ] = addedNoisePower G1 F1 (thermalNoisePower kB T0 B))
    (hN₂ : Var[fun ω => -(Real.sqrt G2 * W₁ ω); μ] =
      addedNoisePower G2 F2 (thermalNoisePower kB T0 B)) :
    noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
        Var[twoStageOutput G1 G2 X₀ W₁ (fun ω => -(Real.sqrt G2 * W₁ ω)); μ] ≠
      F1 + (F2 - 1) / G1 := by
  have hSimp : twoStageOutput G1 G2 X₀ W₁ (fun ω => -(Real.sqrt G2 * W₁ ω))
      = fun ω => (Real.sqrt G2 * Real.sqrt G1) * X₀ ω := by
    funext ω
    show Real.sqrt G2 * (Real.sqrt G1 * X₀ ω + W₁ ω) + -(Real.sqrt G2 * W₁ ω)
      = (Real.sqrt G2 * Real.sqrt G1) * X₀ ω
    ring
  have hVar : Var[twoStageOutput G1 G2 X₀ W₁ (fun ω => -(Real.sqrt G2 * W₁ ω)); μ]
      = G1 * G2 * thermalNoisePower kB T0 B := by
    rw [hSimp]
    have h := variance_const_mul (Real.sqrt G2 * Real.sqrt G1) X₀ μ
    rw [hN₀, mul_pow, Real.sq_sqrt hG2.le, Real.sq_sqrt hG1.le] at h
    linear_combination h
  have hN0 : (0 : ℝ) < thermalNoisePower kB T0 B := by
    show (0 : ℝ) < kB * T0 * B
    exact mul_pos (mul_pos hkB hT0) hB
  have hD' : (G1 * G2) * thermalNoisePower kB T0 B ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos hG1 hG2) hN0)
  have hNF : noiseFactor (G1 * G2) (thermalNoisePower kB T0 B)
      Var[twoStageOutput G1 G2 X₀ W₁ (fun ω => -(Real.sqrt G2 * W₁ ω)); μ] = 1 := by
    show Var[twoStageOutput G1 G2 X₀ W₁ (fun ω => -(Real.sqrt G2 * W₁ ω)); μ]
        / ((G1 * G2) * thermalNoisePower kB T0 B) = 1
    rw [hVar]
    exact div_self hD'
  have hFgt : (1 : ℝ) < F1 + (F2 - 1) / G1 := by
    have hnn : (0 : ℝ) ≤ (F2 - 1) / G1 := div_nonneg (by linarith) (le_of_lt hG1)
    linarith
  rw [hNF]
  exact ne_of_lt hFgt

end PhyslibExt.Communications.TwoStageNoiseBudget
