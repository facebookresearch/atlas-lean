/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.StrongDataProcessing

@[expose] public section

/-!
# Tests for the strong data-processing inequality for KL divergence

* A constant kernel has Dobrushin coefficient `0`: its two outputs are at divergence `0`, even
  for point-mass inputs at divergence `∞` (the right-hand side is `0 · ∞ = 0`).
* Since `η_TV ≤ 1`, the inequality implies the data-processing inequality for KL divergence.
* The identity kernel on `Bool` has coefficient `1`, and the inequality is an equality for it.
* The binary symmetric channel with crossover probability `p` has coefficient `|1 - 2p|`; for
  `p = 1/4` the inequality contracts the divergence by the factor `1/2`.
* Along a composition of two kernels, the coefficients multiply.
-/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.DobrushinContraction
open MathlibExt.InformationTheory.MeasurePinsker
open MathlibExt.InformationTheory.StrongDataProcessingWanted

namespace MathlibExtTest.InformationTheory.StrongDataProcessing

/-- The point masses at `true` and `false` are at KL divergence `∞`. -/
example : _root_.InformationTheory.klDiv (Measure.dirac true) (Measure.dirac false) = ⊤ := by
  refine _root_.InformationTheory.klDiv_of_not_ac fun h => ?_
  have h0 : Measure.dirac true {true} = 0 := h (by simp)
  simp at h0

/-- A constant kernel maps them to outputs at KL divergence `0`: the coefficient is `0`, and
`0 · ∞ = 0` in `ℝ≥0∞`. -/
example (ρ : Measure Bool) [IsProbabilityMeasure ρ] :
    _root_.InformationTheory.klDiv (Kernel.const Bool ρ ∘ₘ Measure.dirac true)
      (Kernel.const Bool ρ ∘ₘ Measure.dirac false) = 0 := by
  have h := klDiv_comp_le_dobrushinCoeff_mul (Kernel.const Bool ρ) (Measure.dirac true)
    (Measure.dirac false)
  have h0 : dobrushinCoeff (Kernel.const Bool ρ) = 0 := by
    simp [dobrushinCoeff, totalVariationDist_self]
  rw [h0, ENNReal.ofReal_zero, zero_mul] at h
  exact le_antisymm h zero_le

/-- The data-processing inequality for KL divergence on finite alphabets, from `η_TV ≤ 1`. -/
example {X Y : Type*} [Finite X] [Finite Y] [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ _root_.InformationTheory.klDiv μ ν := by
  refine (klDiv_comp_le_dobrushinCoeff_mul κ μ ν).trans ?_
  calc ENNReal.ofReal (dobrushinCoeff κ) * _root_.InformationTheory.klDiv μ ν
      ≤ 1 * _root_.InformationTheory.klDiv μ ν := by
        gcongr
        exact ENNReal.ofReal_le_one.2 (dobrushinCoeff_mem_Icc κ).2
    _ = _root_.InformationTheory.klDiv μ ν := one_mul _

/-- The identity kernel on `Bool` has coefficient `1`, so the inequality reads
`D(μ ‖ ν) ≤ D(μ ‖ ν)` for it: the factor `η_TV` cannot be lowered for every kernel. -/
example (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv ((Kernel.id : Kernel Bool Bool) ∘ₘ μ)
        ((Kernel.id : Kernel Bool Bool) ∘ₘ ν) =
      ENNReal.ofReal (dobrushinCoeff (Kernel.id : Kernel Bool Bool)) *
        _root_.InformationTheory.klDiv μ ν := by
  classical
  have h1 : dobrushinCoeff (Kernel.id : Kernel Bool Bool) = 1 := by
    refine le_antisymm (dobrushinCoeff_mem_Icc _).2 ?_
    have h := totalVariationDist_le_dobrushinCoeff (Kernel.id : Kernel Bool Bool) true false
    simpa [Kernel.id_apply, totalVariationDist_dirac] using h
  rw [h1, ENNReal.ofReal_one, one_mul, Measure.id_comp, Measure.id_comp]

/-- The binary symmetric channel with crossover probability `p ∈ [0, 1]`: it keeps the input bit
with probability `1 - p` and flips it with probability `p`. -/
private noncomputable def bsc (p : unitInterval) : Kernel Bool Bool where
  toFun b := ENNReal.ofReal (1 - p) • Measure.dirac b + ENNReal.ofReal p • Measure.dirac (!b)
  measurable' := measurable_of_countable _

private instance (p : unitInterval) : IsMarkovKernel (bsc p) :=
  ⟨fun b => ⟨by simp [bsc, ← ENNReal.ofReal_add (sub_nonneg.2 p.2.2) p.2.1]⟩⟩

/-- The mass that `bsc p` gives to a set `s` from the input `b`. -/
private lemma bsc_apply_toReal (p : unitInterval) (b : Bool) (s : Set Bool) :
    (bsc p b s).toReal = (1 - p) * s.indicator 1 b + p * s.indicator 1 (!b) := by
  have h0 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.2.2
  by_cases h1 : b ∈ s <;> by_cases h2 : (!b) ∈ s <;>
    simp [bsc, h1, h2, ← ENNReal.ofReal_add h0 p.2.1, ENNReal.toReal_ofReal h0, p.2.1]

/-- The two rows of `bsc p` are at total variation `|1 - 2p|`, attained on the event `{true}`. -/
private lemma totalVariationDist_bsc (p : unitInterval) :
    totalVariationDist (bsc p true) (bsc p false) = |1 - 2 * (p : ℝ)| := by
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · change |(bsc p true s.1).toReal - (bsc p false s.1).toReal| ≤ _
    rw [bsc_apply_toReal, bsc_apply_toReal]
    by_cases h1 : true ∈ s.1 <;> by_cases h2 : false ∈ s.1 <;> simp [h1, h2]
    · exact le_of_eq (by ring_nf)
    · rw [abs_sub_comm]
      exact le_of_eq (by ring_nf)
  · have h := abs_sub_le_totalVariationDist (μ := bsc p true) (ν := bsc p false)
      (measurableSet_singleton true)
    rw [measureReal_def, measureReal_def, bsc_apply_toReal, bsc_apply_toReal] at h
    convert h using 2
    simp
    ring

/-- The Dobrushin coefficient of `bsc p` is `|1 - 2p|`. -/
private lemma dobrushinCoeff_bsc (p : unitInterval) :
    dobrushinCoeff (bsc p) = |1 - 2 * (p : ℝ)| := by
  refine le_antisymm (Real.iSup_le (fun x => Real.iSup_le (fun x' => ?_) (abs_nonneg _))
    (abs_nonneg _)) (totalVariationDist_bsc p ▸ totalVariationDist_le_dobrushinCoeff _ true false)
  cases x <;> cases x'
  · rw [totalVariationDist_self]
    exact abs_nonneg _
  · rw [totalVariationDist_comm, totalVariationDist_bsc]
  · rw [totalVariationDist_bsc]
  · rw [totalVariationDist_self]
    exact abs_nonneg _

/-- The binary symmetric channel contracts KL divergence by the factor `|1 - 2p|`. -/
example (p : unitInterval) (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv (bsc p ∘ₘ μ) (bsc p ∘ₘ ν) ≤
      ENNReal.ofReal |1 - 2 * (p : ℝ)| * _root_.InformationTheory.klDiv μ ν :=
  dobrushinCoeff_bsc p ▸ klDiv_comp_le_dobrushinCoeff_mul (bsc p) μ ν

/-- With crossover probability `1/4` the coefficient is `1/2`, strictly between `0` and `1`. -/
example : dobrushinCoeff (bsc ⟨1 / 4, by norm_num, by norm_num⟩) = 1 / 2 := by
  rw [dobrushinCoeff_bsc]
  norm_num

/-- So this channel halves the KL divergence of any two input laws, at least. -/
example (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv (bsc ⟨1 / 4, by norm_num, by norm_num⟩ ∘ₘ μ)
        (bsc ⟨1 / 4, by norm_num, by norm_num⟩ ∘ₘ ν) ≤
      ENNReal.ofReal (1 / 2) * _root_.InformationTheory.klDiv μ ν := by
  have h := klDiv_comp_le_dobrushinCoeff_mul (bsc ⟨1 / 4, by norm_num, by norm_num⟩) μ ν
  rwa [dobrushinCoeff_bsc, show |1 - 2 * (1 / 4 : ℝ)| = 1 / 2 by norm_num] at h

/-- Along a composition `κ₂ ∘ κ₁` of Markov kernels between finite alphabets, the divergence
contracts by the product `η_TV(κ₂) η_TV(κ₁)`. -/
example {X Y Z : Type*} [Finite X] [Finite Y] [Finite Z] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] (κ₁ : Kernel X Y) [IsMarkovKernel κ₁]
    (κ₂ : Kernel Y Z) [IsMarkovKernel κ₂] (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    _root_.InformationTheory.klDiv ((κ₂ ∘ₖ κ₁) ∘ₘ μ) ((κ₂ ∘ₖ κ₁) ∘ₘ ν) ≤
      ENNReal.ofReal (dobrushinCoeff κ₂ * dobrushinCoeff κ₁) *
        _root_.InformationTheory.klDiv μ ν := by
  rw [← Measure.comp_assoc, ← Measure.comp_assoc,
    ENNReal.ofReal_mul (dobrushinCoeff_mem_Icc κ₂).1, mul_assoc]
  exact (klDiv_comp_le_dobrushinCoeff_mul κ₂ _ _).trans
    (by gcongr; exact klDiv_comp_le_dobrushinCoeff_mul κ₁ μ ν)

end MathlibExtTest.InformationTheory.StrongDataProcessing
