/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.HittingTime

/-!
# Path-space moments of the two-locus coalescence times

`MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent` solves the backward (first-step)
equations of the two-locus ancestral process of a sample of two sequences, with rate matrix
`twoLocusRate ρ` (time in units of `2N` generations, `ρ = 4Nr`). This file identifies those
solutions with expectations over the path process `ctmcPath (twoLocusRate ρ) linked` of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`, started from two linked
sequences. The coalescence time at locus `A` (resp. `B`) is the hitting time of the states in
which that locus has coalesced, `T_A = inf {t ≥ 0 | coalescedA (X t)}`, valued in `ℝ≥0∞`; the
expectations are lower Lebesgue integrals, so no integrability hypothesis is needed (they are
proved finite).

## Main results

* `lintegral_coalescenceTimeA`, `lintegral_coalescenceTimeB`: `E T_A = E T_B = 1`.
* `lintegral_coalescenceTimeA_mul_coalescenceTimeB` (Hudson 1983; Kaplan & Hudson 1985):
  `E (T_A T_B) = 1 + (ρ + 18) / (ρ² + 13ρ + 18)`.
* `covariance_coalescenceTimes`: `Cov(T_A, T_B) = (ρ + 18) / (ρ² + 13ρ + 18)` for the path
  process.

The proofs combine the general identification of hitting-time moments with the minimal
nonnegative solutions of the backward equations
(`ProbabilityTheory.IsRateMatrix.ctmcHittingTime_backward`,
`ProbabilityTheory.IsRateMatrix.ctmcHittingTime_mul_backward`) with uniqueness of the solution
of the two-locus systems (`eq_one_of_meanTimeA`, `covariance_of_productMoment`). Only the
`linked` starting state is stated; the other non-coalesced states follow in the same way.

## References

* R. R. Hudson, "Properties of a neutral allele model with intragenic recombination", Theor.
  Popul. Biol. 23 (1983) 183–201.
* N. L. Kaplan and R. R. Hudson, "The use of sample genealogies for studying a selectively
  neutral m-loci model with recombination", Theor. Popul. Biol. 28 (1985) 382–396.
* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §3.3.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentPath

open MeasureTheory ProbabilityTheory
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent TwoLocusState
open scoped NNReal ENNReal

private lemma meanTimeA_nonneg (i : TwoLocusState) : 0 ≤ meanTimeA i := by
  unfold meanTimeA; split_ifs <;> norm_num

private lemma meanTimeB_nonneg (i : TwoLocusState) : 0 ≤ meanTimeB i := by
  unfold meanTimeB; split_ifs <;> norm_num

private lemma productMoment_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (i : TwoLocusState) :
    0 ≤ productMoment ρ i := by
  have hd := twoLocusDenom_pos hρ
  have hc := twoLocusCov_pos hρ
  cases i <;> simp only [productMoment] <;> positivity

variable [MeasurableSpace TwoLocusState] [DiscreteMeasurableSpace TwoLocusState]

/-- The real means `E_i T_A` of the path process solve the backward equations of locus `A`. -/
private lemma backwardA {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ i, ∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) i {k | coalescedA k = true} ω
        ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) ≤ ENNReal.ofReal (meanTimeA i)) ∧
      ∀ i, coalescedA i = false →
        (∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) i {k | coalescedA k = true} ω
          ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal = 1 := by
  obtain ⟨hle, h0, heq⟩ := (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
    (A := {k | coalescedA k = true}) meanTimeA_nonneg
    fun i hi => (productMoment_solution hρ).1 i (by simpa using hi)
  exact ⟨hle, eq_one_of_meanTimeA hρ (fun i hi => h0 i hi)
    fun i hi => heq i (by simpa using hi)⟩

/-- The real means `E_i T_B` of the path process solve the backward equations of locus `B`. -/
private lemma backwardB {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ i, ∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) i {k | coalescedB k = true} ω
        ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) ≤ ENNReal.ofReal (meanTimeB i)) ∧
      ∀ i, coalescedB i = false →
        (∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) i {k | coalescedB k = true} ω
          ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal = 1 := by
  obtain ⟨hle, h0, heq⟩ := (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
    (A := {k | coalescedB k = true}) meanTimeB_nonneg
    fun i hi => (productMoment_solution hρ).2.1 i (by simpa using hi)
  exact ⟨hle, eq_one_of_meanTimeB hρ (fun i hi => h0 i hi)
    fun i hi => heq i (by simpa using hi)⟩

/-- **Mean coalescence time at locus `A`, path form**: for the two-locus ancestral process
started from two linked sequences, the hitting time `T_A` of the states where locus `A` has
coalesced has mean `1`. -/
theorem lintegral_coalescenceTimeA {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = 1 := by
  change ∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) linked {k | coalescedA k = true} ω
    ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = 1
  obtain ⟨hle, h1⟩ := backwardA hρ
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle linked)),
    h1 linked rfl, ENNReal.ofReal_one]

/-- **Mean coalescence time at locus `B`, path form**: from two linked sequences, the hitting
time `T_B` of the states where locus `B` has coalesced has mean `1`. -/
theorem lintegral_coalescenceTimeB {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = 1 := by
  change ∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) linked {k | coalescedB k = true} ω
    ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = 1
  obtain ⟨hle, h1⟩ := backwardB hρ
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle linked)),
    h1 linked rfl, ENNReal.ofReal_one]

/-- **Product moment of the two coalescence times, path form** (Hudson 1983; Kaplan & Hudson
1985): from two linked sequences, `E (T_A T_B) = 1 + (ρ + 18) / (ρ² + 13ρ + 18)`. -/
theorem lintegral_coalescenceTimeA_mul_coalescenceTimeB {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) =
      ENNReal.ofReal (1 + twoLocusCov ρ) := by
  change ∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) linked {k | coalescedA k = true} ω *
    ctmcHittingTime (twoLocusRate ρ) linked {k | coalescedB k = true} ω
    ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ) = _
  have hsol := productMoment_solution hρ
  obtain ⟨hle, h0, heq⟩ := (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_mul_backward
    (A := {k | coalescedA k = true}) (B := {k | coalescedB k = true})
    meanTimeA_nonneg meanTimeB_nonneg (productMoment_nonneg hρ)
    (fun i hi => hsol.1 i (by simpa using hi)) (fun i hi => hsol.2.1 i (by simpa using hi))
    (fun i hi => hsol.2.2.2 i (by simpa using hi))
  have hA1 := (backwardA hρ).2
  have hB1 := (backwardB hρ).2
  have hcov := (covariance_of_productMoment hρ
    (mA := fun j => (∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) j {k | coalescedA k = true} ω
      ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal)
    (mB := fun j => (∫⁻ ω, ctmcHittingTime (twoLocusRate ρ) j {k | coalescedB k = true} ω
      ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal)
    (fun i hi => (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
      (A := {k | coalescedA k = true}) meanTimeA_nonneg
      (fun i hi => hsol.1 i (by simpa using hi)) |>.2.1 i hi)
    (fun i hi => (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
      (A := {k | coalescedA k = true}) meanTimeA_nonneg
      (fun i hi => hsol.1 i (by simpa using hi)) |>.2.2 i (by simpa using hi))
    (fun i hi => (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
      (A := {k | coalescedB k = true}) meanTimeB_nonneg
      (fun i hi => hsol.2.1 i (by simpa using hi)) |>.2.1 i hi)
    (fun i hi => (isRateMatrix_twoLocusRate hρ).ctmcHittingTime_backward
      (A := {k | coalescedB k = true}) meanTimeB_nonneg
      (fun i hi => hsol.2.1 i (by simpa using hi)) |>.2.2 i (by simpa using hi))
    (fun i hi => h0 i (by simpa [Bool.or_eq_true] using hi))
    (fun i hi => heq i (by simpa [Bool.or_eq_false_iff] using hi))).1
  simp only [hA1 linked rfl, hB1 linked rfl, mul_one] at hcov
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle linked))]
  congr 1
  linarith

/-- **Covariance of the coalescence times, path form** (Hudson 1983; Kaplan & Hudson 1985):
for the two-locus ancestral process started from two linked sequences,
`E (T_A T_B) - E T_A E T_B = (ρ + 18) / (ρ² + 13ρ + 18)`, with all three expectations finite
lower Lebesgue integrals of the hitting times. -/
theorem covariance_coalescenceTimes {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) *
      (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal -
      (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedA (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal *
      (∫⁻ ω, (⨅ (t : ℝ≥0) (_ : coalescedB (ctmcPath (twoLocusRate ρ) linked ω t) = true),
        (t : ℝ≥0∞)) ∂ctmcInputMeasure (isRateMatrix_twoLocusRate hρ)).toReal =
      twoLocusCov ρ := by
  rw [lintegral_coalescenceTimeA_mul_coalescenceTimeB hρ, lintegral_coalescenceTimeA hρ,
    lintegral_coalescenceTimeB hρ, ENNReal.toReal_ofReal (by linarith [twoLocusCov_pos hρ])]
  simp

end MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentPath
