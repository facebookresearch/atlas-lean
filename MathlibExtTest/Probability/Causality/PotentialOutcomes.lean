/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.PotentialOutcomes

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
open scoped ENNReal NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.MendelianRandomization

/-! ### Potential outcomes: a non-vacuous witness for the LATE theorem

Units `ω = (z, c)` drawn uniformly from `Bool × Bool`: the instrument is `z`, and `c` says
whether the unit is a complier (`D(z) = z`) or a never-taker (`D(z) = 0`). The outcome is the
treatment indicator, so every complier has effect `1`, and the Wald estimand is `1`. -/

/-- The uniform law on `Bool`. -/
noncomputable def μ2 : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

theorem μ2_singleton (b : Bool) : μ2 {b} = 2⁻¹ := by
  cases b <;> simp [μ2]

instance : IsProbabilityMeasure μ2 := ⟨by
  simp [μ2]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

/-- The witness model. -/
def lateWitness : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun z ω => z && ω.2
  outcome := fun _ d _ => if d then 1 else 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_of_countable _
  measurable_outcome := fun _ _ => measurable_const

theorem lateWitness_compliers : lateWitness.compliers = Set.univ ×ˢ {true} := by
  ext ⟨a, b⟩
  cases b <;> simp [PotentialOutcomes.compliers, PotentialOutcomes.type, complianceType,
    lateWitness]

theorem lateWitness_independence : lateWitness.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun b : Bool => ((fun z => z && b), fun (_ : Bool) (d : Bool) => if d then (1 : ℝ)
      else 0))
    measurable_id (measurable_of_countable _)

/-- Generic source-shaped client: relevance is an explicit premise of LATE identification. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hind : P.Independence μ) (hexcl : P.Exclusion)
    (hmono : P.Monotonicity) (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) (hC : μ P.compliers ≠ 0) (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] :=
  P.waldEstimand_eq_late hind hexcl hmono hY hZ hC z

example : lateWitness.waldEstimand (μ2.prod μ2) = 1 := by
  have hC : (μ2.prod μ2) lateWitness.compliers ≠ 0 := by
    rw [lateWitness_compliers, Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  have hZ : ∀ z, (μ2.prod μ2) (lateWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show lateWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by ext; simp [lateWitness],
      Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  rw [lateWitness.waldEstimand_eq_late lateWitness_independence (fun _ _ => rfl)
    (fun ω => by cases ω.2 <;> simp [lateWitness]) (fun _ _ => Integrable.of_finite) hZ hC
    true]
  have := cond_isProbabilityMeasure (μ := μ2.prod μ2) hC
  rw [show (fun ω : Bool × Bool => lateWitness.outcome true true ω -
      lateWitness.outcome true false ω) = fun _ => 1 by funext; simp [lateWitness]]
  simp

/-- Positive complier mass gives a genuinely nonzero first stage. -/
example : lateWitness.armMean (μ2.prod μ2) lateWitness.treated true -
    lateWitness.armMean (μ2.prod μ2) lateWitness.treated false ≠ 0 := by
  have hC : (μ2.prod μ2) lateWitness.compliers ≠ 0 := by
    rw [lateWitness_compliers, Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  have hZ : ∀ z, (μ2.prod μ2) (lateWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show lateWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by ext; simp [lateWitness],
      Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  rw [lateWitness.armMean_treated_sub lateWitness_independence
    (fun ω => by cases ω.2 <;> simp [lateWitness]) hZ]
  exact (measureReal_ne_zero_iff (by simp)).2 hC

/-! ### Zero-complier boundary: only the totalized algebraic identity remains -/

/-- A randomized instrument with no compliers: every unit is a never-taker and every potential
outcome is zero. The structural independence, exclusion and monotonicity assumptions all hold,
but relevance does not. -/
def zeroComplierWitness : PotentialOutcomes (Bool × Bool) where
  instrument := Prod.fst
  treatment := fun _ _ => false
  outcome := fun _ _ _ => 0
  measurable_instrument := measurable_fst
  measurable_treatment := fun _ => measurable_const
  measurable_outcome := fun _ _ => measurable_const

theorem zeroComplierWitness_compliers : zeroComplierWitness.compliers = ∅ := by
  ext ⟨z, u⟩
  simp [PotentialOutcomes.compliers, PotentialOutcomes.type, complianceType,
    zeroComplierWitness]

theorem zeroComplierWitness_independence : zeroComplierWitness.Independence (μ2.prod μ2) :=
  indepFun_prod (X := id)
    (Y := fun _ : Bool => ((fun _ => false), fun (_ : Bool) (_ : Bool) => (0 : ℝ)))
    measurable_id (measurable_of_countable _)

/-- At the zero-complier boundary, the old unrestricted identity is only the totalized `0 = 0`. -/
example : zeroComplierWitness.waldEstimand (μ2.prod μ2) =
    ∫ ω, zeroComplierWitness.outcome true true ω -
      zeroComplierWitness.outcome true false ω ∂(μ2.prod μ2)[|zeroComplierWitness.compliers] := by
  have hZ : ∀ z, (μ2.prod μ2) (zeroComplierWitness.instrument ⁻¹' {z}) ≠ 0 := by
    intro z
    rw [show zeroComplierWitness.instrument ⁻¹' {z} = {z} ×ˢ Set.univ by
      ext
      simp [zeroComplierWitness], Measure.prod_prod, measure_univ]
    simp [μ2_singleton]
  exact zeroComplierWitness.waldEstimand_eq_late_totalized zeroComplierWitness_independence
    (fun _ _ => rfl) (fun _ => by simp [zeroComplierWitness])
    (fun _ _ => Integrable.of_finite) hZ true

example : zeroComplierWitness.waldEstimand (μ2.prod μ2) = 0 ∧
    (∫ ω, zeroComplierWitness.outcome true true ω -
      zeroComplierWitness.outcome true false ω
        ∂(μ2.prod μ2)[|zeroComplierWitness.compliers]) = 0 := by
  simp [PotentialOutcomes.waldEstimand, PotentialOutcomes.armMean,
    PotentialOutcomes.observedOutcome, zeroComplierWitness]

end MathlibExtTest.Biology.StatisticalGenetics.MendelianRandomization
