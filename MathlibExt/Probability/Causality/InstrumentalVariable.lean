/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.ConditionalProbability

/-!
# Instrumental variables: identification of the local average treatment effect

The LATE identity itself is `PotentialOutcomes.waldEstimand_eq_late` in the
Mendelian randomization module, reused here. This file adds the observed-law
statement of Imbens & Angrist (1994) Theorem 1: the Wald estimand, hence the
complier average effect, depends on the model only through the law of the
observed triple.

## References

* G. W. Imbens and J. D. Angrist, "Identification and Estimation of Local
  Average Treatment Effects", Econometrica 62(2) (1994), 467-475.
* J. D. Angrist, G. W. Imbens, D. B. Rubin, "Identification of causal effects
  using instrumental variables", J. Amer. Statist. Assoc. 91 (1996), 444-455.

## Not covered

* The population average treatment effect (not identified; see the tests).
* Multivalued instruments.
* Covariates.
* Fuzzy regression discontinuity.
* Bounded exclusion violations.
* Estimation and inference.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The observed treatment is measurable. -/
private theorem measurable_observedTreatment
    {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω) :
    Measurable P.observedTreatment := by
  have hu : Measurable (fun p : Ω × Bool => P.treatment p.2 p.1) :=
    measurable_from_prod_countable_left (fun b => P.measurable_treatment b)
  have he : Measurable (fun ω : Ω => (ω, P.instrument ω)) :=
    Measurable.prodMk measurable_id P.measurable_instrument
  have hcomp : (fun p : Ω × Bool => P.treatment p.2 p.1) ∘
      (fun ω : Ω => (ω, P.instrument ω)) = P.observedTreatment :=
    rfl
  rw [← hcomp]
  exact hu.comp he

/-- The observed outcome is measurable. -/
private theorem measurable_observedOutcome
    {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω) :
    Measurable P.observedOutcome := by
  have hu : Measurable
      (fun p : Ω × (Bool × Bool) => P.outcome p.2.1 p.2.2 p.1) :=
    measurable_from_prod_countable_left
      (fun b => P.measurable_outcome b.1 b.2)
  have he : Measurable
      (fun ω : Ω => (ω, (P.instrument ω, P.observedTreatment ω))) :=
    Measurable.prodMk measurable_id
      (Measurable.prodMk P.measurable_instrument
        (measurable_observedTreatment P))
  have hcomp : (fun p : Ω × (Bool × Bool) =>
      P.outcome p.2.1 p.2.2 p.1) ∘
      (fun ω : Ω => (ω, (P.instrument ω, P.observedTreatment ω))) =
      P.observedOutcome :=
    rfl
  rw [← hcomp]
  exact hu.comp he

/-- The observed triple is measurable. -/
private theorem measurable_observedTriple
    {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω) :
    Measurable (fun ω =>
      (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) :=
  Measurable.prodMk P.measurable_instrument
    (Measurable.prodMk (measurable_observedTreatment P)
      (measurable_observedOutcome P))

/-- Conditioning commutes with pushforward. -/
private theorem cond_map_eq
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (T : Ω → β) (μ : Measure Ω) (A : Set β)
    (hT : Measurable T) (hA : MeasurableSet A) :
    (Measure.map T μ)[|A] = Measure.map T (μ[|T ⁻¹' A]) := by
  unfold ProbabilityTheory.cond
  rw [MeasureTheory.Measure.map_smul _ hT.aemeasurable]
  rw [MeasureTheory.Measure.map_apply hT hA]
  rw [MeasureTheory.Measure.restrict_map hT hA]

/-- Integrals over a conditioned pushforward rewrite. -/
private theorem integral_cond_map_eq
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (T : Ω → β) (μ : Measure Ω) (A : Set β) (g : β → ℝ)
    (hT : Measurable T) (hA : MeasurableSet A) (hg : Measurable g) :
    ∫ ω, g (T ω) ∂μ[|T ⁻¹' A] = ∫ x, g x ∂(Measure.map T μ)[|A] := by
  rw [cond_map_eq T μ A hT hA]
  exact (MeasureTheory.integral_map hT.aemeasurable
    hg.aestronglyMeasurable).symm

/-- The outcome arm mean as an integral over the observed law. -/
private theorem armMean_outcome_eq_integral_map
    {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω)
    (μ : Measure Ω) (z : Bool) :
    P.armMean μ P.observedOutcome z = ∫ x,
      x.2.2 ∂(Measure.map (fun ω =>
        (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) μ)[|
        {x | x.1 = z}] := by
  have hT : Measurable (fun ω =>
      (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) :=
    measurable_observedTriple P
  have hA : MeasurableSet {x : Bool × Bool × ℝ | x.1 = z} :=
    measurable_fst (measurableSet_singleton z)
  have hg : Measurable (fun x : Bool × Bool × ℝ => x.2.2) :=
    measurable_snd.comp measurable_snd
  have hPre : P.instrument ⁻¹' {z} = (fun ω =>
      (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) ⁻¹'
      {x | x.1 = z} := by
    ext ω
    simp
  unfold PotentialOutcomes.armMean
  rw [hPre]
  exact integral_cond_map_eq _ _ _ _ hT hA hg

/-- The treated arm mean as an integral over the observed law. -/
private theorem armMean_treated_eq_integral_map
    {Ω : Type*} [MeasurableSpace Ω] (P : PotentialOutcomes Ω)
    (μ : Measure Ω) (z : Bool) :
    P.armMean μ P.treated z = ∫ x,
      (if x.2.1 then (1 : ℝ) else 0) ∂(Measure.map (fun ω =>
        (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) μ)[|
        {x | x.1 = z}] := by
  have hT : Measurable (fun ω =>
      (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) :=
    measurable_observedTriple P
  have hA : MeasurableSet {x : Bool × Bool × ℝ | x.1 = z} :=
    measurable_fst (measurableSet_singleton z)
  have hBool : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have hProj : Measurable (fun x : Bool × Bool × ℝ => x.2.1) :=
    measurable_fst.comp measurable_snd
  have hg : Measurable
      (fun x : Bool × Bool × ℝ => if x.2.1 then (1 : ℝ) else 0) :=
    hBool.comp hProj
  have hPre : P.instrument ⁻¹' {z} = (fun ω =>
      (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) ⁻¹'
      {x | x.1 = z} := by
    ext ω
    simp
  unfold PotentialOutcomes.armMean
  rw [hPre]
  exact integral_cond_map_eq _ _ _ _ hT hA hg

/-- The Wald estimand is a functional of the joint law of the observed
(Z, D, Y) alone (the observed-law half of Imbens & Angrist 1994,
Theorem 1). -/
theorem waldEstimand_eq_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : PotentialOutcomes Ω) (P' : PotentialOutcomes Ω')
    (μ : Measure Ω) (μ' : Measure Ω')
    (h : Measure.map (fun ω =>
        (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) μ =
      Measure.map (fun ω' =>
        (P'.instrument ω', P'.observedTreatment ω',
          P'.observedOutcome ω')) μ') :
    P.waldEstimand μ = P'.waldEstimand μ' := by
  have hOut : ∀ z : Bool, P.armMean μ P.observedOutcome z =
      P'.armMean μ' P'.observedOutcome z := by
    intro z
    calc P.armMean μ P.observedOutcome z
        = ∫ x, x.2.2 ∂(Measure.map (fun ω =>
            (P.instrument ω, P.observedTreatment ω,
              P.observedOutcome ω)) μ)[|{x | x.1 = z}] :=
          armMean_outcome_eq_integral_map P μ z
      _ = ∫ x, x.2.2 ∂(Measure.map (fun ω' =>
            (P'.instrument ω', P'.observedTreatment ω',
              P'.observedOutcome ω')) μ')[|{x | x.1 = z}] := by
          rw [h]
      _ = P'.armMean μ' P'.observedOutcome z :=
          (armMean_outcome_eq_integral_map P' μ' z).symm
  have hTr : ∀ z : Bool, P.armMean μ P.treated z =
      P'.armMean μ' P'.treated z := by
    intro z
    calc P.armMean μ P.treated z
        = ∫ x, (if x.2.1 then (1 : ℝ) else 0) ∂(Measure.map
            (fun ω => (P.instrument ω, P.observedTreatment ω,
              P.observedOutcome ω)) μ)[|{x | x.1 = z}] :=
          armMean_treated_eq_integral_map P μ z
      _ = ∫ x, (if x.2.1 then (1 : ℝ) else 0) ∂(Measure.map
            (fun ω' => (P'.instrument ω', P'.observedTreatment ω',
              P'.observedOutcome ω')) μ')[|{x | x.1 = z}] := by
          rw [h]
      _ = P'.armMean μ' P'.treated z :=
          (armMean_treated_eq_integral_map P' μ' z).symm
  unfold PotentialOutcomes.waldEstimand
  rw [hOut true, hOut false, hTr true, hTr false]

/-- Identification of the complier average effect from the joint
distribution of (Y, D, Z) (Imbens & Angrist 1994, Theorem 1, with the
Atlas joint random-assignment form of Condition 1). -/
theorem late_eq_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : PotentialOutcomes Ω) (P' : PotentialOutcomes Ω')
    (μ : Measure Ω) (μ' : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hind : P.Independence μ) (hexcl : P.Exclusion)
    (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0)
    (hC : μ P.compliers ≠ 0)
    (hind' : P'.Independence μ') (hexcl' : P'.Exclusion)
    (hmono' : P'.Monotonicity)
    (hY' : ∀ z d, Integrable (P'.outcome z d) μ')
    (hZ' : ∀ z, μ' (P'.instrument ⁻¹' {z}) ≠ 0)
    (hC' : μ' P'.compliers ≠ 0)
    (hmap : Measure.map (fun ω =>
        (P.instrument ω, P.observedTreatment ω, P.observedOutcome ω)) μ =
      Measure.map (fun ω' =>
        (P'.instrument ω', P'.observedTreatment ω',
          P'.observedOutcome ω')) μ')
    (z z' : Bool) :
    ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] =
      ∫ ω, P'.outcome z' true ω - P'.outcome z' false ω ∂μ'[|
        P'.compliers] := by
  rw [← P.waldEstimand_eq_late hind hexcl hmono hY hZ hC z]
  rw [← P'.waldEstimand_eq_late hind' hexcl' hmono' hY' hZ' hC' z']
  exact waldEstimand_eq_of_map_eq P P' μ μ' hmap

end MathlibExt.Probability.Causality
