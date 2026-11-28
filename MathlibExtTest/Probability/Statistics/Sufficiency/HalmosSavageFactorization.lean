/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Sufficiency.HalmosSavageFactorization

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency
open scoped ENNReal

-- The parameter space is the power set of ℕ. The sufficient statistic forgets the second
-- coordinate; the family is supported on the slice where that coordinate is false.
example (label : Set ℕ → Bool) :
    ∃ (g : Set ℕ → Bool → ℝ≥0∞) (h : Bool × Bool → ℝ≥0∞),
      (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      ∀ θ ω, g θ ω.1 * h ω = if ω = (label θ, false) then 1 else 0 := by
  classical
  let μ : Measure (Bool × Bool) := Measure.count
  let T : Bool × Bool → Bool := Prod.fst
  let P (θ : Set ℕ) : Measure (Bool × Bool) := Measure.dirac (label θ, false)
  let h (ω : Bool × Bool) : ℝ≥0∞ := if ω.2 = false then 1 else 0
  let g (θ : Set ℕ) (t : Bool) : ℝ≥0∞ := if t = label θ then 1 else 0
  have hT : Measurable T := measurable_fst
  have hh : Measurable h := Measurable.of_discrete
  have hg (θ : Set ℕ) : Measurable (g θ) := Measurable.of_discrete
  have hP (θ : Set ℕ) : IsProbabilityMeasure (P θ) := inferInstance
  have hν : IsFiniteMeasure (μ.withDensity h) := by
    have heq : h = ({ω : Bool × Bool | ω.2 = false} : Set (Bool × Bool)).indicator 1 := by
      funext ω
      simp [h, Set.indicator_apply]
    rw [heq, withDensity_indicator_one (measurableSet_eq_fun measurable_snd measurable_const)]
    infer_instance
  have hfac (θ : Set ℕ) : P θ = μ.withDensity (fun ω => g θ (T ω) * h ω) := by
    have heq : (fun ω => g θ (T ω) * h ω) = ({(label θ, false)} : Set (Bool × Bool)).indicator 1 := by
      ext ⟨a, b⟩
      by_cases ha : a = label θ <;> by_cases hb : b = false <;>
        simp [T, g, h, Prod.mk.injEq, ha, hb]
    rw [heq, withDensity_indicator_one (measurableSet_singleton _), Measure.restrict_singleton]
    simp [μ, P]
  have hsuf := isSufficient_comap_of_factorization_of_sigmaFinite_trim hT μ g hg h hh hfac
  obtain ⟨G, H, hG, hH, hGH⟩ := exists_factorization_of_isSufficient_comap hT μ P
    (fun θ => hfac θ ▸ withDensity_absolutelyContinuous _ _) hsuf
  refine ⟨G, H, hG, hH, fun θ ω => ?_⟩
  have heq := congrArg (fun ν : Measure (Bool × Bool) => ν {ω}) (hGH θ)
  rw [withDensity_apply _ (measurableSet_singleton _), Measure.restrict_singleton] at heq
  simpa [P, T, μ, Measure.count_singleton, Measure.dirac_apply', measurableSet_singleton,
    Set.indicator_apply, eq_comm] using heq.symm

-- No probability-measure instance at a parameter is needed when the family is empty.
example (P : Empty → Measure Bool) :
    ∃ (g : Empty → Bool → ℝ≥0∞) (h : Bool → ℝ≥0∞),
      (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      ∀ θ, P θ = (0 : Measure Bool).withDensity (fun ω => g θ ω * h ω) := by
  have (θ : Empty) : IsProbabilityMeasure (P θ) := θ.elim
  have hP : IsSufficient (MeasurableSpace.comap (id : Bool → Bool) inferInstance) P :=
    ⟨measurable_id.comap_le, isEmptyElim,
      fun _ _ => ⟨fun _ => 0, stronglyMeasurable_const, isEmptyElim⟩⟩
  exact exists_factorization_of_isSufficient_comap measurable_id 0 P isEmptyElim hP
