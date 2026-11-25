/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Sanov
import Mathlib.Probability.Independence.InfinitePi

open Set MeasureTheory ProbabilityTheory InformationTheory
open MathlibExt.Probability.LargeDeviationPrinciple
open MathlibExt.Probability.SampleEmpiricalMeasure
open MathlibExt.Probability.SanovWanted

namespace MathlibExtTest.Probability.Sanov

private theorem eq_empty_or_univ {α : Type*} [Subsingleton α] (s : Set α) :
    s = ∅ ∨ s = univ := by
  by_cases h : s.Nonempty
  · obtain ⟨a, ha⟩ := h
    exact Or.inr (eq_univ_of_forall fun b => (Subsingleton.elim a b) ▸ ha)
  · exact Or.inl (not_nonempty_iff_eq_empty.mp h)

private theorem probabilityMeasure_subsingleton : Subsingleton (ProbabilityMeasure PUnit) := by
  constructor
  intro μ ν
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  rcases eq_empty_or_univ s with rfl | rfl <;> simp

local instance instOpensMeasurableProbabilityMeasurePUnit :
    OpensMeasurableSpace (ProbabilityMeasure PUnit) := by
  have := probabilityMeasure_subsingleton
  constructor
  intro s _
  rcases eq_empty_or_univ s with rfl | rfl <;> simp

private noncomputable def pointLaw : ProbabilityMeasure PUnit :=
  ⟨Measure.dirac PUnit.unit, inferInstance⟩

private noncomputable def sampleLaw : Measure (ℕ → PUnit) :=
  Measure.infinitePi (fun _ => (pointLaw : Measure PUnit))

local instance instProbabilitySampleLaw : IsProbabilityMeasure sampleLaw := by
  unfold sampleLaw
  infer_instance

/-- A constant sample witnesses all hypotheses, including open-set measurability. -/
example :
    SatisfiesLDP (fun n => sampleLaw.map (fun x => sampleEmpiricalMeasure x n))
      (fun β : ProbabilityMeasure PUnit => klDiv (β : Measure PUnit) pointLaw) ∧
    IsGoodRateFunction (fun β : ProbabilityMeasure PUnit =>
      klDiv (β : Measure PUnit) pointLaw) := by
  exact satisfiesLDP_sampleEmpiricalMeasure
    (Xs := fun i (x : ℕ → PUnit) => x i) (P := sampleLaw)
    (hmeas := fun i => measurable_pi_apply i)
    (hindep := iIndepFun_infinitePi (fun _ => measurable_id))
    pointLaw (hlaw := fun i => Measure.infinitePi_map_eval _ i)

/-- The size-zero convention gives the same point mass and zero entropy as a nonempty sample. -/
example (x : ℕ → PUnit) (n : ℕ) :
    klDiv (sampleEmpiricalMeasure x n : Measure PUnit) pointLaw = 0 := by
  have := probabilityMeasure_subsingleton
  rw [Subsingleton.elim (sampleEmpiricalMeasure x n) pointLaw, klDiv_self]

end MathlibExtTest.Probability.Sanov
