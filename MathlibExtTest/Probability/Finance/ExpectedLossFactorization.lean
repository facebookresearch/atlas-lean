/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ExpectedLossFactorization

/-! # Tests for `MathlibExt.Probability.Finance.ExpectedLossFactorization` -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Finance.ExpectedLossFactorization

namespace MathlibExtTest.ExpectedLossFactorization

section Examples

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => (200 : ℝ)) (fun _ => (0.45 : ℝ)) = 90 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have hInt : IntegrableOn
      (fun ω => (fun _ => (200 : ℝ)) ω * (fun _ => (0.45 : ℝ)) ω) Set.univ μ := by
    rw [integrableOn_univ]
    show Integrable (fun _ => (200 : ℝ) * 0.45) μ
    exact integrable_const _
  have hIntLGD : IntegrableOn (fun _ => (0.45 : ℝ)) Set.univ μ := by
    rw [integrableOn_univ]
    exact integrable_const _
  have h := expectedLoss_eq_pd_mul_lgd_mul_ead (μ := μ) (D := Set.univ)
    (EAD := fun _ => (200 : ℝ)) (LGD := fun _ => (0.45 : ℝ))
    (ead := (200 : ℝ)) (lgd := (0.45 : ℝ))
    MeasurableSet.univ hμuniv (fun _ _ => rfl) (fun _ _ => rfl) hInt hIntLGD
  have hPD : defaultProbability μ Set.univ = 1 := by
    simp only [defaultProbability, Measure.real, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one]
  rw [hPD] at h
  exact h.trans (show (1 : ℝ) * 0.45 * 200 = 90 by norm_num)

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    expectedLoss μ Set.univ (fun _ => (200 : ℝ)) (fun _ => (0.45 : ℝ))
      = 1 * (∫ ω, (0.45 : ℝ) ∂(ProbabilityTheory.cond μ Set.univ)) * 200 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have hInt : IntegrableOn
      (fun ω => (fun _ => (200 : ℝ)) ω * (fun _ => (0.45 : ℝ)) ω) Set.univ μ := by
    rw [integrableOn_univ]
    show Integrable (fun _ => (200 : ℝ) * 0.45) μ
    exact integrable_const _
  have hIntLGD : IntegrableOn (fun _ => (0.45 : ℝ)) Set.univ μ := by
    rw [integrableOn_univ]
    exact integrable_const _
  have h := expectedLoss_eq_defaultProbability_mul_condExpectedLGD_mul_ead
    (μ := μ) (D := Set.univ)
    (EAD := fun _ => (200 : ℝ)) (LGD := fun _ => (0.45 : ℝ)) (ead := (200 : ℝ))
    MeasurableSet.univ hμuniv (fun _ _ => rfl) hInt hIntLGD
  have hPD : defaultProbability μ Set.univ = 1 := by
    simp only [defaultProbability, Measure.real, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one]
  rw [hPD] at h
  exact h

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    1 * (∫ ω, (0.45 : ℝ) ∂(ProbabilityTheory.cond μ Set.univ)) * 200 = 90 := by
  have hμuniv : μ Set.univ ≠ 0 := by simp
  have _hcondProb := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) (s := Set.univ) hμuniv
  rw [integral_const]
  have h1 : (ProbabilityTheory.cond μ Set.univ).real Set.univ = 1 := by
    simp only [Measure.real, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
  rw [h1, one_smul]
  norm_num

end Examples

section ProperDefaultEvent

/-- Four equally likely states: the finite probability space for the
nontrivial-default-event example. -/
noncomputable def μ4 : MeasureTheory.Measure (Fin 4) :=
  (1 / 4 : ENNReal) • MeasureTheory.Measure.count

/-- The default event: the first two states, a proper nonempty event. -/
def D4 : Set (Fin 4) := {0, 1}

/-- EAD: `200` on `D4`, with different values `999` and `888` at the two states
outside `D4` (values outside the default event are irrelevant, not merely
unexercised). -/
def ead4 : Fin 4 → ℝ :=
  fun ω => if ω = 0 then 200 else if ω = 1 then 200 else if ω = 2 then 999 else 888

/-- LGD: `0.45` on `D4`, with different values `0.99` and `0.77` at the two
states outside `D4`. -/
def lgd4 : Fin 4 → ℝ :=
  fun ω => if ω = 0 then 0.45 else if ω = 1 then 0.45 else if ω = 2 then 0.99 else 0.77

/-- `μ4` is a probability measure: four states of mass `1 / 4` each. -/
instance : IsProbabilityMeasure μ4 := ⟨by
  simp [μ4, MeasureTheory.Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel]⟩

/-- Each state has mass `1 / 4`. -/
lemma μ4_singleton (a : Fin 4) : μ4 {a} = 1 / 4 := by
  simp [μ4, MeasureTheory.Measure.smul_apply, smul_eq_mul]

/-- The default event as a disjoint union of its two states. -/
lemma D4_eq_union : D4 = ({0} : Set (Fin 4)) ∪ {1} := by
  rw [D4]; exact Set.insert_eq _ _

/-- EAD is the constant `200` on the default event. -/
lemma ead4_eq_on_D4 : ∀ ω ∈ D4, ead4 ω = 200 := by
  intro ω hω
  simp only [D4, Set.mem_insert_iff, Set.mem_singleton_iff] at hω
  rcases hω with rfl | rfl <;> simp [ead4]

/-- LGD is the constant `0.45` on the default event. -/
lemma lgd4_eq_on_D4 : ∀ ω ∈ D4, lgd4 ω = 0.45 := by
  intro ω hω
  simp only [D4, Set.mem_insert_iff, Set.mem_singleton_iff] at hω
  rcases hω with rfl | rfl <;> simp [lgd4]

/-- **Independently computed default probability**: `PD = 2 / 4 = 1 / 2`. -/
lemma defaultProbability_μ4_D4 : defaultProbability μ4 D4 = 1 / 2 := by
  simp only [defaultProbability, MeasureTheory.Measure.real]
  rw [D4_eq_union, measure_union (by simp [Set.disjoint_singleton])
    (MeasurableSet.singleton 1), μ4_singleton, μ4_singleton,
    ENNReal.toReal_add (by simp) (by simp)]
  simp [ENNReal.toReal_div]
  norm_num

/-- **Nontrivial default event**: expected loss is `PD × LGD × EAD =
1 / 2 × 0.45 × 200 = 45`, via the factorization theorem. -/
example : expectedLoss μ4 D4 ead4 lgd4 = 45 := by
  have hμD : μ4 D4 ≠ 0 := by
    rw [D4_eq_union, measure_union (by simp [Set.disjoint_singleton])
      (MeasurableSet.singleton 1), μ4_singleton, μ4_singleton]
    exact add_ne_zero.mpr (Or.inl (by norm_num))
  have hInt : IntegrableOn (fun ω => ead4 ω * lgd4 ω) D4 μ4 :=
    IntegrableOn.of_finite (Set.toFinite _)
  have hIntLGD : IntegrableOn lgd4 D4 μ4 := IntegrableOn.of_finite (Set.toFinite _)
  have h := expectedLoss_eq_pd_mul_lgd_mul_ead (μ := μ4) (D := D4)
    (EAD := ead4) (LGD := lgd4) (ead := (200 : ℝ)) (lgd := (0.45 : ℝ))
    (DiscreteMeasurableSpace.forall_measurableSet _) hμD ead4_eq_on_D4 lgd4_eq_on_D4
    hInt hIntLGD
  rw [defaultProbability_μ4_D4] at h
  exact h.trans (by norm_num)

/-- **Direct computation**: the expected loss is `45`, without using the
factorization theorem, so the value above is independently checked. -/
example : expectedLoss μ4 D4 ead4 lgd4 = 45 := by
  unfold expectedLoss
  rw [MeasureTheory.integral_fintype Integrable.of_finite]
  simp [Fin.sum_univ_four, μ4, D4, ead4, lgd4, MeasureTheory.Measure.smul_apply,
    smul_eq_mul, MeasureTheory.Measure.real]
  norm_num

end ProperDefaultEvent

end MathlibExtTest.ExpectedLossFactorization
