/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Foundations.Prokhorov
import Code.Foundations.StochasticDomination

open MeasureTheory TopologicalSpace Filter Topology MeasurableSpace
open scoped ENNReal NNReal Topology

namespace StatMech

variable {E : Type*} [Countable E]









omit [Countable E] in




theorem isClopen_cylinderEvent (s : Finset E) (S : Set (∀ _i : s, Bool)) :
    IsClopen (cylinder (α := fun _ : E => Bool) s S) := by
  apply IsClopen.preimage
  · exact isClopen_discrete S
  · exact continuous_pi (fun i => continuous_apply i.1)


theorem IsClopen.measurableSet_configSpace {A : Set (ConfigSpace E)} (hA : IsClopen A) :
    MeasurableSet A := hA.isOpen.measurableSet








omit [Countable E] in



theorem ProbabilityMeasure.coe_apply_eq_real
    (μ : ProbabilityMeasure (ConfigSpace E)) (A : Set (ConfigSpace E)) :
    ((μ A : NNReal) : ℝ) = (μ : Measure (ConfigSpace E)).real A := by
  rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact (ENNReal.coe_toReal _).symm






theorem WeakConvergesTo.tendsto_real_of_isClopen
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν) {A : Set (ConfigSpace E)} (hA : IsClopen A) :
    Tendsto (fun n => (μ n : Measure (ConfigSpace E)).real A) atTop
      (𝓝 ((ν : Measure (ConfigSpace E)).real A)) := by
  have hnn : Tendsto (fun n => ((μ n) A : NNReal)) atTop (𝓝 ((ν : ProbabilityMeasure _) A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h hA
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  simp only [Function.comp_def, ProbabilityMeasure.coe_apply_eq_real] at hcoe
  exact hcoe








omit [Countable E] in


theorem monotone_real_of_chain
    {μ : ℕ → Measure (ConfigSpace E)}
    (hchain : ∀ n, μ n ≼ μ (n + 1))
    {A : Set (ConfigSpace E)} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    Monotone (fun n => (μ n).real A) :=
  monotone_nat_of_le_succ fun n => hchain n A hAmeas hAinc

omit [Countable E] in


theorem antitone_real_of_chain
    {μ : ℕ → Measure (ConfigSpace E)}
    (hchain : ∀ n, μ (n + 1) ≼ μ n)
    {A : Set (ConfigSpace E)} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    Antitone (fun n => (μ n).real A) :=
  antitone_nat_of_succ_le fun n => hchain n A hAmeas hAinc












theorem WeakConvergesTo.le_real_of_monotone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) (n : ℕ) :
    (μ n : Measure (ConfigSpace E)).real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  (monotone_real_of_chain hchain (IsClopen.measurableSet_configSpace hAclopen) hAinc).ge_of_tendsto
    (h.tendsto_real_of_isClopen hAclopen) n










theorem WeakConvergesTo.ge_real_of_antitone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) (n : ℕ) :
    (ν : Measure (ConfigSpace E)).real A ≤ (μ n : Measure (ConfigSpace E)).real A :=
  (antitone_real_of_chain hchain (IsClopen.measurableSet_configSpace hAclopen) hAinc).le_of_tendsto
    (h.tendsto_real_of_isClopen hAclopen) n







theorem le_real_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (_hAinc : IsIncreasing A)
    (hbound : ∀ n, ρ.real A ≤ (μ n : Measure (ConfigSpace E)).real A) :
    ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  ge_of_tendsto (h.tendsto_real_of_isClopen hAclopen)
    (Filter.Eventually.of_forall hbound)




theorem real_le_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A)
    (hbound : ∀ n, (μ n : Measure (ConfigSpace E)).real A ≤ ρ.real A) :
    (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A :=
  le_of_tendsto (h.tendsto_real_of_isClopen hAclopen)
    (Filter.Eventually.of_forall hbound)













theorem dominated_weakLimit_of_forall_dominated
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hdom : ∀ n, ρ ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  le_real_of_weakLimit h hAclopen hAinc
    (fun n => hdom n A (IsClopen.measurableSet_configSpace hAclopen) hAinc)





theorem weakLimit_dominated_of_forall_dominated
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hdom : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ ρ)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A :=
  real_le_of_weakLimit h hAclopen
    (fun n => hdom n A (IsClopen.measurableSet_configSpace hAclopen) hAinc)







omit [Countable E] in





theorem ProbabilityMeasure.ext_of_forall_isClopen
    {μ ν : ProbabilityMeasure (ConfigSpace E)}
    (h : ∀ A : Set (ConfigSpace E), IsClopen A → μ A = ν A) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro s hs
    rw [mem_measurableCylinders] at hs
    obtain ⟨t, S, _hS, rfl⟩ := hs
    have hclopen := isClopen_cylinderEvent t S
    have hμν := h _ hclopen
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hμν]
  · rw [measure_univ, measure_univ]





theorem isClopen_apply_eq_of_subseq_tendsto
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {L : Set (ConfigSpace E) → NNReal}
    (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A)))
    {ξ : ProbabilityMeasure (ConfigSpace E)} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (htends : Tendsto (μ ∘ ψ) atTop (𝓝 ξ))
    {A : Set (ConfigSpace E)} (hA : IsClopen A) :
    (ξ A : NNReal) = L A := by
  have hport : Tendsto (fun n => (μ ∘ ψ) n A) atTop (𝓝 (ξ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto htends hA
  have hsub : Tendsto (fun n => (μ ∘ ψ) n A) atTop (𝓝 (L A)) :=
    (hconv A hA).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hport hsub













theorem tendsto_weakly_of_forall_isClopen_tendsto
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {L : Set (ConfigSpace E) → NNReal}
    (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A))) :
    ∃ ν : ProbabilityMeasure (ConfigSpace E), WeakConvergesTo μ ν := by
  obtain ⟨ν, φ, hφ, hν⟩ := prokhorov_seq_compact μ
  refine ⟨ν, ?_⟩
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ξ hξ
  obtain ⟨ψ, hψ, htends_ξ⟩ := hξ.tendsto_subseq
  apply ProbabilityMeasure.ext_of_forall_isClopen
  intro A hA
  have hξA : (ξ A : NNReal) = L A :=
    isClopen_apply_eq_of_subseq_tendsto hconv hψ htends_ξ hA
  have hνA : (ν A : NNReal) = L A :=
    isClopen_apply_eq_of_subseq_tendsto hconv hφ hν hA
  rw [hξA, hνA]










omit [Countable E] in

theorem apply_le_one (μ : ProbabilityMeasure (ConfigSpace E)) (A : Set (ConfigSpace E)) :
    (μ A : NNReal) ≤ 1 := by
  calc (μ A : NNReal) ≤ μ Set.univ := by gcongr; exact Set.subset_univ _
    _ = 1 := by simp







theorem tendsto_NNReal_of_monotone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (⨆ n, (μ n) A)) := by
  have hAmeas := IsClopen.measurableSet_configSpace hAclopen
  have hmono : Monotone (fun n => (μ n) A) := by
    apply monotone_nat_of_le_succ
    intro n
    
    have hreal : (μ n : Measure (ConfigSpace E)).real A
        ≤ (μ (n + 1) : Measure (ConfigSpace E)).real A := hchain n A hAmeas hAinc
    rw [← ProbabilityMeasure.coe_apply_eq_real, ← ProbabilityMeasure.coe_apply_eq_real] at hreal
    exact_mod_cast hreal
  have hbdd : BddAbove (Set.range (fun n => (μ n) A)) :=
    ⟨1, by rintro x ⟨n, rfl⟩; exact apply_le_one _ _⟩
  exact tendsto_atTop_ciSup hmono hbdd

end StatMech
