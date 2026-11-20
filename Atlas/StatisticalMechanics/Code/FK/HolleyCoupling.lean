/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Code.Foundations.StrassenFull
import Code.Inequalities.FKG

open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]





noncomputable def measOfMass (μ : ConfigSpace E → ℝ) : Measure (ConfigSpace E) :=
  ∑ ω : ConfigSpace E, (ENNReal.ofReal (μ ω)) • Measure.dirac ω

open scoped Classical in


theorem measOfMass_apply (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) :
    measOfMass μ A
      = ∑ ω : ConfigSpace E, if ω ∈ A then ENNReal.ofReal (μ ω) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold measOfMass
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hω : ω ∈ A <;> simp [hω]

instance (μ : ConfigSpace E → ℝ) : IsFiniteMeasure (measOfMass μ) := by
  classical
  refine ⟨?_⟩
  rw [measOfMass_apply]
  simp only [Set.mem_univ, if_true]
  exact ENNReal.sum_lt_top.2 (fun ω _ => ENNReal.ofReal_lt_top)



theorem measOfMass_isProbabilityMeasure (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ)
    (hsum : ∑ ω, μ ω = 1) : IsProbabilityMeasure (measOfMass μ) := by
  classical
  refine ⟨?_⟩
  rw [measOfMass_apply]
  simp only [Set.mem_univ, if_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hμ ω), hsum, ENNReal.ofReal_one]

open scoped Classical in


theorem measOfMass_real (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ) (A : Set (ConfigSpace E)) :
    (measOfMass μ).real A = ∑ ω : ConfigSpace E, if ω ∈ A then μ ω else 0 := by
  rw [measureReal_def, measOfMass_apply]
  rw [ENNReal.toReal_sum (fun ω _ => by split_ifs <;> simp)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω ∈ A
  · simp [hω, ENNReal.toReal_ofReal (hμ ω)]
  · simp [hω]

open scoped Classical in


theorem measOfMass_real_eq_indicator_sum (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ)
    (A : Set (ConfigSpace E)) :
    (measOfMass μ).real A = ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω * μ ω := by
  rw [measOfMass_real μ hμ A]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]











theorem holley_stochasticallyDominated {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 ≤ μ₁) (h₂ : 0 ≤ μ₂) (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
    measOfMass μ₁ ≼ measOfMass μ₂ := by
  intro A _ hAinc
  rw [measOfMass_real_eq_indicator_sum μ₁ h₁ A, measOfMass_real_eq_indicator_sum μ₂ h₂ A]
  exact holley_dominates h₁ h₂ hsum hcond hAinc

















theorem holley_exists_monotoneCoupling {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 < μ₁) (h₂ : 0 < μ₂)
    (hn₁ : ∑ ω, μ₁ ω = 1) (hn₂ : ∑ ω, μ₂ ω = 1)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
    ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
      IsFiniteMeasure κ ∧ MonotoneCoupling (measOfMass μ₁) (measOfMass μ₂) κ := by
  have hp₁ : 0 ≤ μ₁ := le_of_lt h₁
  have hp₂ : 0 ≤ μ₂ := le_of_lt h₂
  have : IsProbabilityMeasure (measOfMass μ₁) :=
    measOfMass_isProbabilityMeasure μ₁ hp₁ hn₁
  have : IsProbabilityMeasure (measOfMass μ₂) :=
    measOfMass_isProbabilityMeasure μ₂ hp₂ hn₂
  exact exists_monotoneCoupling_of_stochasticallyDominated _ _
    (holley_stochasticallyDominated hp₁ hp₂ (hn₁.trans hn₂.symm) hcond)









theorem holley_dominates_measure {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 < μ₁) (h₂ : 0 < μ₂)
    (hn₁ : ∑ ω, μ₁ ω = 1) (hn₂ : ∑ ω, μ₂ ω = 1)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
    measOfMass μ₁ ≼ measOfMass μ₂ :=
  holley_stochasticallyDominated (le_of_lt h₁) (le_of_lt h₂)
    (hn₁.trans hn₂.symm) hcond

end FK

end StatMech
