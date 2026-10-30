/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StochasticOrder.StrassenFinite
public import MathlibExt.Probability.CorrelationInequalities.FKG
/-!
# Holley's inequality and the Holley coupling

Holley's lattice condition on two mass functions on `{0,1}^E` gives stochastic domination and a
monotone coupling of the corresponding measures.

## i. Overview

For a finite edge set `E`, a mass function `μ : ConfigSpace E → ℝ` defines the finite measure
`measOfMass μ = ∑_ω μ(ω) δ_ω`. Holley's theorem says: if `μ₁, μ₂ ≥ 0` have equal total mass and
satisfy the Holley lattice condition

  `μ₁(a) μ₂(b) ≤ μ₁(a ∧ b) μ₂(a ∨ b)` for all `a, b`,

then `μ₁` is stochastically dominated by `μ₂`: `μ₁(A) ≤ μ₂(A)` for every increasing event `A`.
The real-valued inequality is `StatMech.holley_dominates` (from Mathlib's `holley` in
`Mathlib.Combinatorics.SetFamily.FourFunctions`); this file restates it for the measures
`measOfMass μᵢ` and, through Strassen's theorem
`StatMech.exists_monotoneCoupling_of_stochasticallyDominated`, produces a monotone coupling:
a measure on pairs with marginals `μ₁`, `μ₂` that is concentrated on `{(a, b) | a ≤ b}`.
This is the comparison tool for random-cluster measures with different parameters.

## ii. Key results

- `StatMech.FK.measOfMass` : the finite measure with point masses `μ(ω)`, with
  `measOfMass_eq_toMeasure` relating it to `PMF.toMeasure`.
- `StatMech.FK.holley_stochasticallyDominated` : Holley's inequality for `measOfMass`.
- `StatMech.FK.holley_exists_monotoneCoupling` : Holley's coupling theorem.

## iii. Table of contents

- A. Measures from mass functions
- B. Holley's inequality and coupling

## iv. References

- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
- V. Strassen, *The existence of probability measures with given marginals*, Ann. Math. Statist.
  36 (1965).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 2.

-/

@[expose] public section

open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]

/-!

## A. Measures from mass functions

-/

/-- The finite measure `∑_ω μ(ω) δ_ω` on `ConfigSpace E` with point masses `μ(ω)` (negative
masses are truncated to `0`). For a normalized nonnegative `μ` it is the measure of the `PMF`
`PMF.ofFintype μ`; see `measOfMass_eq_toMeasure`. -/
noncomputable def measOfMass (μ : ConfigSpace E → ℝ) : Measure (ConfigSpace E) :=
  ∑ ω : ConfigSpace E, (ENNReal.ofReal (μ ω)) • Measure.dirac ω

open scoped Classical in
lemma measOfMass_apply (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) :
    measOfMass μ A
      = ∑ ω : ConfigSpace E, if ω ∈ A then ENNReal.ofReal (μ ω) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold measOfMass
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- `measOfMass μ` is a finite measure. -/
instance (μ : ConfigSpace E → ℝ) : IsFiniteMeasure (measOfMass μ) := by
  classical
  refine ⟨?_⟩
  rw [measOfMass_apply]
  simp only [Set.mem_univ, ite_true]
  exact ENNReal.sum_lt_top.2 (fun ω _ => ENNReal.ofReal_lt_top)

lemma measOfMass_isProbabilityMeasure (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ)
    (hsum : ∑ ω, μ ω = 1) : IsProbabilityMeasure (measOfMass μ) := by
  classical
  refine ⟨?_⟩
  rw [measOfMass_apply]
  simp only [Set.mem_univ, ite_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hμ ω), hsum, ENNReal.ofReal_one]

/-- For a normalized nonnegative mass function, `measOfMass μ` is the measure of the `PMF`
`PMF.ofFintype (ENNReal.ofReal ∘ μ)`. -/
lemma measOfMass_eq_toMeasure (μ : ConfigSpace E → ℝ)
    (h : ∑ ω, ENNReal.ofReal (μ ω) = 1) :
    measOfMass μ = (PMF.ofFintype (fun ω => ENNReal.ofReal (μ ω)) h).toMeasure := by
  classical
  ext A hA
  rw [measOfMass_apply, PMF.toMeasure_apply_fintype]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω ∈ A <;> simp [hω, Set.indicator]

open scoped Classical in
lemma measOfMass_real (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ) (A : Set (ConfigSpace E)) :
    (measOfMass μ).real A = ∑ ω : ConfigSpace E, if ω ∈ A then μ ω else 0 := by
  rw [measureReal_def, measOfMass_apply]
  rw [ENNReal.toReal_sum (fun ω _ => by split_ifs <;> simp)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω ∈ A
  · simp [hω, ENNReal.toReal_ofReal (hμ ω)]
  · simp [hω]

open scoped Classical in
lemma measOfMass_real_eq_indicator_sum (μ : ConfigSpace E → ℝ) (hμ : 0 ≤ μ)
    (A : Set (ConfigSpace E)) :
    (measOfMass μ).real A = ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω * μ ω := by
  rw [measOfMass_real μ hμ A]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

/-!

## B. Holley's inequality and coupling

-/

/-- **Holley's inequality.** If `μ₁, μ₂ ≥ 0` on `{0,1}^E` have equal total mass and satisfy
the Holley lattice condition `μ₁(a) μ₂(b) ≤ μ₁(a ∧ b) μ₂(a ∨ b)`, then `measOfMass μ₁` is
stochastically dominated by `measOfMass μ₂`. Strict positivity, assumed in Holley's paper, is not
needed. See R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974); the
real-valued form is `StatMech.holley_dominates`, from Mathlib's `holley`. -/
theorem holley_stochasticallyDominated {μ₁ μ₂ : ConfigSpace E → ℝ}
    (h₁ : 0 ≤ μ₁) (h₂ : 0 ≤ μ₂) (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
    (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
    measOfMass μ₁ ≼ measOfMass μ₂ := by
  intro A _ hAinc
  rw [measOfMass_real_eq_indicator_sum μ₁ h₁ A, measOfMass_real_eq_indicator_sum μ₂ h₂ A]
  exact holley_dominates h₁ h₂ hsum hcond hAinc

/-- **Holley's coupling theorem.** If `μ₁, μ₂` are strictly positive probability mass functions
on `{0,1}^E` satisfying the Holley lattice condition `μ₁(a) μ₂(b) ≤ μ₁(a ∧ b) μ₂(a ∨ b)`, there
is a finite measure on pairs with marginals `measOfMass μ₁` and `measOfMass μ₂`, concentrated on
`{(a, b) | a ≤ b}`. See R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36
(1974), and G. Grimmett, *The Random-Cluster Model* (2006), Chapter 2. -/
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

end FK

end StatMech
