/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.MultivaluedMap

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

namespace StatMech.FrontierA

variable {Omega I : Type*} [MeasurableSpace Omega]


noncomputable def finiteEventMultiplicity (J : Finset I) (A : I → Set Omega)
    (omega : Omega) : Nat := by
  classical
  exact (J.filter fun i => omega ∈ A i).card

theorem finiteEventMultiplicity_eq_sum_indicator
    (J : Finset I) (A : I → Set Omega) (omega : Omega) :
    (finiteEventMultiplicity J A omega : ℝ≥0∞) =
      ∑ i ∈ J, (A i).indicator (fun _ => (1 : ℝ≥0∞)) omega := by
  classical
  unfold finiteEventMultiplicity
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmem : omega ∈ A i
  · simp [hmem]
  · simp [hmem]


theorem lintegral_finiteEventMultiplicity
    (mu : Measure Omega) (J : Finset I) (A : I → Set Omega)
    (hA : ∀ i ∈ J, MeasurableSet (A i)) :
    ∫⁻ omega, (finiteEventMultiplicity J A omega : ℝ≥0∞) ∂mu =
      ∑ i ∈ J, mu (A i) := by
  classical
  calc
    ∫⁻ omega, (finiteEventMultiplicity J A omega : ℝ≥0∞) ∂mu =
        ∫⁻ omega, ∑ i ∈ J,
          (A i).indicator (fun _ => (1 : ℝ≥0∞)) omega ∂mu := by
      apply lintegral_congr
      exact fun omega => finiteEventMultiplicity_eq_sum_indicator J A omega
    _ = ∑ i ∈ J, ∫⁻ omega,
        (A i).indicator (fun _ => (1 : ℝ≥0∞)) omega ∂mu := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro i hi
      exact Measurable.indicator measurable_const (hA i hi)
    _ = ∑ i ∈ J, mu (A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_indicator_one (hA i hi)


theorem finiteEventMultivalued_probability_bound
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (J : Finset I) (source target : I → Set Omega)
    (hsourceMeas : ∀ i ∈ J, MeasurableSet (source i))
    (htargetMeas : ∀ i ∈ J, MeasurableSet (target i))
    (E : Set Omega) (hEMeas : MeasurableSet E)
    (c : ℝ≥0∞) (K L : Nat)
    (hsourceDegree : ∀ omega ∈ E,
      K ≤ finiteEventMultiplicity J source omega)
    (htargetDegree : ∀ omega,
      finiteEventMultiplicity J target omega ≤ L)
    (htransfer : ∀ i ∈ J, c * mu (source i) ≤ mu (target i)) :
    c * K * mu E ≤ L := by
  classical
  have hsourceIntegral : (K : ℝ≥0∞) * mu E ≤
      ∫⁻ omega, (finiteEventMultiplicity J source omega : ℝ≥0∞) ∂mu := by
    calc
      (K : ℝ≥0∞) * mu E =
          ∫⁻ omega, E.indicator (fun _ => (K : ℝ≥0∞)) omega ∂mu := by
        rw [lintegral_indicator hEMeas]
        simp
      _ ≤ ∫⁻ omega,
          (finiteEventMultiplicity J source omega : ℝ≥0∞) ∂mu := by
        apply lintegral_mono
        intro omega
        by_cases homega : omega ∈ E
        · simp only [Set.indicator_of_mem homega]
          exact_mod_cast hsourceDegree omega homega
        · simp [Set.indicator_of_notMem homega]
  have htargetIntegral :
      (∫⁻ omega, (finiteEventMultiplicity J target omega : ℝ≥0∞) ∂mu) ≤ L := by
    calc
      (∫⁻ omega, (finiteEventMultiplicity J target omega : ℝ≥0∞) ∂mu) ≤
          ∫⁻ _omega : Omega, (L : ℝ≥0∞) ∂mu := by
        apply lintegral_mono
        intro omega
        change (finiteEventMultiplicity J target omega : ℝ≥0∞) ≤
          (L : ℝ≥0∞)
        exact_mod_cast htargetDegree omega
      _ = L := by simp
  calc
    c * K * mu E = c * ((K : ℝ≥0∞) * mu E) := by ring
    _ ≤ c * ∫⁻ omega,
        (finiteEventMultiplicity J source omega : ℝ≥0∞) ∂mu := by
      gcongr
    _ = c * ∑ i ∈ J, mu (source i) := by
      rw [lintegral_finiteEventMultiplicity mu J source hsourceMeas]
    _ = ∑ i ∈ J, c * mu (source i) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ J, mu (target i) := by
      gcongr with i hi
      exact htransfer i hi
    _ = ∫⁻ omega,
        (finiteEventMultiplicity J target omega : ℝ≥0∞) ∂mu := by
      rw [lintegral_finiteEventMultiplicity mu J target htargetMeas]
    _ ≤ L := htargetIntegral

end StatMech.FrontierA
