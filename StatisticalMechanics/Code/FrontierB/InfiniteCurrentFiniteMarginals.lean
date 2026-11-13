/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.InfiniteCurrentTopology

open Filter MeasureTheory Topology

namespace StatMech
namespace FrontierB



def currentCylinder {E : Type*} (S : Finset E) (A : Set (↑S → ℕ)) :
    Set (InfiniteCurrentConfig E) := restrictCurrent S ⁻¹' A



theorem isClopen_currentCylinder {E : Type*} (S : Finset E) (A : Set (↑S → ℕ)) :
    IsClopen (currentCylinder S A) := by
  apply IsClopen.preimage
  · exact ⟨isClosed_discrete A, isOpen_discrete A⟩
  · exact continuous_restrictCurrent S

theorem measurableSet_currentCylinder {E : Type*} [Countable E]
    (S : Finset E) (A : Set (↑S → ℕ)) :
    MeasurableSet (currentCylinder S A) :=
  (continuous_restrictCurrent S).measurable MeasurableSet.of_discrete



theorem currentMarginal_apply {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E)
    (A : Set (↑S → ℕ)) :
    (currentMarginal mu S : Measure (↑S → ℕ)) A =
      (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S A) := by
  change Measure.map (restrictCurrent S) (mu : Measure (InfiniteCurrentConfig E)) A = _
  rw [Measure.map_apply (continuous_restrictCurrent S).measurable
    MeasurableSet.of_discrete]
  rfl




theorem WeakCurrentConverges.cylinder {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun k => mu k (currentCylinder S A))
      atTop
      (nhds (nu (currentCylinder S A))) := by
  exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
    (isClopen_currentCylinder S A)


theorem WeakCurrentConverges.marginal_apply {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E) (A : Set (↑S → ℕ)) :
    Tendsto (fun k => currentMarginal (mu k) S A) atTop
      (nhds (currentMarginal nu S A)) := by
  have heq (rho : ProbabilityMeasure (InfiniteCurrentConfig E)) :
      currentMarginal rho S A = rho (currentCylinder S A) := by
    unfold currentMarginal currentCylinder
    exact ProbabilityMeasure.map_apply rho _ MeasurableSet.of_discrete
  simpa only [heq] using h.cylinder S A



theorem restrictCurrent_restrict₂ {E : Type*} {S T : Finset E} (hTS : T ⊆ S)
    (n : InfiniteCurrentConfig E) :
    Finset.restrict₂ (π := fun _ : E => ℕ) hTS (restrictCurrent S n) =
      restrictCurrent T n := by
  rfl


theorem currentMarginal_map_restrict₂ {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) {S T : Finset E}
    (hTS : T ⊆ S) :
    (currentMarginal mu S).map
        (Finset.measurable_restrict₂ (X := fun _ : E => ℕ) hTS).aemeasurable =
      currentMarginal mu T := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [currentMarginal, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map]
  · congr 1
  · exact Finset.measurable_restrict₂ hTS
  · exact (continuous_restrictCurrent S).measurable



theorem ProbabilityMeasure.ext_of_currentMarginal_eq {E : Type*} [Countable E]
    {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : ∀ S : Finset E, currentMarginal mu S = currentMarginal nu S) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => ℕ))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro C hC
    rw [mem_measurableCylinders] at hC
    obtain ⟨S, A, hA, rfl⟩ := hC
    have hmarg := congrArg
      (fun rho : ProbabilityMeasure (↑S → ℕ) => (rho : Measure (↑S → ℕ)) A) (h S)
    simpa only [currentMarginal_apply, currentCylinder, cylinder,
      Finset.restrict] using hmarg
  · rw [measure_univ, measure_univ]

theorem ProbabilityMeasure.ext_iff_currentMarginal_eq {E : Type*} [Countable E]
    {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
    mu = nu ↔ ∀ S : Finset E, currentMarginal mu S = currentMarginal nu S := by
  constructor
  · rintro rfl S
    rfl
  · exact ProbabilityMeasure.ext_of_currentMarginal_eq

end FrontierB
end StatMech
