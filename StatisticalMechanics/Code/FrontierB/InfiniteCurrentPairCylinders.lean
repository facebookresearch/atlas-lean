/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.JointCurrentSubsequence

open Filter MeasureTheory Topology

namespace StatMech.FrontierB

variable {E : Type*} [Countable E]

def restrictCurrentPair (S : Finset E)
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) :
    (↑S → ℕ) × (↑S → ℕ) :=
  (restrictCurrent S n.1, restrictCurrent S n.2)

omit [Countable E] in
theorem continuous_restrictCurrentPair (S : Finset E) :
    Continuous (restrictCurrentPair S :
      InfiniteCurrentConfig E × InfiniteCurrentConfig E →
        (↑S → ℕ) × (↑S → ℕ)) :=
  (continuous_restrictCurrent S).comp continuous_fst |>.prodMk
    ((continuous_restrictCurrent S).comp continuous_snd)

def currentPairCylinder (S : Finset E) (A : Set ((↑S → ℕ) × (↑S → ℕ))) :
    Set (InfiniteCurrentConfig E × InfiniteCurrentConfig E) :=
  restrictCurrentPair S ⁻¹' A

omit [Countable E] in
theorem isClopen_currentPairCylinder (S : Finset E)
    (A : Set ((↑S → ℕ) × (↑S → ℕ))) :
    IsClopen (currentPairCylinder S A) := by
  exact IsClopen.preimage ⟨isClosed_discrete A, isOpen_discrete A⟩
    (continuous_restrictCurrentPair S)

theorem measurableSet_currentPairCylinder (S : Finset E)
    (A : Set ((↑S → ℕ) × (↑S → ℕ))) :
    MeasurableSet (currentPairCylinder S A) :=
  (continuous_restrictCurrentPair S).measurable MeasurableSet.of_discrete

theorem WeakCurrentConverges.pairCylinder
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (S : Finset E) (A : Set ((↑S → ℕ) × (↑S → ℕ))) :
    Tendsto
      (fun k => (mu k).prod (nu k) (currentPairCylinder S A)) atTop
      (nhds (muLim.prod nuLim (currentPairCylinder S A))) := by
  have hpair : Tendsto (fun k => (mu k, nu k)) atTop (nhds (muLim, nuLim)) :=
    hmu.prodMk_nhds hnu
  have hprod : Tendsto (fun k => (mu k).prod (nu k)) atTop
      (nhds (muLim.prod nuLim)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hprod
    (isClopen_currentPairCylinder S A)



theorem WeakCurrentConverges.superposedTrace_real
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (Q : Set (ConfigSpace E)) (hQ : IsClopen Q) :
    Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (superposedCurrentTrace ⁻¹' Q)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (superposedCurrentTrace ⁻¹' Q))) := by
  have hpair : Tendsto (fun k => (mu k, nu k)) atTop
      (nhds (muLim, nuLim)) := hmu.prodMk_nhds hnu
  have hprod : Tendsto (fun k => (mu k).prod (nu k)) atTop
      (nhds (muLim.prod nuLim)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  have hnn := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hprod
    (hQ.preimage continuous_superposedCurrentTrace)
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  have hreal (rho : ProbabilityMeasure
      (InfiniteCurrentConfig E × InfiniteCurrentConfig E)) :
      (((rho (superposedCurrentTrace ⁻¹' Q)) : NNReal) : ℝ) =
        (rho : Measure _).real (superposedCurrentTrace ⁻¹' Q) := by
    rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  simpa only [Function.comp_def, hreal] using hcoe

theorem pairCylinder_limit_identity_of_eventually
    {mu₁ mu₂ nu₁ nu₂ : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {mu₁Lim mu₂Lim nu₁Lim nu₂Lim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu₁ : WeakCurrentConverges mu₁ mu₁Lim)
    (hmu₂ : WeakCurrentConverges mu₂ mu₂Lim)
    (hnu₁ : WeakCurrentConverges nu₁ nu₁Lim)
    (hnu₂ : WeakCurrentConverges nu₂ nu₂Lim)
    (S T : Finset E)
    (A : Set ((↑S → ℕ) × (↑S → ℕ)))
    (B : Set ((↑T → ℕ) × (↑T → ℕ)))
    (hid : ∀ᶠ k in atTop,
      (mu₁ k).prod (mu₂ k) (currentPairCylinder S A) =
        (nu₁ k).prod (nu₂ k) (currentPairCylinder T B)) :
    mu₁Lim.prod mu₂Lim (currentPairCylinder S A) =
      nu₁Lim.prod nu₂Lim (currentPairCylinder T B) := by
  have hleft := hmu₁.pairCylinder hmu₂ S A
  have hright := hnu₁.pairCylinder hnu₂ T B
  exact tendsto_nhds_unique (hleft.congr' hid) hright

end StatMech.FrontierB
