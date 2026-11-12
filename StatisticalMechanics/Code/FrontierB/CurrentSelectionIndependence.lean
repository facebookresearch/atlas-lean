/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.CurrentParityLimits
import Code.FrontierB.BoxCurrentPatternFactor
import Code.FrontierB.InfiniteCurrentMeasures

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def currentParityMarginalPMF {E : Type*} [Countable E]
    [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E) :
    PMF (↑S → Bool) :=
  (((currentMarginal mu S).map
    (Measurable.of_discrete (f := currentLocalParity)).aemeasurable :
      ProbabilityMeasure (↑S → Bool)) : Measure (↑S → Bool)).toPMF

theorem currentParityMarginalPMF_toMeasure {E : Type*} [Countable E]
    [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E) :
    (currentParityMarginalPMF mu S).toMeasure =
      (((currentMarginal mu S).map
        (Measurable.of_discrete (f := currentLocalParity)).aemeasurable :
          ProbabilityMeasure (↑S → Bool)) : Measure (↑S → Bool)) := by
  exact Measure.toPMF_toMeasure _

def ambientSubfinset {E : Type*} [DecidableEq E]
    (S : Finset E) (T : Finset ↑S) : Finset E :=
  T.map ⟨Subtype.val, Subtype.val_injective⟩

theorem preimage_boolAvoid_currentLocalParity_restrictCurrent
    {E : Type*} [DecidableEq E] (S : Finset E) (T : Finset ↑S) :
    (currentLocalParity ∘ restrictCurrent S) ⁻¹' boolAvoid T =
      currentParityAvoidCylinder (ambientSubfinset S T) := by
  ext m
  simp only [Set.mem_preimage, Function.comp_apply, boolAvoid,
    Set.mem_setOf_eq, currentParityAvoidCylinder]
  rw [Finset.disjoint_left]
  constructor
  · intro h e heT
    have heT' : e ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩ := by
      simpa [ambientSubfinset] using heT
    rw [Finset.mem_map] at heT'
    obtain ⟨i, hiT, rfl⟩ := heT'
    by_contra hneven
    have hodd : Odd (m i.1) := Nat.not_even_iff_odd.mp hneven
    apply h (a := i)
    · simp [boolSupport, currentLocalParity, restrictCurrent, hodd]
    · exact hiT
  · intro h i hiSupp hiT
    have heven : Even (m i.1) := h i.1 (by
      simpa [ambientSubfinset] using
        (Finset.mem_map.mpr ⟨i, hiT, rfl⟩ :
          i.1 ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩))
    have hodd : Odd (m i.1) := by
      simpa [boolSupport, currentLocalParity, restrictCurrent] using hiSupp
    exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem currentParityMarginalPMF_avoid
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (T : Finset ↑S) :
    (currentParityMarginalPMF mu S).toMeasure (boolAvoid T) =
      (mu : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder (ambientSubfinset S T)) := by
  rw [currentParityMarginalPMF_toMeasure]
  change Measure.map currentLocalParity
      (currentMarginal mu S : Measure (↑S → ℕ)) (boolAvoid T) = _
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  change Measure.map (restrictCurrent S)
      (mu : Measure (InfiniteCurrentConfig E))
      (currentLocalParity ⁻¹' boolAvoid T) = _
  rw [Measure.map_apply (continuous_restrictCurrent S).measurable
    MeasurableSet.of_discrete]
  rw [← preimage_boolAvoid_currentLocalParity_restrictCurrent S T]
  rfl

theorem currentParityMarginalPMF_apply
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (odd : ↑S → Bool) :
    currentParityMarginalPMF mu S odd =
      (mu : Measure (InfiniteCurrentConfig E))
        (currentParityPatternCylinder S odd) := by
  rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd),
    currentParityMarginalPMF_toMeasure]
  change Measure.map currentLocalParity
      (currentMarginal mu S : Measure (↑S → ℕ)) {odd} = _
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton odd)]
  change Measure.map (restrictCurrent S)
      (mu : Measure (InfiniteCurrentConfig E))
      (currentLocalParity ⁻¹' {odd}) = _
  rw [Measure.map_apply (continuous_restrictCurrent S).measurable
    MeasurableSet.of_discrete]
  rfl

theorem WeakCurrentConverges.cylinderENNReal
    {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E)
    (A : Set (↑S → ℕ)) :
    Tendsto (fun k => (mu k : Measure (InfiniteCurrentConfig E))
        (currentCylinder S A)) atTop
      (nhds ((nu : Measure (InfiniteCurrentConfig E))
        (currentCylinder S A))) := by
  have hc := (ENNReal.tendsto_coe).2 (h.cylinder S A)
  simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc

theorem currentParityAvoidCylinder_eq_currentCylinder {E : Type*}
    (S : Finset E) :
    currentParityAvoidCylinder S =
      currentCylinder S {a | ∀ i, Even (a i)} := by
  ext m
  simp [currentParityAvoidCylinder, currentCylinder, restrictCurrent]





theorem currentLimit_parityMarginal_eq_of_avoid_tendsto
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (havoid : ∀ A : Finset E, ∃ L : ℝ≥0∞,
      Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) atTop (nhds L))
    (S : Finset E)
    {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges (mu ∘ phi) nu)
    (hrho : WeakCurrentConverges (mu ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  obtain ⟨L, hfull⟩ := havoid A
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  exact (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')



theorem currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (S : Finset E) (kernel : (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
    (hparity : currentParityMarginalPMF mu S =
      currentParityMarginalPMF nu S)
    (hmu : ∀ a : ↑S → ℕ,
      (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a)
    (hnu : ∀ a : ↑S → ℕ,
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a) :
    currentMarginal mu S = currentMarginal nu S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply, hmu a, hnu a]
  congr 1
  have hp := congrArg
    (fun p : PMF (↑S → Bool) => p (currentLocalParity a)) hparity
  simpa only [currentParityMarginalPMF_apply] using hp



theorem ProbabilityMeasure.ext_of_currentParity_and_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (kernel : ∀ S : Finset E, (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
    (hparity : ∀ S, currentParityMarginalPMF mu S =
      currentParityMarginalPMF nu S)
    (hmu : ∀ (S : Finset E) (a : ↑S → ℕ),
      (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a)
    (hnu : ∀ (S : Finset E) (a : ↑S → ℕ),
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a) :
    mu = nu := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact currentMarginal_eq_of_parityMarginal_eq_of_pattern_factor
    mu nu S (kernel S) (hparity S) (hmu S) (hnu S)




theorem WeakCurrentConverges.pattern_factor_of_eventually
    {E : Type*} [Countable E] [DecidableEq E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hnu : WeakCurrentConverges mu nu)
    (S : Finset E) (kernel : (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
    (hkernelTop : ∀ odd a, kernel odd a ≠ ⊤)
    (hfactor : ∀ a : ↑S → ℕ, ∀ᶠ n in atTop,
      (mu n : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (mu n : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel (currentLocalParity a) a)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig E))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        kernel (currentLocalParity a) a := by
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hproduct := (ENNReal.continuous_mul_const
    (hkernelTop (currentLocalParity a) a)).continuousAt.tendsto.comp hparity
  have hpoint' := hpoint
  have hproduct' := hproduct
  have hproductCurrent := hproduct'.congr' (by
    filter_upwards [hfactor a] with n hn
    exact hn.symm)
  exact tendsto_nhds_unique hpoint' hproductCurrent



theorem currentLimit_eq_of_avoid_tendsto_of_pattern_factor
    {E : Type*} [Countable E] [DecidableEq E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (havoid : ∀ A : Finset E, ∃ L : ℝ≥0∞,
      Tendsto (fun n => (mu n : Measure (InfiniteCurrentConfig E))
        (currentParityAvoidCylinder A)) atTop (nhds L))
    (kernel : ∀ S : Finset E,
      (↑S → Bool) → (↑S → ℕ) → ℝ≥0∞)
    {nu rho : ProbabilityMeasure (InfiniteCurrentConfig E)}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges (mu ∘ phi) nu)
    (hrho : WeakCurrentConverges (mu ∘ psi) rho)
    (hnuFactor : ∀ (S : Finset E) (a : ↑S → ℕ),
      (nu : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (nu : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a)
    (hrhoFactor : ∀ (S : Finset E) (a : ↑S → ℕ),
      (rho : Measure (InfiniteCurrentConfig E)) (currentCylinder S {a}) =
        (rho : Measure (InfiniteCurrentConfig E))
            (currentParityPatternCylinder S (currentLocalParity a)) *
          kernel S (currentLocalParity a) a) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentParity_and_pattern_factor
    nu rho kernel
  · intro S
    exact currentLimit_parityMarginal_eq_of_avoid_tendsto
      mu havoid S hphi hpsi hnu hrho
  · exact hnuFactor
  · exact hrhoFactor

theorem ambientSubfinset_lattice
    (d : ℕ) (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (T : Finset ↑S) :
    (↑(ambientSubfinset S T) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  have he' : e ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    simpa [ambientSubfinset] using he
  rw [Finset.mem_map] at he'
  obtain ⟨i, hi, rfl⟩ := he'
  exact hS i.2

theorem plusCurrentLimit_parityMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  have hA : (↑A : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    ambientSubfinset_lattice d S hS T
  have hfull := plusBoxCurrentMeasure_parityAvoid_full_tendsto
    d beta hbeta A hA
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (plusBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (plusBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  simpa [A] using (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')

theorem freeCurrentLimit_parityMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ psi) rho) :
    currentParityMarginalPMF nu S = currentParityMarginalPMF rho S := by
  apply PMF.ext_of_boolAvoid_eq
  intro T
  rw [currentParityMarginalPMF_avoid, currentParityMarginalPMF_avoid]
  let A := ambientSubfinset S T
  have hA : (↑A : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    ambientSubfinset_lattice d S hS T
  have hfull := freeBoxCurrentMeasure_parityAvoid_full_tendsto
    d beta hbeta A hA
  have hsubPhi := hfull.comp hphi.tendsto_atTop
  have hsubPsi := hfull.comp hpsi.tendsto_atTop
  have hportPhi := hnu.cylinder A {a | ∀ i, Even (a i)}
  have hportPsi := hrho.cylinder A {a | ∀ i, Even (a i)}
  rw [← currentParityAvoidCylinder_eq_currentCylinder] at hportPhi hportPsi
  have hportPhi' : Tendsto
      ((fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ phi) atTop
      (nhds ((nu : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPhi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  have hportPsi' : Tendsto
      ((fun n => (freeBoxCurrentMeasure d n beta hbeta : Measure _)
        (currentParityAvoidCylinder A)) ∘ psi) atTop
      (nhds ((rho : Measure _) (currentParityAvoidCylinder A))) := by
    have hc := (ENNReal.tendsto_coe).2 hportPsi
    simpa [Function.comp_def,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hc
  simpa [A] using (tendsto_nhds_unique hsubPhi hportPhi').symm.trans
    (tendsto_nhds_unique hsubPsi hportPsi')

theorem plusCurrentLimit_pattern_factor
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  obtain ⟨N, hSN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d S hS
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hprod := (ENNReal.continuous_mul_const
    (PMF.apply_ne_top
      (finiteParityPMF S beta hbeta (currentLocalParity a)) a)).continuousAt.tendsto.comp
        hparity
  have hev : ∀ᶠ k in atTop,
      (plusBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
          (currentCylinder S {a}) =
        (plusBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
            (currentParityPatternCylinder S (currentLocalParity a)) *
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hindex : N + 1 ≤ phi k := hk.trans (hphi.id_le k)
    let n := phi k - 1
    have hphi_eq : phi k = n + 1 := by omega
    rw [hphi_eq]
    apply plusBoxCurrentMeasure_pattern_factor d n beta hbeta S
      (hSN.trans (StatMech.Ising.bondFinsetTouch_subset (by omega))) a
  have hpoint' := hpoint
  have hprod' := hprod
  simp only [Function.comp_apply] at hpoint' hprod'
  have hprodCurrent := hprod'.congr' (by
    filter_upwards [hev] with k hk
    exact hk.symm)
  exact tendsto_nhds_unique hpoint' hprodCurrent

theorem freeCurrentLimit_pattern_factor
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (a : ↑S → ℕ) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder S (currentLocalParity a)) *
        finiteParityPMF S beta hbeta (currentLocalParity a) a := by
  obtain ⟨N, hSN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d S hS
  have hpoint := hnu.cylinderENNReal S {a}
  have hparity := hnu.cylinderENNReal S
    {b | currentLocalParity b = currentLocalParity a}
  have hprod := (ENNReal.continuous_mul_const
    (PMF.apply_ne_top
      (finiteParityPMF S beta hbeta (currentLocalParity a)) a)).continuousAt.tendsto.comp
        hparity
  have hev : ∀ᶠ k in atTop,
      (freeBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
          (currentCylinder S {a}) =
        (freeBoxCurrentMeasure d (phi k) beta hbeta.le : Measure _)
            (currentParityPatternCylinder S (currentLocalParity a)) *
          finiteParityPMF S beta hbeta (currentLocalParity a) a := by
    filter_upwards [eventually_ge_atTop (N + 1)] with k hk
    have hindex : N + 1 ≤ phi k := hk.trans (hphi.id_le k)
    let n := phi k - 1
    have hphi_eq : phi k = n + 1 := by omega
    rw [hphi_eq]
    apply freeBoxCurrentMeasure_pattern_factor d n beta hbeta S
      (hSN.trans (StatMech.Ising.bondFinsetTouch_subset (by omega))) a
  have hpoint' := hpoint
  have hprod' := hprod
  simp only [Function.comp_apply] at hpoint' hprod'
  have hprodCurrent := hprod'.congr' (by
    filter_upwards [hev] with k hk
    exact hk.symm)
  exact tendsto_nhds_unique hpoint' hprodCurrent

theorem plusCurrentLimit_latticeMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply]
  rw [plusCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a,
    plusCurrentLimit_pattern_factor d beta hbeta S hS hpsi hrho a]
  congr 1
  have hp := congrArg (fun p : PMF (↑S → Bool) => p (currentLocalParity a))
    (plusCurrentLimit_parityMarginal_eq d beta hbeta.le S hS
      hphi hpsi hnu hrho)
  simpa only [currentParityMarginalPMF_apply] using hp

theorem freeCurrentLimit_latticeMarginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply]
  rw [freeCurrentLimit_pattern_factor d beta hbeta S hS hphi hnu a,
    freeCurrentLimit_pattern_factor d beta hbeta S hS hpsi hrho a]
  congr 1
  have hp := congrArg (fun p : PMF (↑S → Bool) => p (currentLocalParity a))
    (freeCurrentLimit_parityMarginal_eq d beta hbeta.le S hS
      hphi hpsi hnu hrho)
  simpa only [currentParityMarginalPMF_apply] using hp

theorem boxCurrentEdgeIncl_mem_lattice
    (d n : ℕ) (e : (StatMech.FK.boxGraph d n).edgeFinset) :
    boxCurrentEdgeIncl d n e ∈ (hypercubicLattice d).edgeSet := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at he
      change (hypercubicLattice d).Adj x.1 y.1
      exact he

theorem boxCurrentEdgeIncl_ne_nonlattice
    (d n : ℕ) (e : Sym2 (Site d))
    (he : e ∉ (hypercubicLattice d).edgeSet) :
    e ∉ Set.range (boxCurrentEdgeIncl d n) := by
  rintro ⟨f, rfl⟩
  exact he (boxCurrentEdgeIncl_mem_lattice d n f)

theorem freeBoxCurrentMeasure_nonlattice_zero
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet) :
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendBoxCurrent d n)
    (sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
      (fun _ => 1) hbeta (fun _ => zero_le_one)).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hmeas]
  have hout := boxCurrentEdgeIncl_ne_nonlattice d n e he
  have hpre : extendBoxCurrent d n ⁻¹' {m | m e = 0} = Set.univ := by
    ext m
    simp [extendBoxCurrent_outside d n m e hout]
  rw [hpre, measure_univ]

theorem plusBoxCurrentMeasure_nonlattice_zero
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet) :
    (plusBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  change Measure.map (extendBoxCurrent d n)
    (boundaryCurrentPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1)
      hbeta (fun _ => zero_le_one) (boxCurrentInterior d n)).toMeasure
      {m | m e = 0} = 1
  rw [Measure.map_apply (measurable_extendBoxCurrent d n) hmeas]
  have hout := boxCurrentEdgeIncl_ne_nonlattice d n e he
  have hpre : extendBoxCurrent d n ⁻¹' {m | m e = 0} = Set.univ := by
    ext m
    simp [extendBoxCurrent_outside d n m e hout]
  rw [hpre, measure_univ]

theorem plusCurrentLimit_nonlattice_zero
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ}
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  let S : Finset (Sym2 (Site d)) := {e}
  let A : Set (↑S → ℕ) := {a | a ⟨e, by simp [S]⟩ = 0}
  have hset : currentCylinder S A = {m | m e = 0} := by
    ext m
    simp [currentCylinder, restrictCurrent, A, S]
  have hlim := hnu.cylinderENNReal S A
  rw [hset] at hlim
  have hone : Tendsto
      (fun k => (plusBoxCurrentMeasure d (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [plusBoxCurrentMeasure_nonlattice_zero d _ beta hbeta e he]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

theorem freeCurrentLimit_nonlattice_zero
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (he : e ∉ (hypercubicLattice d).edgeSet)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ}
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu) :
    (nu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
      {m | m e = 0} = 1 := by
  let S : Finset (Sym2 (Site d)) := {e}
  let A : Set (↑S → ℕ) := {a | a ⟨e, by simp [S]⟩ = 0}
  have hset : currentCylinder S A = {m | m e = 0} := by
    ext m
    simp [currentCylinder, restrictCurrent, A, S]
  have hlim := hnu.cylinderENNReal S A
  rw [hset] at hlim
  have hone : Tendsto
      (fun k => (freeBoxCurrentMeasure d (phi k) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0}) atTop (nhds 1) := by
    simpa only [freeBoxCurrentMeasure_nonlattice_zero d _ beta hbeta e he]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (nhds 1))
  exact tendsto_nhds_unique hlim hone

noncomputable def latticeEdgePart (d : ℕ)
    (S : Finset (Sym2 (Site d))) : Finset (Sym2 (Site d)) :=
  S.filter fun e => e ∈ (hypercubicLattice d).edgeSet

theorem latticeEdgePart_subset (d : ℕ)
    (S : Finset (Sym2 (Site d))) : latticeEdgePart d S ⊆ S :=
  Finset.filter_subset _ _

theorem latticeEdgePart_lattice (d : ℕ)
    (S : Finset (Sym2 (Site d))) :
    (↑(latticeEdgePart d S) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  exact (Finset.mem_filter.mp he).2

theorem ae_eq_zero_of_measure_eq_one
    {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (e : E)
    (hzero : (mu : Measure (InfiniteCurrentConfig E)) {m | m e = 0} = 1) :
    ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig E)), m e = 0 := by
  rw [ae_iff]
  have hmeas : MeasurableSet
      {m : InfiniteCurrentConfig E | m e = 0} :=
    (measurable_pi_apply e) (MeasurableSet.singleton 0)
  have hset : {m : InfiniteCurrentConfig E | ¬m e = 0} =
      {m : InfiniteCurrentConfig E | m e = 0}ᶜ := by
    ext m
    simp
  rw [hset, measure_compl hmeas (measure_ne_top _ _), measure_univ, hzero]
  simp

theorem ae_nonlattice_zero_on_finset
    (d : ℕ) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1) :
    ∀ᵐ m ∂(mu : Measure (InfiniteCurrentConfig (Sym2 (Site d)))),
      ∀ e ∈ S, e ∉ (hypercubicLattice d).edgeSet → m e = 0 := by
  rw [Finset.eventually_all]
  intro e heS
  by_cases he : e ∈ (hypercubicLattice d).edgeSet
  · filter_upwards with m hnot
    exact (hnot he).elim
  · filter_upwards [ae_eq_zero_of_measure_eq_one mu e (hzero e he)] with m hm
    exact fun _ => hm

theorem currentCylinder_singleton_reduce_lattice
    (d : ℕ) (mu : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))))
    (S : Finset (Sym2 (Site d)))
    (hzero : ∀ e, e ∉ (hypercubicLattice d).edgeSet →
      (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | m e = 0} = 1)
    (a : ↑S → ℕ) :
    (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder S {a}) =
      if ∀ e : ↑S,
          e.1 ∉ (hypercubicLattice d).edgeSet → a e = 0 then
        (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder (latticeEdgePart d S)
            {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
              (latticeEdgePart_subset d S) a})
      else 0 := by
  let L := latticeEdgePart d S
  let aL := Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
    (latticeEdgePart_subset d S) a
  have hae := ae_nonlattice_zero_on_finset d mu S hzero
  split_ifs with ha
  · apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ restrictCurrent L m = aL
    constructor
    · intro h
      funext e
      exact congrFun h ⟨e.1, (latticeEdgePart_subset d S) e.2⟩
    · intro h
      funext e
      by_cases he : e.1 ∈ (hypercubicLattice d).edgeSet
      · let eL : ↑L := ⟨e.1, Finset.mem_filter.mpr ⟨e.2, he⟩⟩
        have hc := congrFun h eL
        exact hc
      · rw [show restrictCurrent S m e = 0 by
          exact hm e.1 e.2 he]
        exact (ha e he).symm
  · have hempty : (mu : Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (∅ : Set (InfiniteCurrentConfig (Sym2 (Site d)))) = 0 := measure_empty
    rw [← hempty]
    apply measure_congr
    filter_upwards [hae] with m hm
    apply propext
    change (restrictCurrent S m = a) ↔ False
    constructor
    · intro h
      apply ha
      intro e he
      rw [← congrFun h e]
      exact hm e.1 e.2 he
    · exact False.elim

theorem plusCurrentLimit_marginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_lattice d nu S
      (fun e he => plusCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_lattice d rho S
      (fun e he => plusCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hrho) a]
  split_ifs
  · have hL := plusCurrentLimit_latticeMarginal_eq d beta hbeta
      (latticeEdgePart d S) (latticeEdgePart_lattice d S)
      hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(latticeEdgePart d S) → ℕ) =>
        (p : Measure (↑(latticeEdgePart d S) → ℕ))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
            (latticeEdgePart_subset d S) a}) hL
    simpa only [currentMarginal_apply] using happ
  · rfl

theorem freeCurrentLimit_marginal_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    currentMarginal nu S = currentMarginal rho S := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro a
  rw [currentMarginal_apply, currentMarginal_apply,
    currentCylinder_singleton_reduce_lattice d nu S
      (fun e he => freeCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hnu) a,
    currentCylinder_singleton_reduce_lattice d rho S
      (fun e he => freeCurrentLimit_nonlattice_zero
        d beta hbeta.le e he hrho) a]
  split_ifs
  · have hL := freeCurrentLimit_latticeMarginal_eq d beta hbeta
      (latticeEdgePart d S) (latticeEdgePart_lattice d S)
      hphi hpsi hnu hrho
    have happ := congrArg (fun p : ProbabilityMeasure
      (↑(latticeEdgePart d S) → ℕ) =>
        (p : Measure (↑(latticeEdgePart d S) → ℕ))
          {Finset.restrict₂ (π := fun _ : Sym2 (Site d) => ℕ)
            (latticeEdgePart_subset d S) a}) hL
    simpa only [currentMarginal_apply] using happ
  · rfl

theorem plusCurrentLimit_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact plusCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

theorem freeCurrentLimit_eq
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi psi : ℕ → ℕ} (hphi : StrictMono phi) (hpsi : StrictMono psi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu)
    (hrho : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ psi) rho) :
    nu = rho := by
  apply ProbabilityMeasure.ext_of_currentMarginal_eq
  intro S
  exact freeCurrentLimit_marginal_eq d beta hbeta S hphi hpsi hnu hrho

theorem plusCurrentLimit_eq_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
    nu = infinitePlusCurrentMeasure d beta hbeta.le := by
  exact plusCurrentLimit_eq d beta hbeta hphi
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le) hnu
    (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)

theorem freeCurrentLimit_eq_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    {nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))}
    {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (hnu : WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta.le) ∘ phi) nu) :
    nu = infiniteFreeCurrentMeasure d beta hbeta.le := by
  exact freeCurrentLimit_eq d beta hbeta hphi
    (infiniteCurrentBoxSubsequence_strictMono d beta hbeta.le) hnu
    (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)

theorem weakCurrent_tendsto_of_tight_of_subseq_unique
    {E : Type*} [Countable E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (nu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (htight : IsTightMeasureSet (Set.range fun n =>
      (mu n : Measure (InfiniteCurrentConfig E))))
    (hnuMem : nu ∈ closure (Set.range mu))
    (hunique : ∀ (rho : ProbabilityMeasure (InfiniteCurrentConfig E))
      (phi : ℕ → ℕ), StrictMono phi →
        WeakCurrentConverges (mu ∘ phi) rho → rho = nu) :
    WeakCurrentConverges mu nu := by
  let K : Set (ProbabilityMeasure (InfiniteCurrentConfig E)) :=
    closure (Set.range mu)
  have hK : IsCompact K := by
    apply isCompact_closure_of_isTightMeasureSet
    have heq : {m : Measure (InfiniteCurrentConfig E) |
        ∃ rho ∈ Set.range mu, (rho : Measure _) = m} =
        Set.range (fun n => (mu n : Measure (InfiniteCurrentConfig E))) := by
      ext m
      simp
    rw [heq]
    exact htight
  let muK : ℕ → K := fun n =>
    ⟨mu n, subset_closure (Set.mem_range_self n)⟩
  let nuK : K := ⟨nu, hnuMem⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsub : Tendsto muK atTop (nhds nuK) := by
    apply tendsto_nhds_of_unique_mapClusterPt
    intro rho hrho
    obtain ⟨phi, hphi, hconv⟩ := hrho.tendsto_subseq
    apply Subtype.ext
    have hval : WeakCurrentConverges (mu ∘ phi) rho.1 := by
      have hc := (continuous_subtype_val.tendsto rho).comp hconv
      simpa [muK, Function.comp_def] using hc
    exact hunique rho.1 phi hphi hval
  have hval := (continuous_subtype_val.tendsto nuK).comp hsub
  simpa [muK, nuK] using hval

theorem plusBoxCurrentMeasure_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    WeakCurrentConverges
      (fun n => plusBoxCurrentMeasure d n beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) := by
  let mu := fun n => plusBoxCurrentMeasure d n beta hbeta.le
  have hmem : infinitePlusCurrentMeasure d beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta.le)
    filter_upwards with k
    exact subset_closure ⟨infiniteCurrentBoxSubsequence d beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (infinitePlusCurrentMeasure d beta hbeta.le)
    (plusBoxCurrentMeasure_tight d beta hbeta.le) hmem
    (fun rho phi hphi hconv =>
      plusCurrentLimit_eq_infinitePlus d beta hbeta hphi hconv)

theorem freeBoxCurrentMeasure_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) :
    WeakCurrentConverges
      (fun n => freeBoxCurrentMeasure d n beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
  let mu := fun n => freeBoxCurrentMeasure d n beta hbeta.le
  have hmem : infiniteFreeCurrentMeasure d beta hbeta.le ∈
      closure (Set.range mu) := by
    apply isClosed_closure.mem_of_tendsto
      (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta.le)
    filter_upwards with k
    exact subset_closure ⟨infiniteCurrentBoxSubsequence d beta hbeta.le k, rfl⟩
  exact weakCurrent_tendsto_of_tight_of_subseq_unique mu
    (infiniteFreeCurrentMeasure d beta hbeta.le)
    (freeBoxCurrentMeasure_tight d beta hbeta.le) hmem
    (fun rho phi hphi hconv =>
      freeCurrentLimit_eq_infiniteFree d beta hbeta hphi hconv)

theorem plusBoxCurrentMeasure_cylinder_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun n => (plusBoxCurrentMeasure d n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((infinitePlusCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (plusBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal S A

theorem freeBoxCurrentMeasure_cylinder_tendsto_full
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun n => (freeBoxCurrentMeasure d n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A)) atTop
      (nhds ((infiniteFreeCurrentMeasure d beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentCylinder S A))) :=
  (freeBoxCurrentMeasure_tendsto_full d beta hbeta).cylinderENNReal S A

end StatMech.FrontierB
