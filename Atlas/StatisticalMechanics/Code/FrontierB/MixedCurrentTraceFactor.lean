/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.MixedCurrentTraceMixing
import Code.FrontierB.CurrentTraceZeroBeta

open MeasureTheory Set

namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]

def pairOrSupport [DecidableEq E] (S : Finset E) : Finset (E ⊕ E) :=
  S.image Sum.inl ∪ S.image Sum.inr

def pairOrLocalPattern [DecidableEq E] (S : Finset E)
    (a : ↑(pairOrSupport S) -> Bool) : ↑S -> Bool := fun e =>
  a ⟨Sum.inl e.1, Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)⟩ ||
  a ⟨Sum.inr e.1, Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)⟩

def pairOrPullbackPatternSet [DecidableEq E] (S : Finset E)
    (A : Set (↑S -> Bool)) : Set (↑(pairOrSupport S) -> Bool) :=
  {a | pairOrLocalPattern S a ∈ A}

omit [Countable E] in
theorem pairOrConfig_preimage_cylinder [DecidableEq E]
    (S : Finset E) (A : Set (↑S -> Bool)) :
    pairOrConfig ⁻¹' MeasureTheory.cylinder S A =
      MeasureTheory.cylinder (pairOrSupport S) (pairOrPullbackPatternSet S A) := by
  ext omega
  change (fun e : ↑S => omega (Sum.inl e.1) || omega (Sum.inr e.1)) ∈ A ↔
    pairOrLocalPattern S (Finset.restrict (pairOrSupport S) omega) ∈ A
  have hpattern : (fun e : ↑S =>
      omega (Sum.inl e.1) || omega (Sum.inr e.1)) =
      pairOrLocalPattern S (Finset.restrict (pairOrSupport S) omega) := by
    funext e
    rfl
  rw [hpattern]



theorem pairOrConfig_preimage_mem_measurableCylinders
    {C : Set (ConfigSpace E)}
    (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
    pairOrConfig ⁻¹' C ∈ measurableCylinders (fun _ : E ⊕ E => Bool) := by
  classical
  rw [mem_measurableCylinders] at hC ⊢
  obtain ⟨S, A, hA, rfl⟩ := hC
  exact ⟨pairOrSupport S, pairOrPullbackPatternSet S A,
    MeasurableSet.of_discrete, pairOrConfig_preimage_cylinder S A⟩



noncomputable def independentMixedOrConfigLaw
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace E) :=
  (independentMixedPairConfigLaw rho nu).map
    measurable_pairOrConfig.aemeasurable

theorem mixedPairOrConfig_measurePreserving
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving pairOrConfig
      (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E)))
      (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
  change MeasurePreserving pairOrConfig _
    (Measure.map pairOrConfig
      (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))))
  exact measurable_pairOrConfig.measurePreserving _

theorem independentMixedOrConfigLaw_real
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A) :
    (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)).real A =
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))).real (pairOrConfig ⁻¹' A) := by
  have hleft : (((independentMixedOrConfigLaw rho nu) A : NNReal) : Real) =
      (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)).real A := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  have hright : (((independentMixedPairConfigLaw rho nu)
      (pairOrConfig ⁻¹' A) : NNReal) : Real) =
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E))).real (pairOrConfig ⁻¹' A) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft, ← hright]
  exact congrArg (fun z : NNReal => (z : Real))
    (ProbabilityMeasure.map_apply (independentMixedPairConfigLaw rho nu)
      measurable_pairOrConfig.aemeasurable hA)

omit [Countable E] in
theorem pairOrConfig_preimage_inter_shift (g : H)
    (A B : Set (ConfigSpace E)) :
    pairOrConfig ⁻¹' (A ∩ (shift g) ⁻¹' B) =
      (pairOrConfig ⁻¹' A) ∩
        (shift g) ⁻¹' (pairOrConfig ⁻¹' B) := by
  ext omega
  rfl


theorem independentMixedOrConfigLaw_genMixing
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hmix : fmu_GenMixing (G := H)
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E)))) :
    fmu_GenMixing (G := H)
      (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
  classical
  intro family hfamily epsilon hepsilon
  let pulled : Finset (Set (ConfigSpace (E ⊕ E))) :=
    family.image (fun A => pairOrConfig ⁻¹' A)
  have hpulled : ∀ A ∈ pulled,
      A ∈ measurableCylinders (fun _ : E ⊕ E => Bool) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact pairOrConfig_preimage_mem_measurableCylinders (hfamily C hC)
  obtain ⟨g, hg⟩ := hmix pulled hpulled epsilon hepsilon
  refine ⟨g, ?_⟩
  intro A hA B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  have hABmeas : MeasurableSet (A ∩ (shift g) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage (measurable_shift g))
  rw [independentMixedOrConfigLaw_real rho nu hABmeas,
    independentMixedOrConfigLaw_real rho nu hAmeas,
    independentMixedOrConfigLaw_real rho nu hBmeas,
    pairOrConfig_preimage_inter_shift]
  exact hg (pairOrConfig ⁻¹' A)
    (Finset.mem_image.mpr ⟨A, hA, rfl⟩)
    (pairOrConfig ⁻¹' B)
    (Finset.mem_image.mpr ⟨B, hB, rfl⟩)

theorem independentMixedOrConfigLaw_isTranslationInvariant
    (rho nu : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H)
      (independentMixedPairConfigLaw rho nu :
        Measure (ConfigSpace (E ⊕ E)))) :
    IsTranslationInvariant (G := H)
      (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
  intro g
  exact (mixedPairOrConfig_measurePreserving rho nu).of_semiconj
    (hti g) (pairOrConfig_shift g) (measurable_shift g)



theorem independentMixedOr_currentTraceLaw_eq_superposed
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    (independentMixedOrConfigLaw (currentTraceLaw mu) (currentTraceLaw nu) :
        Measure (ConfigSpace E)) =
      (independentSuperposedTraceLaw mu nu : Measure (ConfigSpace E)) := by
  change Measure.map pairOrConfig
      (Measure.map (Function.uncurry pairConfig)
        ((Measure.map currentTrace (mu : Measure _)).prod
          (Measure.map currentTrace (nu : Measure _)))) =
    Measure.map superposedCurrentTrace
      ((mu : Measure (InfiniteCurrentConfig E)).prod
        (nu : Measure (InfiniteCurrentConfig E)))
  rw [Measure.map_prod_map (mu : Measure (InfiniteCurrentConfig E))
    (nu : Measure (InfiniteCurrentConfig E))
    continuous_currentTrace.measurable continuous_currentTrace.measurable]
  rw [Measure.map_map measurable_pairConfig
      (continuous_currentTrace.measurable.prodMap
        continuous_currentTrace.measurable),
    Measure.map_map measurable_pairOrConfig
      (measurable_pairConfig.comp
        (continuous_currentTrace.measurable.prodMap
          continuous_currentTrace.measurable))]
  congr 1
  funext p e
  change (decide (0 < p.1 e) || decide (0 < p.2 e)) =
    decide (0 < p.1 e + p.2 e)
  simp



theorem freePlusSuperposedTraceLaw_genMixing
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_GenMixing (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))) := by
  rw [← independentMixedOr_currentTraceLaw_eq_superposed]
  exact independentMixedOrConfigLaw_genMixing _ _
    (freePlusCurrentTracePairLaw_genMixing hd hbeta)

theorem freePlusSuperposedTraceLaw_isTranslationInvariant
    {d : Nat} {beta : Real} (hbeta : 0 < beta) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))) := by
  rw [← independentMixedOr_currentTraceLaw_eq_superposed]
  apply independentMixedOrConfigLaw_isTranslationInvariant
  exact independentMixedPairConfigLaw_isTranslationInvariant _ _
    ((infiniteFreeCurrentMeasure_isTranslationInvariant d beta hbeta).trace _)
    ((infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta).trace _)

theorem freePlusSuperposedTraceLaw_isErgodic
    {d : Nat} (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    IsErgodic (G := Multiplicative (Site d))
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Site d)))) :=
  fmu_isErgodic_of_pairMixing
    (freePlusSuperposedTraceLaw_isTranslationInvariant hbeta)
    (fmu_pairMixing_of_genMixing
      (freePlusSuperposedTraceLaw_genMixing hd hbeta))



theorem freePlusSuperposedTraceLaw_uniqueness
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta) (hd : 1 ≤ d) :
    let mu := (independentSuperposedTraceLaw
      (infiniteFreeCurrentMeasure d beta hbeta)
      (infinitePlusCurrentMeasure d beta hbeta) :
        Measure (ConfigSpace (Sym2 (Site d))))
    (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨
        mu {omega | numInfiniteClusters d omega = 1} = 1) ∧
      mu (atLeastTwoInfinite d) = 0 ∧
      mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
  rcases hbeta.eq_or_lt with hzero | hpos
  · subst beta
    simpa only using freePlusSuperposedTraceLaw_zero_beta_uniqueness d
  · exact freePlusSuperposedTraceLaw_coarse_uniqueness d beta hpos hd
      (freePlusSuperposedTraceLaw_isErgodic hd hpos)

end StatMech.FrontierB
