/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.BackboneTwoEdgeBondToggle

open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoUnitCertificate

open BackboneConcreteSelector
open BackboneConcreteBondProgram (canonicalEdgeSegment)
open BackboneTwoEdgeBondProgram
open BackboneTwoEdgeBondToggle
open BackboneDeterminedCutSwitching
open BackboneLabeledSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open FluxEdgeCopy

noncomputable local instance twoUnitCertificateDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _




theorem twoUnit_canonicalToggle_instance
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    ∃ path : Finset (Copy d.graph (twoUnitFlux d.graph e f)), ∀ T,
      BondwisePairEvent
          ((program (V := V)).runSpec d
            [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
          (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
          d.graph (twoUnitFlux d.graph e f) T <->
        BondwisePairEvent
          (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
          ((program (V := V)).liftedResidualRunSpec d
            (canonicalEdgeSegment d.graph e)
            [canonicalEdgeSegment d.graph f])
          d.graph (twoUnitFlux d.graph e f) (T ∆ path) := by
  exact ⟨{secondCopy d.graph e f hne},
    twoUnit_pair_toggle d e f hne hfirst hactiveE hactiveF hpath⟩



theorem sources_secondCopy_eq_stepToggleSource
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f) :
    RandomCurrent.sources
        (endsM d.graph (twoUnitFlux d.graph e f))
        ({secondCopy d.graph e f hne} :
          Finset (Copy d.graph (twoUnitFlux d.graph e f))) =
      stepToggleSource (selectorSpec (V := V)).toPartialSelector d
        (canonicalEdgeSegment d.graph e)
        [canonicalEdgeSegment d.graph f] := by
  rw [FluxEdgeCopy.sources_eq, profileFlux_secondCopy,
    BackboneConcreteBondProgram.sources_unitFlux]
  simp only [stepToggleSource]
  change
    ({(canonicalEdgeSegment d.graph f).1,
        (canonicalEdgeSegment d.graph f).2.1} : Finset V) =
      ({(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1} ∆
        {(canonicalEdgeSegment d.graph f).1,
          (canonicalEdgeSegment d.graph f).2.1}) ∆
        {(canonicalEdgeSegment d.graph e).1,
          (canonicalEdgeSegment d.graph e).2.1}
  simp



theorem weight_twoUnitFlux_pos
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) :
    0 < weight d.graph beta J
      (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) := by
  unfold weight
  refine Finset.prod_pos (fun g _ => ?_)
  exact div_pos (pow_pos (mul_pos hbeta (hJ g)) _)
    (by positivity)



theorem twoUnit_left_rawPairFiberMass_pos
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    0 < rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f)
      ((selectorSpec (V := V)).toPartialSelector.sourceClass d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      ((selectorSpec (V := V)).toPartialSelector.Fiber d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      (liftedResidualVacuum d (canonicalEdgeSegment d.graph e)) := by
  let m := twoUnitFlux d.graph e f
  let word :=
    [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
  let A := (selectorSpec (V := V)).toPartialSelector.sourceClass d word
  let Q := fun T : Finset (Copy d.graph m) =>
    (selectorSpec (V := V)).toPartialSelector.Fiber d word
        (profileFlux d.graph m T) /\
      liftedResidualVacuum d (canonicalEdgeSegment d.graph e)
        (profileFlux d.graph m (univ \ T))
  have hfiber : (selectorSpec (V := V)).toPartialSelector.Fiber d word m := by
    exact selectorSpec_fiber_canonical_pair_twoUnitFlux d e f hne hfirst
      hactiveE hactiveF hpath
  have hvacuum : liftedResidualVacuum d
      (canonicalEdgeSegment d.graph e) 0 := by
    exact (residualVacuumRunSpec_event d
      (canonicalEdgeSegment d.graph e) 0).mp (vacuum_zero d e)
  have hsource : RandomCurrent.sources (endsM d.graph m)
      (univ : Finset (Copy d.graph m)) = A := by
    calc
      RandomCurrent.sources (endsM d.graph m)
          (univ : Finset (Copy d.graph m)) =
          sources d.graph
            (ofEdgeFun d.graph (profileFlux d.graph m univ)) :=
        FluxEdgeCopy.sources_eq d.graph m univ
      _ = sources d.graph (ofEdgeFun d.graph m) := by
        rw [profileFlux_univ]
      _ = A :=
        (selectorSpec (V := V)).toPartialSelector
          |>.sources_eq_sourceClass_of_select d m word hfiber
  have hQ : Q (univ : Finset (Copy d.graph m)) := by
    constructor
    · rw [profileFlux_univ]
      exact hfiber
    · simpa [Q] using hvacuum
  let witness : Fiber d.graph m A Q := ⟨univ, hsource, hQ⟩
  change 0 < rawSourcePairFiberMass d.graph beta J m A
    ((selectorSpec (V := V)).toPartialSelector.Fiber d word)
    (liftedResidualVacuum d (canonicalEdgeSegment d.graph e))
  rw [rawSourcePairFiberMass_eq_labeled]
  unfold labeledSourcePairFiberMass
  exact Finset.sum_pos
    (fun _ _ => weight_twoUnitFlux_pos beta J hbeta hJ d e f)
    ⟨witness, Finset.mem_univ witness⟩



theorem twoUnit_coordinatePairContributes
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector
      beta J d (canonicalEdgeSegment d.graph e)
      [canonicalEdgeSegment d.graph f] hactiveE
      (twoUnitFlux d.graph e f) := by
  exact Or.inl (ne_of_gt (twoUnit_left_rawPairFiberMass_pos beta J hbeta hJ
    d e f hne hfirst hactiveE hactiveF hpath))





theorem twoUnit_rawPairFiberMass_eq
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f)
        ((selectorSpec (V := V)).toPartialSelector.sourceClass d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        ((selectorSpec (V := V)).toPartialSelector.Fiber d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (liftedResidualVacuum d (canonicalEdgeSegment d.graph e)) =
      rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f)
        (((selectorSpec (V := V)).toPartialSelector.sourceClass d
            [canonicalEdgeSegment d.graph e,
              canonicalEdgeSegment d.graph f]) ∆
          stepToggleSource (selectorSpec (V := V)).toPartialSelector d
            (canonicalEdgeSegment d.graph e)
            [canonicalEdgeSegment d.graph f])
        (shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hactiveE)
        (liftedResidualFiber (selectorSpec (V := V)).toPartialSelector d
          (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f]) := by
  apply rawSourcePairFiberMass_eq_of_labeledToggle
    d.graph beta J (twoUnitFlux d.graph e f)
    ((selectorSpec (V := V)).toPartialSelector.sourceClass d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (stepToggleSource (selectorSpec (V := V)).toPartialSelector d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    ({secondCopy d.graph e f hne} :
      Finset (Copy d.graph (twoUnitFlux d.graph e f)))
    (sources_secondCopy_eq_stepToggleSource d e f hne)
  intro T
  calc
    ((selectorSpec (V := V)).toPartialSelector.Fiber d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
          (profileFlux d.graph (twoUnitFlux d.graph e f) T) /\
        liftedResidualVacuum d (canonicalEdgeSegment d.graph e)
          (profileFlux d.graph (twoUnitFlux d.graph e f) (univ \ T))) <->
        BondwisePairEvent
          ((program (V := V)).runSpec d
            [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
          (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
          d.graph (twoUnitFlux d.graph e f) T := by
      exact and_congr
        ((selectorSpec (V := V)).fiber_iff_runSpec_event d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
          (profileFlux d.graph (twoUnitFlux d.graph e f) T))
        (residualVacuumRunSpec_event d (canonicalEdgeSegment d.graph e)
          (profileFlux d.graph (twoUnitFlux d.graph e f)
            (univ \ T))).symm
    _ <-> BondwisePairEvent
          (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
          ((program (V := V)).liftedResidualRunSpec d
            (canonicalEdgeSegment d.graph e)
            [canonicalEdgeSegment d.graph f])
          d.graph (twoUnitFlux d.graph e f)
          (T ∆ {secondCopy d.graph e f hne}) :=
      twoUnit_pair_toggle d e f hne hfirst hactiveE hactiveF hpath T
    _ <-> (shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hactiveE
          (profileFlux d.graph (twoUnitFlux d.graph e f)
            (T ∆ {secondCopy d.graph e f hne})) /\
        liftedResidualFiber (selectorSpec (V := V)).toPartialSelector d
          (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]
          (profileFlux d.graph (twoUnitFlux d.graph e f)
            (univ \ (T ∆ {secondCopy d.graph e f hne})))) := by
      exact and_congr
        (activeSegmentRunSpec_event d (canonicalEdgeSegment d.graph e)
          hactiveE _)
        (((program (V := V)).liftedResidualRunSpec_event d
          (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f] _).trans
            ((selectorSpec (V := V)).liftedResidualFiber_iff_liftedRunEvent d
              (canonicalEdgeSegment d.graph e)
              [canonicalEdgeSegment d.graph f] _).symm)





theorem canonicalBondwiseToggleExists_iff_off_twoUnit
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d
        (canonicalEdgeSegment d.graph e)
        [canonicalEdgeSegment d.graph f] hactiveE <->
      ∀ m, m ≠ twoUnitFlux d.graph e f ->
        CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector
          beta J d (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f] hactiveE m ->
        ∃ path : Finset (Copy d.graph m), ∀ T,
          BondwisePairEvent
              ((program (V := V)).runSpec d
                [canonicalEdgeSegment d.graph e,
                  canonicalEdgeSegment d.graph f])
              (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
              d.graph m T <->
            BondwisePairEvent
              (activeSegmentRunSpec d
                (canonicalEdgeSegment d.graph e) hactiveE)
              ((program (V := V)).liftedResidualRunSpec d
                (canonicalEdgeSegment d.graph e)
                [canonicalEdgeSegment d.graph f])
              d.graph m (T ∆ path) := by
  constructor
  · intro htoggle m _ hm
    exact htoggle m hm
  · intro hoff m hm
    by_cases hmtwo : m = twoUnitFlux d.graph e f
    · subst m
      exact twoUnit_canonicalToggle_instance d e f hne hfirst hactiveE
        hactiveF hpath
    · exact hoff m hmtwo hm




theorem nonempty_canonicalCertificate_iff_off_twoUnit
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hne : e ≠ f)
    (hfirst : scan.firstAdmissible
      (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit
        (twoUnitFlux d.graph e f) b)
      ⟨d, []⟩ = some e.1)
    (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
    (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
    (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e)
      (canonicalEdgeSegment d.graph f)) :
    Nonempty (AsymmetricBondwiseCoordinateCertificate
      ((program (V := V)).runSpec d
        [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
      (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
      (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE)
      ((program (V := V)).liftedResidualRunSpec d
        (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
      (selectorSpec (V := V)).toPartialSelector beta J d
      (canonicalEdgeSegment d.graph e)
      [canonicalEdgeSegment d.graph f] hactiveE) <->
      ∀ m, m ≠ twoUnitFlux d.graph e f ->
        CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector
          beta J d (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f] hactiveE m ->
        ∃ path : Finset (Copy d.graph m), ∀ T,
          BondwisePairEvent
              ((program (V := V)).runSpec d
                [canonicalEdgeSegment d.graph e,
                  canonicalEdgeSegment d.graph f])
              (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
              d.graph m T <->
            BondwisePairEvent
              (activeSegmentRunSpec d
                (canonicalEdgeSegment d.graph e) hactiveE)
              ((program (V := V)).liftedResidualRunSpec d
                (canonicalEdgeSegment d.graph e)
                [canonicalEdgeSegment d.graph f])
              d.graph m (T ∆ path) := by
  rw [selectorSpec_nonempty_canonicalCertificate_iff_toggleExists]
  exact canonicalBondwiseToggleExists_iff_off_twoUnit beta J d e f hne
    hfirst hactiveE hactiveF hpath

end BackboneTwoUnitCertificate

end

end StatMech.Sharpness
