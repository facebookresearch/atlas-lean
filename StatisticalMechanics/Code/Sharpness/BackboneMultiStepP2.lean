/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Sharpness.BackboneMultiStepBondProgram

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneMultiStepBondProgram

open BackboneConcreteSelector
open BackboneConcreteBondProgram

noncomputable local instance multiStepP2DecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _




theorem designatedHead_unrestricted_cut_factor
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset) :
    shb_fullWeightMass d.graph beta J =
      shb_cutLeftMass d.graph beta J (fun g => g.1 = e.1) *
        shb_cutRightMass d.graph beta J (fun g => g.1 = e.1) :=
  shb_tsum_weight_cut_factor d.graph beta J (fun g => g.1 = e.1)



theorem selectorSpec_not_fiber_singleton
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    ¬((selectorSpec (V := V)).toPartialSelector).Fiber d [s] m := by
  intro hfiber
  have hcomplete :=
    ((selectorSpec (V := V)).fiber_iff_completeEvent d [s] m).mp hfiber
  rcases program_complete_word_eq_nil_or_pair d m [s] hcomplete with
    hnil | ⟨u, v, hpair⟩
  · simp at hnil
  · simp at hpair


theorem selectorSpec_actualMass_singleton_eq_zero
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d [s] = 0 := by
  unfold shb_PartialCurrentDynamicSelector.actualMass
  simp [selectorSpec_not_fiber_singleton]




theorem selectorSpec_pair_clearedP2_of_toggleExists
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (htoggle : (selectorSpec (V := V)).CanonicalBondwiseToggleExists
      beta J d (canonicalEdgeSegment d.graph e)
      [canonicalEdgeSegment d.graph f] heactive) :
    ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] *
        currentSum
          (shb_BackboneExplorationDomain.advance d
            (canonicalEdgeSegment d.graph e)).graph beta J ∅ =
      shb_segmentNum beta J d (canonicalEdgeSegment d.graph e) *
        ((selectorSpec (V := V)).toPartialSelector).actualMass beta J
          (shb_BackboneExplorationDomain.advance d
            (canonicalEdgeSegment d.graph e))
          [canonicalEdgeSegment d.graph f] := by
  let C := (selectorSpec (V := V)).toCanonicalAsymmetricCertificate_of_toggleExists
      beta J d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]
      heactive htoggle
  exact C.actualMass_active
    ((program (V := V)).runSpec d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
    (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) heactive)
    ((program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    (selectorSpec (V := V)).toPartialSelector beta J d
    (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]
    heactive




theorem selectorSpec_pair_clearedMass_eq_zero_of_toggleExists
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (htoggle : (selectorSpec (V := V)).CanonicalBondwiseToggleExists
      beta J d (canonicalEdgeSegment d.graph e)
      [canonicalEdgeSegment d.graph f] heactive) :
    ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] *
        currentSum
          (shb_BackboneExplorationDomain.advance d
            (canonicalEdgeSegment d.graph e)).graph beta J ∅ = 0 := by
  have hp2 := selectorSpec_pair_clearedP2_of_toggleExists
    beta J d e f heactive htoggle
  simpa [selectorSpec_actualMass_singleton_eq_zero] using hp2





theorem selectorSpec_not_admissible_unitFlux_of_active_eq_empty
    (d : shb_ExplorationDomain V) (e : d.graph.edgeFinset)
    (hactive : d.active = ∅) :
    ¬((selectorSpec (V := V)).toPartialSelector.Admissible d
      (unitFlux d.graph e)) := by
  rintro ⟨word, hfiber⟩
  have hcomplete :=
    ((selectorSpec (V := V)).fiber_iff_completeEvent d word
      (unitFlux d.graph e)).mp hfiber
  rcases program_complete_word_eq_nil_or_pair d (unitFlux d.graph e)
      word hcomplete with rfl | ⟨s, t, rfl⟩
  · have hzero :=
      (program_complete_nil_iff d (unitFlux d.graph e)).mp hcomplete
    rw [sources_unitFlux] at hzero
    have hmem : (canonicalEdgeSegment d.graph e).1 ∈ (∅ : Finset V) := by
      rw [← hzero]
      simp
    simp at hmem
  · obtain ⟨_, _, _, _, _, _, _, heactive, _, _, _⟩ :=
      program_complete_pair_data d (unitFlux d.graph e) s t hcomplete
    rw [hactive] at heactive
    simp at heactive



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



theorem selectorSpec_actualMass_designated_pair_pos
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    0 < ((selectorSpec (V := V)).toPartialSelector).actualMass beta J d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] := by
  let word :=
    [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]
  let m₀ := twoUnitFlux d.graph e f
  let F := fun m : d.graph.edgeFinset -> Nat =>
    if ((selectorSpec (V := V)).toPartialSelector).Fiber d word m then
      weight d.graph beta J (ofEdgeFun d.graph m)
    else 0
  change 0 < ∑' m, F m
  have hfiber : ((selectorSpec (V := V)).toPartialSelector).Fiber d word m₀ := by
    exact selectorSpec_fiber_designated_twoUnitFlux d e f hpair
      heactive hfactive
  have hsummable : Summable F := by
    dsimp only [F]
    exact shb_summable_indicator d.graph beta J hbeta.le
      (fun g => (hJ g).le) _
  have hle : F m₀ ≤ ∑' m, F m := by
    exact hsummable.le_tsum m₀ (fun m _ => by
      dsimp only [F]
      by_cases hm : ((selectorSpec (V := V)).toPartialSelector).Fiber
          d word m
      · rw [if_pos hm]
        exact shb_weight_nonneg d.graph beta J hbeta.le
          (fun g => (hJ g).le) _
      · simp [hm])
  have hterm : F m₀ =
      weight d.graph beta J (ofEdgeFun d.graph m₀) := by
    simp [F, hfiber]
  rw [hterm] at hle
  exact (weight_twoUnitFlux_pos beta J hbeta hJ d e f).trans_le hle






theorem selectorSpec_not_pair_toggleExists_of_pos
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g)
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset)
    (hpair : IsDesignatedPair d e f)
    (heactive : canonicalEdgeSegment d.graph e ∈ d.active)
    (hfactive : canonicalEdgeSegment d.graph f ∈ d.active) :
    ¬ (selectorSpec (V := V)).CanonicalBondwiseToggleExists
      beta J d (canonicalEdgeSegment d.graph e)
        [canonicalEdgeSegment d.graph f] heactive := by
  intro htoggle
  have hzero := selectorSpec_pair_clearedMass_eq_zero_of_toggleExists
    beta J d e f heactive htoggle
  have hmass := selectorSpec_actualMass_designated_pair_pos
    beta J hbeta hJ d e f hpair heactive hfactive
  have hvac := StatMech.Ising.acr_currentSum_empty_pos
    (shb_BackboneExplorationDomain.advance d
      (canonicalEdgeSegment d.graph e)).graph beta J
  exact (ne_of_gt (mul_pos hmass hvac)) hzero

end BackboneMultiStepBondProgram

end

end StatMech.Sharpness
