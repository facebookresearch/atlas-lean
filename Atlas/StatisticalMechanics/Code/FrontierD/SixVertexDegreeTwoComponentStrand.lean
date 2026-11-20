/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit
import Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
import Mathlib.Data.Finset.SymmDiff









open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.FrontierD

noncomputable section

local instance degreeTwoComponentStrandDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


theorem SixVertexLocallyDegreeTwo.pairSwitch
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexLocallyDegreeTwo
      (sixVertexTorusSwitchFirst mask omega eta)
      (sixVertexTorusSwitchSecond mask omega eta) := by
  intro vertex
  have hsides : sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) vertex)
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) vertex) =
      sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega vertex)
        (sixVertexLocalIncomingPattern eta vertex) := by
    ext side
    simp only [mem_sixVertexLocalDisagreementSides]
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
  rw [hsides]
  exact hdegree vertex


theorem sixVertexTorusMaskSelects_maskXor
    {T : EvenTorus} (first second : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexTorusMaskXor first second) edge =
      (sixVertexTorusMaskSelects first edge !=
        sixVertexTorusMaskSelects second edge) := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction <;>
    simp [sixVertexTorusMaskSelects, sixVertexTorusMaskXor]


theorem sixVertexDisagreementComponentSetMask_symmDiff_selects
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (first second : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta
          (first ∆ second)) edge =
      (sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta first) edge !=
        sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta second) edge) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [sixVertexDisagreementComponentSetMask_selects_iff,
    bne_iff_ne]
  constructor
  · rintro ⟨component, hcomponent, hedge⟩
    rw [Finset.mem_symmDiff] at hcomponent
    rcases hcomponent with ⟨hfirst, hsecond⟩ | ⟨hsecond, hfirst⟩
    · have hfirstSelect :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta first edge).2 ⟨component, hfirst, hedge⟩
      have hsecondSelect : sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta second)
          edge = false := by
        cases hs : sixVertexTorusMaskSelects
            (sixVertexDisagreementComponentSetMask omega eta second) edge
        · rfl
        · exfalso
          obtain ⟨other, hother, hotherEdge⟩ :=
            (sixVertexDisagreementComponentSetMask_selects_iff
              omega eta second edge).1 hs
          apply hsecond
          have : other = component := by
            apply Subtype.ext
            exact hotherEdge.symm.trans hedge
          simpa [this] using hother
      simp [hfirstSelect, hsecondSelect]
    · have hsecondSelect :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta second edge).2 ⟨component, hsecond, hedge⟩
      have hfirstSelect : sixVertexTorusMaskSelects
          (sixVertexDisagreementComponentSetMask omega eta first)
          edge = false := by
        cases hs : sixVertexTorusMaskSelects
            (sixVertexDisagreementComponentSetMask omega eta first) edge
        · rfl
        · exfalso
          obtain ⟨other, hother, hotherEdge⟩ :=
            (sixVertexDisagreementComponentSetMask_selects_iff
              omega eta first edge).1 hs
          apply hfirst
          have : other = component := by
            apply Subtype.ext
            exact hotherEdge.symm.trans hedge
          simpa [this] using hother
      simp [hfirstSelect, hsecondSelect]
  · intro hne
    cases hfirstSelect : sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta first) edge <;>
      cases hsecondSelect : sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta second) edge
    · exact False.elim (hne (by rw [hfirstSelect, hsecondSelect]))
    · obtain ⟨component, hcomponent, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta second edge).1 hsecondSelect
      refine ⟨component, (Finset.mem_symmDiff).2 (Or.inr
        ⟨hcomponent, ?_⟩), hedge⟩
      intro hmem
      have hfalse := (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta first edge).2 ⟨component, hmem, hedge⟩
      rw [hfirstSelect] at hfalse
      exact Bool.noConfusion hfalse
    · obtain ⟨component, hcomponent, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta first edge).1 hfirstSelect
      refine ⟨component, (Finset.mem_symmDiff).2 (Or.inl
        ⟨hcomponent, ?_⟩), hedge⟩
      intro hmem
      have hfalse := (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta second edge).2 ⟨component, hmem, hedge⟩
      rw [hsecondSelect] at hfalse
      exact Bool.noConfusion hfalse
    · exact False.elim (hne (by rw [hfirstSelect, hsecondSelect]))



theorem sixVertexDisagreementComponentSetMask_symmDiff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (first second : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexDisagreementComponentSetMask omega eta (first ∆ second) =
      sixVertexTorusMaskXor
        (sixVertexDisagreementComponentSetMask omega eta first)
        (sixVertexDisagreementComponentSetMask omega eta second) := by
  apply SixVertexArrows.ext <;> funext base
  · simpa [sixVertexTorusMaskSelects, sixVertexTorusMaskXor] using
      sixVertexDisagreementComponentSetMask_symmDiff_selects
        omega eta first second (0, base)
  · simpa [sixVertexTorusMaskSelects, sixVertexTorusMaskXor] using
      sixVertexDisagreementComponentSetMask_symmDiff_selects
        omega eta first second (1, base)


theorem sixVertexTorusSwitchFirst_pairSwitch
    {T : EvenTorus} (first second omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchFirst second
        (sixVertexTorusSwitchFirst first omega eta)
        (sixVertexTorusSwitchSecond first omega eta) =
      sixVertexTorusSwitchFirst (sixVertexTorusMaskXor first second)
        omega eta := by
  apply SixVertexArrows.ext <;> funext base <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      sixVertexTorusMaskXor] <;>
    split <;> split <;> simp_all

theorem sixVertexTorusSwitchSecond_pairSwitch
    {T : EvenTorus} (first second omega eta : SixVertexArrows T) :
    sixVertexTorusSwitchSecond second
        (sixVertexTorusSwitchFirst first omega eta)
        (sixVertexTorusSwitchSecond first omega eta) =
      sixVertexTorusSwitchSecond (sixVertexTorusMaskXor first second)
        omega eta := by
  apply SixVertexArrows.ext <;> funext base <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      sixVertexTorusMaskXor] <;>
    split <;> split <;> simp_all



theorem SixVertexFullDisagreementMask.selects_of_reachable
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    {seed edge : SixVertexTorusEdge T}
    (hseed : sixVertexTorusMaskSelects mask seed = true)
    (hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
      seed edge) :
    sixVertexTorusMaskSelects mask edge = true := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hseed
  | tail first hadj ih =>
      obtain ⟨hne, _, hedge, vertex, firstSide, edgeSide,
        hfirst, hedgeEq⟩ := hadj
      rw [← hedgeEq, ← sixVertexTorusLocalSwitchMask_apply]
      apply hmask.2 vertex firstSide edgeSide
      · rw [sixVertexTorusLocalSwitchMask_apply, hfirst]
        exact ih
      · rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
          hedgeEq]
        exact hedge


theorem sixVertexTorusIncidentEdge_injective
    (T : EvenTorus) (vertex : T.Vertex) :
    Function.Injective (sixVertexTorusIncidentEdge T vertex) := by
  intro first second heq
  fin_cases first <;> fin_cases second <;>
    simp_all [sixVertexTorusIncidentEdge, Prod.ext_iff,
      cyclicPred_ne_self T.one_lt_width vertex.1,
      cyclicPred_ne_self T.one_lt_height vertex.2]
  all_goals first
    | exact (cyclicPred_ne_self T.one_lt_width vertex.1) heq.symm
    | exact (cyclicPred_ne_self T.one_lt_height vertex.2) heq.symm


abbrev sixVertexDegreeTwoOrientedComponentEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexTorusEdge T :=
  sixVertexTorusDartEdge T
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1



theorem sixVertexDegreeTwoOrientedComponentEdge_successor_adj
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexTorusDisagreementGraph omega eta).Adj
      (sixVertexDegreeTwoOrientedComponentEdge hdegree dart)
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexOrientedDegreeTwoStrandSuccessor
          homega heta hdegree dart)) := by
  let outgoing := sixVertexDegreeTwoLocalMate hdegree dart.1
  let successor := sixVertexDisagreementBondMate outgoing
  have hsuccessor :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree dart).1 = successor := rfl
  have hfirst : sixVertexDegreeTwoOrientedComponentEdge hdegree dart =
      sixVertexTorusDartEdge T outgoing.1 := rfl
  have hsecond : sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexOrientedDegreeTwoStrandSuccessor
          homega heta hdegree dart) =
      sixVertexTorusDartEdge T
        (sixVertexDegreeTwoLocalMate hdegree successor).1 := by
    rfl
  have hfirstIncident : sixVertexTorusDartEdge T outgoing.1 =
      sixVertexTorusIncidentEdge T successor.1.1 successor.1.2 := by
    change sixVertexTorusDartEdge T outgoing.1 =
      sixVertexTorusDartEdge T successor.1
    exact (sixVertexTorusDartEdge_bondMate T outgoing.1).symm
  rw [hfirst, hsecond]
  refine ⟨?_, outgoing.2,
    (sixVertexDegreeTwoLocalMate hdegree successor).2,
    successor.1.1, successor.1.2,
    (sixVertexDegreeTwoLocalMate hdegree successor).1.2, ?_, ?_⟩
  · intro hedge
    have hsides := (sixVertexTorusIncidentEdge_injective T successor.1.1)
      (hfirstIncident.symm.trans hedge)
    exact (sixVertexDegreeTwoLocalMate_side_ne hdegree successor)
      hsides.symm
  · exact hfirstIncident.symm
  · rfl



theorem sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second) :
    (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree first) =
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree second) := by
  let successor := sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree
  obtain ⟨power, hpower⟩ := hsame.exists_nat_pow_eq
  have hpow : forall n : Nat,
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree first) =
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree
            ((successor ^ n) first)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact ih.trans (ConnectedComponent.sound
          (sixVertexDegreeTwoOrientedComponentEdge_successor_adj
            homega heta hdegree ((successor ^ n) first)).reachable)
  simpa [successor, hpower] using hpow power



theorem sixVertexDegreeTwoStrand_mask_component
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (edge : SixVertexTorusEdge T)
    (hselected : sixVertexTorusMaskSelects
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask edge = true) :
    (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction
  · obtain ⟨index, hindex⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_horizontal base).1 (by
          simpa [sixVertexTorusMaskSelects] using hselected)
    have hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed index) = (0, base) := by
      exact sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
        (by simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
            sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
            sixVertexDegreeTwoOrientedStrandEdge,
            SixVertexDirectedTorusEdge.physical] using hindex)
    change (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (0, base) = _
    rw [← hedge]
    exact (sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
      homega heta hdegree seed _
      (sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
        homega heta hdegree seed index)).symm
  · obtain ⟨index, hindex⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_vertical base).1 (by
          simpa [sixVertexTorusMaskSelects] using hselected)
    have hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed index) = (1, base) := by
      exact sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
        (by simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
            sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
            sixVertexDegreeTwoOrientedStrandEdge,
            SixVertexDirectedTorusEdge.physical] using hindex)
    change (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (1, base) = _
    rw [← hedge]
    exact (sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle
      homega heta hdegree seed _
      (sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
        homega heta hdegree seed index)).symm


theorem sixVertexDegreeTwoStrand_mask_seedEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexTorusMaskSelects
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask
      (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = true := by
  let zero : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
    ⟨0, orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)⟩
  rcases hedge : sixVertexDegreeTwoOrientedComponentEdge hdegree seed with
    ⟨direction, base⟩
  fin_cases direction
  · apply ((sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).mask_horizontal base).2
    refine ⟨zero, ?_⟩
    change (sixVertexDirectedTorusEdgeOfArrow omega
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed zero))).physical = (false, base)
    rw [show sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed zero = seed by rfl, hedge]
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical]
  · apply ((sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).mask_vertical base).2
    refine ⟨zero, ?_⟩
    change (sixVertexDirectedTorusEdgeOfArrow omega
      (sixVertexDegreeTwoOrientedComponentEdge hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed zero))).physical = (true, base)
    rw [show sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed zero = seed by rfl, hedge]
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical]



theorem sixVertexDegreeTwoStrand_mask_full
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask := by
  have hbalanced : SixVertexBalancedFlipMask omega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask :=
    sixVertexBalancedFlipMask_of_ice_flip homega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        homega heta hdegree seed)
  exact hbalanced.fullDisagreementMask_of_degreeTwo hdegree
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      homega heta hdegree seed)



theorem sixVertexDegreeTwoStrand_mask_eq_component
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component : SixVertexDisagreementComponent omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (hseed : (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
        (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = component.1) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask =
      sixVertexDisagreementComponentSetMask omega eta {component} := by
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).mask
  let componentMask :=
    sixVertexDisagreementComponentSetMask omega eta {component}
  have hstrandFull := sixVertexDegreeTwoStrand_mask_full
    homega heta hdegree seed
  have hcomponentFull := sixVertexDisagreementComponentSetMask_full
    omega eta {component}
  have hstrandSeed := sixVertexDegreeTwoStrand_mask_seedEdge
    homega heta hdegree seed
  apply SixVertexArrows.ext <;> funext base
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta {component} (0, base)).2
      refine ⟨component, by simp, ?_⟩
      exact (sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (0, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)).trans
        hseed
    · intro hcomponent
      have hcomponentEq :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta {component} (0, base)).1 (by
            simpa [componentMask, sixVertexTorusMaskSelects] using hcomponent)
      obtain ⟨other, hother, hedge⟩ := hcomponentEq
      have : other = component := by simpa using hother
      subst other
      have hselected := hstrandFull.selects_of_reachable hstrandSeed
        (ConnectedComponent.exact (hseed.trans hedge.symm))
      simpa [sixVertexTorusMaskSelects] using hselected
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta {component} (1, base)).2
      refine ⟨component, by simp, ?_⟩
      exact (sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (1, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)).trans
        hseed
    · intro hcomponent
      have hcomponentEq :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta {component} (1, base)).1 (by
            simpa [componentMask, sixVertexTorusMaskSelects] using hcomponent)
      obtain ⟨other, hother, hedge⟩ := hcomponentEq
      have : other = component := by simpa using hother
      subst other
      have hselected := hstrandFull.selects_of_reachable hstrandSeed
        (ConnectedComponent.exact (hseed.trans hedge.symm))
      simpa [sixVertexTorusMaskSelects] using hselected




theorem sixVertexDegreeTwoStrand_mask_eq_reference_component
    {T : EvenTorus} {omega eta referenceFirst referenceSecond :
      SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (hgraph : sixVertexTorusDisagreementGraph omega eta =
      sixVertexTorusDisagreementGraph referenceFirst referenceSecond)
    (component : SixVertexDisagreementComponent
      referenceFirst referenceSecond)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (hseed : (sixVertexTorusDisagreementGraph
        referenceFirst referenceSecond).connectedComponentMk
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) =
      component.1) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask =
      sixVertexDisagreementComponentSetMask
        referenceFirst referenceSecond {component} := by
  let strandMask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).mask
  have hstrandFull := sixVertexDegreeTwoStrand_mask_full
    homega heta hdegree seed
  have hstrandSeed := sixVertexDegreeTwoStrand_mask_seedEdge
    homega heta hdegree seed
  apply SixVertexArrows.ext <;> funext base
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        referenceFirst referenceSecond {component} (0, base)).2
      refine ⟨component, by simp, ?_⟩
      have hcomponent := sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (0, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)
      rw [hgraph] at hcomponent
      exact hcomponent.trans hseed
    · intro hcomponent
      obtain ⟨other, hother, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          referenceFirst referenceSecond {component} (0, base)).1 (by
            simpa [sixVertexTorusMaskSelects] using hcomponent)
      have : other = component := by simpa using hother
      subst other
      have hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed)
          (0, base) := by
        rw [hgraph]
        exact ConnectedComponent.exact (hseed.trans hedge.symm)
      have hselected := hstrandFull.selects_of_reachable
        hstrandSeed hreach
      simpa [sixVertexTorusMaskSelects] using hselected
  · apply Bool.eq_iff_iff.mpr
    constructor
    · intro hstrand
      apply (sixVertexDisagreementComponentSetMask_selects_iff
        referenceFirst referenceSecond {component} (1, base)).2
      refine ⟨component, by simp, ?_⟩
      have hcomponent := sixVertexDegreeTwoStrand_mask_component
        homega heta hdegree seed (1, base) (by
          simpa [strandMask, sixVertexTorusMaskSelects] using hstrand)
      rw [hgraph] at hcomponent
      exact hcomponent.trans hseed
    · intro hcomponent
      obtain ⟨other, hother, hedge⟩ :=
        (sixVertexDisagreementComponentSetMask_selects_iff
          referenceFirst referenceSecond {component} (1, base)).1 (by
            simpa [sixVertexTorusMaskSelects] using hcomponent)
      have : other = component := by simpa using hother
      subst other
      have hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable
          (sixVertexDegreeTwoOrientedComponentEdge hdegree seed)
          (1, base) := by
        rw [hgraph]
        exact ConnectedComponent.exact (hseed.trans hedge.symm)
      have hselected := hstrandFull.selects_of_reachable
        hstrandSeed hreach
      simpa [sixVertexTorusMaskSelects] using hselected
end

end StatMech.FrontierD
