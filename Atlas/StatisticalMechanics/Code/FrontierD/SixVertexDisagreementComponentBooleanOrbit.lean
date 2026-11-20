/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFullComponentMaskSwap










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

local instance disagreementComponentBooleanOrbitDecidableProp (p : Prop) :
    Decidable p := Classical.propDecidable p


abbrev SixVertexDisagreementComponent
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {component :
      (sixVertexTorusDisagreementGraph omega eta).ConnectedComponent //
    ∃ edge : SixVertexTorusEdge T,
      sixVertexTorusEdgeDisagrees omega eta edge ∧
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
          component}


noncomputable def sixVertexDisagreementComponentSetMask
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    SixVertexArrows T := by
  classical
  let graph := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (∃ component ∈ selected,
        graph.connectedComponentMk (0, v) = component.1)
      vertical := fun v => decide (∃ component ∈ selected,
        graph.connectedComponentMk (1, v) = component.1) }

theorem sixVertexDisagreementComponentSetMask_selects_iff
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta selected) edge = true
      ↔ ∃ component ∈ selected,
        (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
          component.1 := by
  classical
  rcases edge with ⟨direction, vertex⟩
  fin_cases direction <;>
    simp [sixVertexTorusMaskSelects,
      sixVertexDisagreementComponentSetMask]


theorem sixVertexDisagreementComponentSetMask_selects_only_disagreement
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (edge : SixVertexTorusEdge T)
    (hselected : sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected) edge = true) :
    sixVertexTorusEdgeDisagrees omega eta edge := by
  obtain ⟨component, _, hedge⟩ :=
    (sixVertexDisagreementComponentSetMask_selects_iff
      omega eta selected edge).1 hselected
  obtain ⟨seed, hseed, hseedComponent⟩ := component.2
  apply sixVertexDisagreementGraph_reachable_disagrees hseed
  apply ConnectedComponent.exact
  exact hseedComponent.trans hedge.symm



theorem sixVertexDisagreementComponentSetMask_incident_closure
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (vertex : T.Vertex) (first second : Fin 4)
    (hfirst : sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected)
        (sixVertexTorusIncidentEdge T vertex first) = true)
    (hsecond : sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusIncidentEdge T vertex second)) :
    sixVertexTorusMaskSelects
      (sixVertexDisagreementComponentSetMask omega eta selected)
        (sixVertexTorusIncidentEdge T vertex second) = true := by
  let graph := sixVertexTorusDisagreementGraph omega eta
  obtain ⟨component, hcomponent, hfirstComponent⟩ :=
    (sixVertexDisagreementComponentSetMask_selects_iff omega eta selected
      (sixVertexTorusIncidentEdge T vertex first)).1 hfirst
  apply (sixVertexDisagreementComponentSetMask_selects_iff omega eta selected
    (sixVertexTorusIncidentEdge T vertex second)).2
  refine ⟨component, hcomponent, ?_⟩
  by_cases hedges : sixVertexTorusIncidentEdge T vertex first =
      sixVertexTorusIncidentEdge T vertex second
  · simpa [hedges] using hfirstComponent
  · have hfirstDisagrees :=
      sixVertexDisagreementComponentSetMask_selects_only_disagreement
        omega eta selected _ hfirst
    have hadj : graph.Adj
        (sixVertexTorusIncidentEdge T vertex first)
        (sixVertexTorusIncidentEdge T vertex second) :=
      ⟨hedges, hfirstDisagrees, hsecond,
        vertex, first, second, rfl, rfl⟩
    exact (ConnectedComponent.sound hadj.reachable).symm.trans
      hfirstComponent


theorem sixVertexDisagreementComponentSetMask_full
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexDisagreementComponentSetMask omega eta selected) := by
  constructor
  · intro vertex side hside
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexDisagreementComponentSetMask_selects_only_disagreement
      omega eta selected
    rwa [sixVertexTorusLocalSwitchMask_apply] at hside
  · intro vertex first second hfirst hsecond
    rw [sixVertexTorusLocalSwitchMask_apply] at hfirst ⊢
    apply sixVertexDisagreementComponentSetMask_incident_closure
      omega eta selected vertex first second hfirst
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta vertex second).1 hsecond



theorem sixVertexDisagreementComponent_mem_iff_mask_selects
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta))
    (component : SixVertexDisagreementComponent omega eta)
    (edge : SixVertexTorusEdge T)
    (hcomponent :
      (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge =
        component.1) :
    component ∈ selected ↔
      sixVertexTorusMaskSelects
        (sixVertexDisagreementComponentSetMask omega eta selected) edge = true := by
  constructor
  · intro hmem
    apply (sixVertexDisagreementComponentSetMask_selects_iff
      omega eta selected edge).2
    exact ⟨component, hmem, hcomponent⟩
  · intro hselected
    obtain ⟨other, hother, hotherComponent⟩ :=
      (sixVertexDisagreementComponentSetMask_selects_iff
        omega eta selected edge).1 hselected
    have : other = component := by
      apply Subtype.ext
      exact hotherComponent.symm.trans hcomponent
    simpa [this] using hother


theorem sixVertexDisagreementComponentSetMask_injective
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    Function.Injective
      (sixVertexDisagreementComponentSetMask omega eta) := by
  classical
  intro first second hmasks
  ext component
  obtain ⟨edge, _, hcomponent⟩ := component.2
  rw [sixVertexDisagreementComponent_mem_iff_mask_selects omega eta first
      component edge hcomponent,
    sixVertexDisagreementComponent_mem_iff_mask_selects omega eta second
      component edge hcomponent,
    hmasks]


def sixVertexDisagreementComponentCharge
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (component : SixVertexDisagreementComponent omega eta) : Int :=
  ∑ column : Fin T.width,
    if (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk
          (1, (column, svFinLast T.height_pos)) = component.1 then
      (eta.vertical (column, svFinLast T.height_pos)).toNat -
        (omega.vertical (column, svFinLast T.height_pos)).toNat
    else 0


theorem sixVertexDisagreementComponentSetMask_seamTransfer
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexTorusMaskSeamTransfer
        (sixVertexDisagreementComponentSetMask omega eta selected) omega eta =
      ∑ component ∈ selected,
        sixVertexDisagreementComponentCharge omega eta component := by
  classical
  unfold sixVertexTorusMaskSeamTransfer
    sixVertexDisagreementComponentCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro column _
  let edge : SixVertexTorusEdge T :=
    (1, (column, svFinLast T.height_pos))
  let graph := sixVertexTorusDisagreementGraph omega eta
  let difference : Int :=
    (eta.vertical (column, svFinLast T.height_pos)).toNat -
      (omega.vertical (column, svFinLast T.height_pos)).toNat
  by_cases hexists : ∃ component ∈ selected,
      graph.connectedComponentMk edge = component.1
  · obtain ⟨component, hcomponent, hedge⟩ := hexists
    have hsum : (∑ other ∈ selected,
        if graph.connectedComponentMk edge = other.1 then difference
        else 0) = difference := by
      calc
        (∑ other ∈ selected,
            if graph.connectedComponentMk edge = other.1 then difference
            else 0) =
            (if graph.connectedComponentMk edge = component.1 then
              difference else 0) := by
          apply Finset.sum_eq_single component
          · intro other hother hne
            have hcomponentNe :
                graph.connectedComponentMk edge ≠ other.1 := by
              intro heq
              apply hne
              apply Subtype.ext
              exact heq.symm.trans hedge
            simp [hcomponentNe]
          · intro hnot
            exact False.elim (hnot hcomponent)
        _ = difference := by simp [hedge]
    have hmask :
        (sixVertexDisagreementComponentSetMask omega eta selected).vertical
          (column, svFinLast T.height_pos) = true := by
      simpa [edge, graph, sixVertexTorusMaskSelects] using
        (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta selected edge).2 ⟨component, hcomponent, hedge⟩
    simpa [difference, hmask] using hsum.symm
  · have hsum : (∑ other ∈ selected,
        if graph.connectedComponentMk edge = other.1 then difference
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro component hcomponent
      have hne : graph.connectedComponentMk edge ≠ component.1 := by
        intro heq
        exact hexists ⟨component, hcomponent, heq⟩
      simp [hne]
    have hmask :
        (sixVertexDisagreementComponentSetMask omega eta selected).vertical
          (column, svFinLast T.height_pos) = false := by
      cases hm :
          (sixVertexDisagreementComponentSetMask omega eta selected).vertical
            (column, svFinLast T.height_pos)
      · rfl
      · exfalso
        apply hexists
        exact (sixVertexDisagreementComponentSetMask_selects_iff
          omega eta selected edge).1 (by
            simpa [edge, sixVertexTorusMaskSelects] using hm)
    simpa [difference, hmask] using hsum.symm



theorem sixVertexDisagreementComponentSetMask_seamTransfer_of_unit
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (hunit : forall component : SixVertexDisagreementComponent omega eta,
      sixVertexDisagreementComponentCharge omega eta component = 1)
    (selected : Finset (SixVertexDisagreementComponent omega eta)) :
    sixVertexTorusMaskSeamTransfer
        (sixVertexDisagreementComponentSetMask omega eta selected) omega eta =
      selected.card := by
  rw [sixVertexDisagreementComponentSetMask_seamTransfer]
  simp_rw [hunit]
  simp



theorem SixVertexFullDisagreementMask.of_pairSwitch
    {T : EvenTorus} {omega eta firstMask secondMask : SixVertexArrows T}
    (hfirst : SixVertexFullDisagreementMask omega eta firstMask) :
    SixVertexFullDisagreementMask
      (sixVertexTorusSwitchFirst secondMask omega eta)
      (sixVertexTorusSwitchSecond secondMask omega eta) firstMask := by
  constructor
  · intro vertex side hselected
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta vertex side).1 (hfirst.1 vertex side hselected)
  · intro vertex first second hselected hsecond
    apply hfirst.2 vertex first second hselected
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees] at hsecond ⊢
    exact (sixVertexTorusEdgeDisagrees_pairSwitch_iff
      secondMask omega eta _).1 hsecond


theorem SixVertexFullDisagreementMask.switchFirst_ice
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    (sixVertexTorusSwitchFirst mask omega eta).IceRule := by
  intro vertex
  rw [← sixVertexLocalIncomingPattern_count]
  rcases hmask.local_eq_or_swap vertex with hsame | hswap
  · have hfirst := congrArg Prod.fst hsame
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchFirst mask omega eta) vertex =
        sixVertexLocalIncomingPattern omega vertex at hfirst
    rw [hfirst, sixVertexLocalIncomingPattern_count]
    exact homega vertex
  · have hfirst := congrArg Prod.fst hswap
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchFirst mask omega eta) vertex =
        sixVertexLocalIncomingPattern eta vertex at hfirst
    rw [hfirst, sixVertexLocalIncomingPattern_count]
    exact heta vertex


theorem SixVertexFullDisagreementMask.switchSecond_ice
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    (sixVertexTorusSwitchSecond mask omega eta).IceRule := by
  intro vertex
  rw [← sixVertexLocalIncomingPattern_count]
  rcases hmask.local_eq_or_swap vertex with hsame | hswap
  · have hsecond := congrArg Prod.snd hsame
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchSecond mask omega eta) vertex =
        sixVertexLocalIncomingPattern eta vertex at hsecond
    rw [hsecond, sixVertexLocalIncomingPattern_count]
    exact heta vertex
  · have hsecond := congrArg Prod.snd hswap
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchSecond mask omega eta) vertex =
        sixVertexLocalIncomingPattern omega vertex at hsecond
    rw [hsecond, sixVertexLocalIncomingPattern_count]
    exact homega vertex

end

end StatMech.FrontierD
