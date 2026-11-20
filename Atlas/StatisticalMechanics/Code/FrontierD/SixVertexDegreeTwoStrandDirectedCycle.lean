/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
import Code.FrontierD.SixVertexPairTwoCycleRelation











namespace StatMech.FrontierD

noncomputable section



def sixVertexDirectedTorusEdgeOfArrow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) : SixVertexDirectedTorusEdge T :=
  if edge.1 = 0 then
    .horizontal edge.2 (omega.horizontal edge.2)
  else .vertical edge.2 (omega.vertical edge.2)

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_tail
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).tail =
      (sixVertexTorusEdgeOutgoingDart omega edge).1 := by
  rcases edge with ⟨direction, ⟨column, row⟩⟩
  fin_cases direction <;>
    cases hh : omega.horizontal (column, row) <;>
    cases hv : omega.vertical (column, row) <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.tail,
      sixVertexTorusEdgeOutgoingDart, hh, hv]

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_head
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).head =
      (sixVertexTorusDartBondMate T
        (sixVertexTorusEdgeOutgoingDart omega edge)).1 := by
  rcases edge with ⟨direction, ⟨column, row⟩⟩
  fin_cases direction <;>
    cases hh : omega.horizontal (column, row) <;>
    cases hv : omega.vertical (column, row) <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.head,
      sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartBondMate, hh, hv,
      svCyclicPred_finitePeriodicSucc]


theorem sixVertexDirectedTorusEdgeOfArrow_physical_injective
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Function.Injective
      (fun edge : SixVertexTorusEdge T =>
        (sixVertexDirectedTorusEdgeOfArrow omega edge).physical) := by
  intro first second heq
  rcases first with ⟨firstDirection, firstVertex⟩
  rcases second with ⟨secondDirection, secondVertex⟩
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical] at heq ⊢ <;>
    exact heq


def sixVertexDegreeTwoOrientedStrandEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexDirectedTorusEdge T :=
  sixVertexDirectedTorusEdgeOfArrow omega
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1)

theorem sixVertexDegreeTwoLocalMate_incoming_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1.1
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1.2 = false := by
  have hne := sixVertexDegreeTwoLocalMate_incoming_ne
    homega heta hdegree dart.1
  rw [dart.2] at hne
  cases h : sixVertexLocalIncomingPattern omega
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1.1
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1.2 <;> simp_all

theorem sixVertexDegreeTwoOrientedStrandEdge_tail
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).tail =
      dart.1.1.1 := by
  rw [sixVertexDegreeTwoOrientedStrandEdge,
    sixVertexDirectedTorusEdgeOfArrow_tail,
    sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1
      (sixVertexDegreeTwoLocalMate_incoming_false
        homega heta hdegree dart)]
  exact sixVertexDegreeTwoLocalMate_vertex hdegree dart.1

theorem sixVertexDegreeTwoOrientedStrandEdge_head
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).head =
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree dart).1.1.1 := by
  rw [sixVertexDegreeTwoOrientedStrandEdge,
    sixVertexDirectedTorusEdgeOfArrow_head,
    sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1
      (sixVertexDegreeTwoLocalMate_incoming_false
        homega heta hdegree dart)]
  rfl


theorem sixVertexOrientedDisagreementDart_vertex_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Function.Injective
      (fun dart : SixVertexOrientedDisagreementDart omega eta =>
        dart.1.1.1) := by
  intro first second hvertex
  change first.1.1.1 = second.1.1.1 at hvertex
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hvertex
  · by_contra hside
    have hbits := sixVertexLocalIncoming_ne_at_two_disagreements
      (sixVertexLocalIncomingPattern omega first.1.1.1)
      (sixVertexLocalIncomingPattern eta first.1.1.1)
      first.1.1.2 second.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega first.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta first.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree first.1)
      (sixVertexDisagreementDart_side_mem first.1)
      (by
        simpa only [hvertex] using
          (sixVertexDisagreementDart_side_mem second.1))
      (Ne.symm hside)
    apply hbits
    calc
      sixVertexLocalIncomingPattern omega first.1.1.1 second.1.1.2 =
          sixVertexLocalIncomingPattern omega second.1.1.1 second.1.1.2 := by
        rw [hvertex]
      _ = true := second.2
      _ = sixVertexLocalIncomingPattern omega first.1.1.1 first.1.1.2 :=
        first.2.symm



theorem sixVertexDegreeTwoOrientedStrandEdge_physical_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Function.Injective
      (fun dart : SixVertexOrientedDisagreementDart omega eta =>
        (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).physical) := by
  intro first second heq
  apply (sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree).injective
  apply Subtype.ext
  apply sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
  exact heq



def sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (length : Nat) (length_pos : 0 < length)
    (dart : Fin length → SixVertexOrientedDisagreementDart omega eta)
    (dart_injective : Function.Injective dart)
    (next : ∀ i, dart (finitePeriodicSucc length_pos i) =
      sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree (dart i)) :
    SixVertexDirectedSimpleCycle T where
  length := length
  length_pos := length_pos
  edge := fun i => sixVertexDegreeTwoOrientedStrandEdge hdegree (dart i)
  head_eq_next_tail := by
    intro i
    rw [sixVertexDegreeTwoOrientedStrandEdge_head homega heta hdegree,
      sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree,
      next i]
  tail_injective := by
    intro first second heq
    apply dart_injective
    apply sixVertexOrientedDisagreementDart_vertex_injective
      homega heta hdegree
    simpa only [sixVertexDegreeTwoOrientedStrandEdge_tail
      homega heta hdegree] using heq
  physical_injective := by
    intro first second heq
    apply dart_injective
    apply sixVertexDegreeTwoOrientedStrandEdge_physical_injective
      homega heta hdegree
    exact heq

local instance sixVertexStrandDirectedCycleSameCycleDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    DecidableRel
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle :=
  Classical.decRel _



theorem permCycleFinEquivSupport_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (cycle : Equiv.Perm D) (hcycle : cycle.IsCycle)
    (seed : cycle.support) (i : Fin (orderOf cycle)) :
    permCycleFinEquivSupport cycle hcycle seed
        (finitePeriodicSucc (orderOf_pos cycle) i) =
      ⟨cycle (permCycleFinEquivSupport cycle hcycle seed i).1,
        Equiv.Perm.apply_mem_support.mpr
          (permCycleFinEquivSupport cycle hcycle seed i).2⟩ := by
  apply Subtype.ext
  change (cycle ^ ((i.val + 1) % orderOf cycle)) seed.1 =
    cycle ((cycle ^ i.val) seed.1)
  rw [pow_mod_orderOf]
  simp only [pow_succ', Equiv.Perm.mul_apply]



noncomputable def sixVertexDegreeTwoStrandCyclePerm
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Equiv.Perm (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree).cycleOf seed

theorem sixVertexDegreeTwoStrandCyclePerm_isCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed).IsCycle :=
  Equiv.Perm.isCycle_cycleOf _
    (sixVertexOrientedDegreeTwoStrandSuccessor_ne
      homega heta hdegree seed)

theorem sixVertexDegreeTwoStrandCyclePerm_seed_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    seed ∈ (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed).support := by
  rw [Equiv.Perm.mem_support]
  change (sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree).cycleOf seed seed ≠ seed
  rw [Equiv.Perm.cycleOf_apply_self]
  exact sixVertexOrientedDegreeTwoStrandSuccessor_ne
    homega heta hdegree seed


noncomputable def sixVertexDegreeTwoStrandCycleEnumerationEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed)) ≃
      (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed).support :=
  permCycleFinEquivSupport
    (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCyclePerm_isCycle
      homega heta hdegree seed)
    ⟨seed, sixVertexDegreeTwoStrandCyclePerm_seed_mem
      homega heta hdegree seed⟩

noncomputable def sixVertexDegreeTwoStrandCycleEnumeration
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed)) →
      SixVertexOrientedDisagreementDart omega eta :=
  fun i => (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed i).1

theorem sixVertexDegreeTwoStrandCycleEnumeration_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Function.Injective (sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed) := by
  intro first second heq
  apply (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed).injective
  exact Subtype.ext heq


theorem sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  let cycle := sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed
  let enumerate := sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed
  have hmem : (enumerate i).1 ∈ cycle.support := (enumerate i).2
  by_contra hnot
  apply (Equiv.Perm.mem_support.mp hmem)
  exact Equiv.Perm.cycleOf_apply_of_not_sameCycle hnot

set_option maxHeartbeats 1000000 in

theorem sixVertexDegreeTwoStrandCycleEnumeration_next
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) :
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (finitePeriodicSucc
          (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed)) i) =
      sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  let cycle := sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed
  let enumerate := sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed
  have hcycle := sixVertexDegreeTwoStrandCyclePerm_isCycle
    homega heta hdegree seed
  have hnext := congrArg Subtype.val
    (permCycleFinEquivSupport_succ cycle hcycle
      ⟨seed, sixVertexDegreeTwoStrandCyclePerm_seed_mem
        homega heta hdegree seed⟩ i)
  have hsame :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed (enumerate i).1 := by
    exact sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
      homega heta hdegree seed i
  have hsame' :
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := hsame
  calc
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (finitePeriodicSucc
          (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
            homega heta hdegree seed)) i) = cycle (enumerate i).1 := by
      simpa only [cycle, enumerate,
        sixVertexDegreeTwoStrandCycleEnumeration,
        sixVertexDegreeTwoStrandCycleEnumerationEquiv] using hnext
    _ = sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
      change (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).cycleOf seed
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed i) = _
      rw [Equiv.Perm.cycleOf_apply, if_pos hsame']



noncomputable def sixVertexDegreeTwoStrandDirectedSimpleCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexDirectedSimpleCycle T :=
  sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration
    homega heta hdegree
    (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))
    (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))
    (sixVertexDegreeTwoStrandCycleEnumeration
      homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCycleEnumeration_injective
      homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCycleEnumeration_next
      homega heta hdegree seed)

end

end StatMech.FrontierD
