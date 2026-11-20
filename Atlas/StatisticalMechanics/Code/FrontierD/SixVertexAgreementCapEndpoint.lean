/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDirectedSimpleCycleFlip
import Code.FrontierD.SixVertexPairTwoCycleObstructionRepair
import Code.FrontierD.SixVertexDegreeTwoStrandCycleCut
















namespace StatMech.FrontierD

noncomputable section


def SixVertexDirectedTorusEdge.IsAgreement
    {T : EvenTorus} (edge : SixVertexDirectedTorusEdge T)
    (omega eta : SixVertexArrows T) : Prop :=
  match edge with
  | .horizontal base _ => omega.horizontal base = eta.horizontal base
  | .vertical base _ => omega.vertical base = eta.vertical base


def SixVertexDirectedSimpleArc.Follows
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T)
    (omega : SixVertexArrows T) : Prop :=
  forall i, (arc.edge i).Follows omega


def SixVertexDirectedSimpleArc.IsAgreement
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T)
    (omega eta : SixVertexArrows T) : Prop :=
  forall i, (arc.edge i).IsAgreement omega eta


def sixVertexFourByTwoAgreementSuccessor
    (v : sixVertexFourByTwoTorus.Vertex) :
    sixVertexFourByTwoTorus.Vertex :=
  if v.1.val % 2 = v.2.val % 2 then
    (SixVertexArrows.cyclicPred sixVertexFourByTwoTorus.width_pos v.1, v.2)
  else
    (v.1, finitePeriodicSucc sixVertexFourByTwoTorus.height_pos v.2)



theorem sixVertexFourByTwo_agreement_followed_head
    (edge : SixVertexDirectedTorusEdge sixVertexFourByTwoTorus)
    (hfollows : edge.Follows sixVertexFourByTwoLowArrows)
    (hagrees : edge.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    edge.head = sixVertexFourByTwoAgreementSuccessor edge.tail := by
  rcases edge with ⟨⟨x, y⟩, positive⟩ | ⟨⟨x, y⟩, positive⟩ <;>
    fin_cases x <;> fin_cases y <;> cases positive
  all_goals simp_all [SixVertexDirectedTorusEdge.Follows,
      SixVertexDirectedTorusEdge.IsAgreement,
      SixVertexDirectedTorusEdge.head, SixVertexDirectedTorusEdge.tail,
      sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows,
      sixVertexFourByTwoAgreementSuccessor,
      SixVertexArrows.cyclicPred, finitePeriodicSucc,
      sixVertexFourByTwoTorus]



theorem SixVertexDirectedSimpleArc.agreement_tail_next
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (i : Fin (cap.length - 1)) :
    (cap.edge ⟨i.val + 1, by omega⟩).tail =
      sixVertexFourByTwoAgreementSuccessor
        (cap.edge ⟨i.val, by omega⟩).tail := by
  rw [← cap.head_eq_next_tail i]
  exact sixVertexFourByTwo_agreement_followed_head
    (cap.edge ⟨i.val, by omega⟩)
    (hfollows ⟨i.val, by omega⟩)
    (hagrees ⟨i.val, by omega⟩)



def sixVertexFourByTwoCanonicalFirstDisagreementArc :
    SixVertexDirectedSimpleArc sixVertexFourByTwoTorus where
  length := 4
  length_pos := by norm_num
  edge i :=
    if i.val = 0 then .vertical (sixVertexFourByTwoVertex 0 1) false
    else if i.val = 1 then .horizontal (sixVertexFourByTwoVertex 3 1) false
    else if i.val = 2 then .vertical (sixVertexFourByTwoVertex 3 0) false
    else .horizontal (sixVertexFourByTwoVertex 2 0) false
  head_eq_next_tail := by
    intro i
    fin_cases i <;>
      norm_num [SixVertexDirectedTorusEdge.head,
        SixVertexDirectedTorusEdge.tail, sixVertexFourByTwoVertex,
        finitePeriodicSucc, sixVertexFourByTwoTorus]
  tail_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.tail,
        sixVertexFourByTwoVertex, finitePeriodicSucc,
        sixVertexFourByTwoTorus]
  physical_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByTwoVertex]

@[simp] theorem sixVertexFourByTwoCanonicalFirstDisagreementArc_start :
    sixVertexFourByTwoCanonicalFirstDisagreementArc.start =
      sixVertexFourByTwoVertex 0 0 := by
  rfl

@[simp] theorem sixVertexFourByTwoCanonicalFirstDisagreementArc_finish :
    sixVertexFourByTwoCanonicalFirstDisagreementArc.finish =
      sixVertexFourByTwoVertex 2 0 := by
  rfl




theorem sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (hstart : cap.start = sixVertexFourByTwoVertex 2 0)
    (hfinish : cap.finish = sixVertexFourByTwoVertex 0 0) :
    exists i : Fin cap.length,
      (cap.edge i).tail = sixVertexFourByTwoVertex 0 1 := by
  have htail0 :
      (cap.edge ⟨0, cap.length_pos⟩).tail =
        sixVertexFourByTwoVertex 2 0 := by
    exact hstart
  have hlengthTwo : 2 <= cap.length := by
    by_contra hnot
    have hpositive := cap.length_pos
    have hlength : cap.length = 1 := by omega
    have hlast : cap.lastIndex = ⟨0, cap.length_pos⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail0] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail1 :
      (cap.edge ⟨1, by omega⟩).tail = sixVertexFourByTwoVertex 1 0 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨0, by omega⟩
    rw [htail0] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  have hlengthThree : 3 <= cap.length := by
    by_contra hnot
    have hlength : cap.length = 2 := by omega
    have hlast : cap.lastIndex = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail1] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail2 :
      (cap.edge ⟨2, by omega⟩).tail = sixVertexFourByTwoVertex 1 1 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨1, by omega⟩
    rw [htail1] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  have hlengthFour : 4 <= cap.length := by
    by_contra hnot
    have hlength : cap.length = 3 := by omega
    have hlast : cap.lastIndex = ⟨2, by omega⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail2] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail3 :
      (cap.edge ⟨3, by omega⟩).tail = sixVertexFourByTwoVertex 0 1 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨2, by omega⟩
    rw [htail2] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  exact ⟨⟨3, by omega⟩, htail3⟩



theorem sixVertexFourByTwo_no_internallyDisjointAgreementCap
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (hstart : cap.start = sixVertexFourByTwoCanonicalFirstDisagreementArc.finish)
    (hfinish : cap.finish = sixVertexFourByTwoCanonicalFirstDisagreementArc.start) :
    Not (forall i j,
      (cap.edge i).tail ≠
        (sixVertexFourByTwoCanonicalFirstDisagreementArc.edge j).tail) := by
  intro hdisjoint
  obtain ⟨i, hi⟩ :=
    sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior cap
      hfollows hagrees
      (by simpa using hstart) (by simpa using hfinish)
  apply hdisjoint i ⟨1, by
    change 1 < 4
    norm_num⟩
  simpa [sixVertexFourByTwoCanonicalFirstDisagreementArc,
    SixVertexDirectedTorusEdge.tail, sixVertexFourByTwoVertex,
    finitePeriodicSucc, sixVertexFourByTwoTorus] using hi

end

end StatMech.FrontierD
