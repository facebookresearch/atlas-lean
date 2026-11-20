/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle
import Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents










namespace StatMech.FrontierD

noncomputable section


theorem sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hseparate : ¬ (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree first)))
    (j : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree second))) :
    (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree first i).1.1.1 ≠
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree second j).1.1.1 := by
  intro hvertex
  have hdart :
      sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree first i =
        sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree second j :=
    sixVertexOrientedDisagreementDart_vertex_injective
      homega heta hdegree hvertex
  have hfirst := sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    homega heta hdegree first i
  have hsecond := sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    homega heta hdegree second j
  rw [hdart] at hfirst
  exact hseparate (hfirst.trans hsecond.symm)


noncomputable def sixVertexDegreeTwoSeparateStrandCycleFamily
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hseparate : ¬ (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second) :
    SixVertexAtMostTwoCycleFamily T where
  count := 2
  count_le_two := by omega
  cycle i := ![
    sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree first,
    sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree second] i
  tail_disjoint := by
    intro i j hij a b
    fin_cases i <;> fin_cases j
    · simp at hij
    · rw [bne_iff_ne]
      intro htail
      apply sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
        homega heta hdegree first second hseparate a b
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree] using
        htail
    · rw [bne_iff_ne]
      intro htail
      apply sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
        homega heta hdegree first second hseparate b a
      symm
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree] using
        htail
    · simp at hij




theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.separateCycles_or_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    (¬ (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed.first seed.second) ∨
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed.first seed.second := by
  by_cases hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second
  · exact Or.inr hsame
  · exact Or.inl hsame

end

end StatMech.FrontierD
