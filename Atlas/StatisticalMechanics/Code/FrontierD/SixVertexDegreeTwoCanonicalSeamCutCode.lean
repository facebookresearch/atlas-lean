/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoStrandCycleCut
import Code.FrontierD.SixVertexPositiveSeamWindingFlows










namespace StatMech.FrontierD

noncomputable section


def sixVertexTorusEdgePhysical {T : EvenTorus}
    (edge : SixVertexTorusEdge T) : Bool × T.Vertex :=
  if edge.1 = 0 then (false, edge.2) else (true, edge.2)

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_physical
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).physical =
      sixVertexTorusEdgePhysical edge := by
  rcases edge with ⟨direction, vertex⟩
  fin_cases direction <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical, sixVertexTorusEdgePhysical]


def SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    SixVertexTorusEdge T :=
  sixVertexTorusDartEdge T
    (sixVertexDegreeTwoLocalMate hdegree (seed.nextPositiveDart hsame).1).1

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    (seed.nextPositiveSeamEdge hsame).1 = 1 ∧
      (seed.nextPositiveSeamEdge hsame).2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape
    (seed.nextPositiveDart_seamSign hsame)



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_nextPositiveSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.firstSeamEdge ≠ seed.nextPositiveSeamEdge hsame := by
  intro hedge
  apply seed.first_ne_nextPositiveDart hsame
  apply (sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree).injective
  apply Subtype.ext
  exact hedge


def SixVertexDegreeTwoSynchronizedHighChargeSeed.nextPositiveWindingColumn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) : Fin T.width :=
  (seed.nextPositiveSeamEdge hsame).2.1

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalWindingColumns_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    seed.firstWindingColumn ≠ seed.nextPositiveWindingColumn hsame := by
  intro hcolumn
  apply seed.firstSeamEdge_ne_nextPositiveSeamEdge hsame
  apply Prod.ext
  · exact seed.firstSeamEdge_shape.1.trans
      (seed.nextPositiveSeamEdge_shape hsame).1.symm
  · apply Prod.ext
    · exact hcolumn
    · exact seed.firstSeamEdge_shape.2.trans
        (seed.nextPositiveSeamEdge_shape hsame).2.symm


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_first_physical
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    ((seed.sameStrandArcPair hsame).first.edge
      (seed.sameStrandArcPair hsame).first.firstIndex).physical =
        sixVertexTorusEdgePhysical seed.firstSeamEdge := by
  change (sixVertexDegreeTwoOrientedStrandEdge hdegree
    (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
      (sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
        ⟨0, seed.nextPositiveIndex_val_pos hsame⟩))).physical = _
  unfold sixVertexDegreeTwoOrientedStrandEdge
  rw [sixVertexDirectedTorusEdgeOfArrow_physical]
  apply congrArg sixVertexTorusEdgePhysical
  change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
          (sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
            ⟨0, seed.nextPositiveIndex_val_pos hsame⟩))).1 =
    sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree seed.first.1).1
  rw [show sixVertexFinPrefixIndex (seed.nextPositiveIndex hsame)
      ⟨0, seed.nextPositiveIndex_val_pos hsame⟩ =
        sixVertexDegreeTwoStrandCycleZeroIndex
          homega heta hdegree seed.first by
      apply Fin.ext
      rfl,
    sixVertexDegreeTwoStrandCycleEnumeration_zero]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sameStrandArcPair_second_physical
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    ((seed.sameStrandArcPair hsame).second.edge
      (seed.sameStrandArcPair hsame).second.firstIndex).physical =
        sixVertexTorusEdgePhysical (seed.nextPositiveSeamEdge hsame) := by
  change (sixVertexDegreeTwoOrientedStrandEdge hdegree
    (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
      (sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
        ⟨0, by omega⟩))).physical = _
  unfold sixVertexDegreeTwoOrientedStrandEdge
  rw [sixVertexDirectedTorusEdgeOfArrow_physical]
  apply congrArg sixVertexTorusEdgePhysical
  change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed.first
          (sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
            ⟨0, by omega⟩))).1 =
    sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree (seed.nextPositiveDart hsame).1).1
  rw [show sixVertexFinSuffixIndex (seed.nextPositiveIndex hsame)
      ⟨0, by omega⟩ = seed.nextPositiveIndex hsame by
      apply Fin.ext
      simp]
  rfl


structure SixVertexCanonicalSameStrandCutCode (T : EvenTorus) where
  arcs : SixVertexDirectedComplementaryArcPair T
  firstSeamEdge : SixVertexTorusEdge T
  secondSeamEdge : SixVertexTorusEdge T
  first_shape : firstSeamEdge.1 = 1 ∧
    firstSeamEdge.2.2 = svFinLast T.height_pos
  second_shape : secondSeamEdge.1 = 1 ∧
    secondSeamEdge.2.2 = svFinLast T.height_pos
  seam_ne : firstSeamEdge ≠ secondSeamEdge
  first_marked : (arcs.first.edge arcs.first.firstIndex).physical =
    sixVertexTorusEdgePhysical firstSeamEdge
  second_marked : (arcs.second.edge arcs.second.firstIndex).physical =
    sixVertexTorusEdgePhysical secondSeamEdge



def sixVertexDecodeVerticalPhysicalEdge {T : EvenTorus}
    (physical : Bool × T.Vertex) : SixVertexTorusEdge T :=
  (1, physical.2)

theorem sixVertexDecodeVerticalPhysicalEdge_leftInverse
    {T : EvenTorus} (edge : SixVertexTorusEdge T) (hvertical : edge.1 = 1) :
    sixVertexDecodeVerticalPhysicalEdge (sixVertexTorusEdgePhysical edge) =
      edge := by
  rcases edge with ⟨direction, vertex⟩
  fin_cases direction
  · simp at hvertical
  · rfl


def SixVertexCanonicalSameStrandCutCode.decodeSeamPair
    {T : EvenTorus} (code : SixVertexCanonicalSameStrandCutCode T) :
    SixVertexTorusEdge T × SixVertexTorusEdge T :=
  (sixVertexDecodeVerticalPhysicalEdge
      (code.arcs.first.edge code.arcs.first.firstIndex).physical,
    sixVertexDecodeVerticalPhysicalEdge
      (code.arcs.second.edge code.arcs.second.firstIndex).physical)



@[simp] theorem SixVertexCanonicalSameStrandCutCode.decodeSeamPair_eq
    {T : EvenTorus} (code : SixVertexCanonicalSameStrandCutCode T) :
    code.decodeSeamPair = (code.firstSeamEdge, code.secondSeamEdge) := by
  unfold SixVertexCanonicalSameStrandCutCode.decodeSeamPair
  rw [code.first_marked, code.second_marked,
    sixVertexDecodeVerticalPhysicalEdge_leftInverse _ code.first_shape.1,
    sixVertexDecodeVerticalPhysicalEdge_leftInverse _ code.second_shape.1]



theorem SixVertexCanonicalSameStrandCutCode.seamPair_eq_of_arcs_eq
    {T : EvenTorus} (first second : SixVertexCanonicalSameStrandCutCode T)
    (harcs : first.arcs = second.arcs) :
    (first.firstSeamEdge, first.secondSeamEdge) =
      (second.firstSeamEdge, second.secondSeamEdge) := by
  rw [← first.decodeSeamPair_eq, ← second.decodeSeamPair_eq]
  unfold SixVertexCanonicalSameStrandCutCode.decodeSeamPair
  rw [harcs]


def SixVertexDegreeTwoSynchronizedHighChargeSeed.canonicalSameStrandCutCode
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second) :
    SixVertexCanonicalSameStrandCutCode T where
  arcs := seed.sameStrandArcPair hsame
  firstSeamEdge := seed.firstSeamEdge
  secondSeamEdge := seed.nextPositiveSeamEdge hsame
  first_shape := seed.firstSeamEdge_shape
  second_shape := seed.nextPositiveSeamEdge_shape hsame
  seam_ne := seed.firstSeamEdge_ne_nextPositiveSeamEdge hsame
  first_marked := seed.sameStrandArcPair_first_physical hsame
  second_marked := seed.sameStrandArcPair_second_physical hsame

end

end StatMech.FrontierD
