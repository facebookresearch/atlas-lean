/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents
import Code.FrontierD.SixVertexWindingCycleBranchRecovery










namespace StatMech.FrontierD

noncomputable section


def sixVertexPositiveVerticalWindingCycle {T : EvenTorus}
    (column : Fin T.width) : SixVertexDirectedSimpleCycle T where
  length := T.height
  length_pos := T.height_pos
  edge := fun row => .vertical (column, row) true
  head_eq_next_tail := by
    intro row
    rfl
  tail_injective := by
    intro first second h
    exact congrArg Prod.snd h
  physical_injective := by
    intro first second h
    exact congrArg (fun edge => edge.2.2) h


def sixVertexPositiveHorizontalWindingCycle {T : EvenTorus}
    (row : Fin T.height) : SixVertexDirectedSimpleCycle T where
  length := T.width
  length_pos := T.width_pos
  edge := fun column => .horizontal (column, row) true
  head_eq_next_tail := by
    intro column
    rfl
  tail_injective := by
    intro first second h
    exact congrArg Prod.fst h
  physical_injective := by
    intro first second h
    exact congrArg (fun edge => edge.2.1) h


def SixVertexAtMostTwoCycleFamily.single {T : EvenTorus}
    (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexAtMostTwoCycleFamily T where
  count := 1
  count_le_two := by omega
  cycle := fun _ => cycle
  tail_disjoint := by
    intro i j hne
    fin_cases i
    fin_cases j
    simp at hne


def sixVertexPositiveVerticalWindingFamily {T : EvenTorus}
    (column : Fin T.width) : SixVertexAtMostTwoCycleFamily T :=
  .single (sixVertexPositiveVerticalWindingCycle column)


def sixVertexPositiveHorizontalWindingFamily {T : EvenTorus}
    (row : Fin T.height) : SixVertexAtMostTwoCycleFamily T :=
  .single (sixVertexPositiveHorizontalWindingCycle row)

@[simp] theorem sixVertexPositiveHorizontalWindingFamily_horizontalFlow_same
    {T : EvenTorus} (row : Fin T.height) (column : Fin T.width) :
    (sixVertexPositiveHorizontalWindingFamily row).horizontalFlow
      (column, row) = 1 := by
  classical
  simp [sixVertexPositiveHorizontalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexDirectedSimpleCycle.horizontalFlow,
    sixVertexPositiveHorizontalWindingCycle,
    SixVertexDirectedTorusEdge.horizontalFlow]
  rw [Finset.card_eq_one]
  refine ⟨column, ?_⟩
  ext other
  simp [eq_comm]

@[simp] theorem sixVertexPositiveHorizontalWindingFamily_horizontalFlow_other
    {T : EvenTorus} {first second : Fin T.height} (hne : first ≠ second)
    (column : Fin T.width) :
    (sixVertexPositiveHorizontalWindingFamily second).horizontalFlow
      (column, first) = 0 := by
  classical
  simp [sixVertexPositiveHorizontalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexDirectedSimpleCycle.horizontalFlow,
    sixVertexPositiveHorizontalWindingCycle,
    SixVertexDirectedTorusEdge.horizontalFlow, hne]

@[simp] theorem sixVertexPositiveVerticalWindingFamily_verticalFlow_same
    {T : EvenTorus} (column : Fin T.width) (row : Fin T.height) :
    (sixVertexPositiveVerticalWindingFamily column).verticalFlow (column, row) = 1 := by
  classical
  simp [sixVertexPositiveVerticalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexDirectedSimpleCycle.verticalFlow,
    sixVertexPositiveVerticalWindingCycle,
    SixVertexDirectedTorusEdge.verticalFlow]
  rw [Finset.card_eq_one]
  refine ⟨row, ?_⟩
  ext other
  simp [eq_comm]

@[simp] theorem sixVertexPositiveVerticalWindingFamily_verticalFlow_other
    {T : EvenTorus} {first second : Fin T.width} (hne : first ≠ second)
    (row : Fin T.height) :
    (sixVertexPositiveVerticalWindingFamily second).verticalFlow (first, row) = 0 := by
  classical
  simp [sixVertexPositiveVerticalWindingFamily,
    SixVertexAtMostTwoCycleFamily.single,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexDirectedSimpleCycle.verticalFlow,
    sixVertexPositiveVerticalWindingCycle,
    SixVertexDirectedTorusEdge.verticalFlow, hne]


def SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : SixVertexTorusEdge T :=
  sixVertexTorusDartEdge T
    (sixVertexDegreeTwoLocalMate hdegree seed.first.1).1


def SixVertexDegreeTwoSynchronizedHighChargeSeed.secondSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : SixVertexTorusEdge T :=
  sixVertexTorusDartEdge T
    (sixVertexDegreeTwoLocalMate hdegree seed.second.1).1



theorem sixVertexTorusEdgeSeamSign_eq_one_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {edge : SixVertexTorusEdge T}
    (h : sixVertexTorusEdgeSeamSign omega eta edge = 1) :
    edge.1 = 1 ∧ edge.2.2 = svFinLast T.height_pos := by
  unfold sixVertexTorusEdgeSeamSign at h
  split at h
  · assumption
  · simp at h

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstSeamEdge.1 = 1 ∧
      seed.firstSeamEdge.2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape seed.first_seamSign

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.secondSeamEdge_shape
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.secondSeamEdge.1 = 1 ∧
      seed.secondSeamEdge.2.2 = svFinLast T.height_pos :=
  sixVertexTorusEdgeSeamSign_eq_one_shape seed.second_seamSign


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstSeamEdge_ne_secondSeamEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstSeamEdge ≠ seed.secondSeamEdge := by
  intro hedge
  apply seed.distinct
  apply (sixVertexOrientedDisagreementDartEquivEdge homega heta hdegree).injective
  apply Subtype.ext
  exact hedge


def SixVertexDegreeTwoSynchronizedHighChargeSeed.firstWindingColumn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : Fin T.width := seed.firstSeamEdge.2.1


def SixVertexDegreeTwoSynchronizedHighChargeSeed.secondWindingColumn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : Fin T.width := seed.secondSeamEdge.2.1

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingColumns_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.firstWindingColumn ≠ seed.secondWindingColumn := by
  intro hcolumn
  apply seed.firstSeamEdge_ne_secondSeamEdge
  apply Prod.ext
  · exact seed.firstSeamEdge_shape.1.trans seed.secondSeamEdge_shape.1.symm
  · apply Prod.ext
    · exact hcolumn
    · exact seed.firstSeamEdge_shape.2.trans seed.secondSeamEdge_shape.2.symm


def SixVertexDegreeTwoSynchronizedHighChargeSeed.firstWindingFamily
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : SixVertexAtMostTwoCycleFamily T :=
  sixVertexPositiveVerticalWindingFamily seed.firstWindingColumn


def SixVertexDegreeTwoSynchronizedHighChargeSeed.secondWindingFamily
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) : SixVertexAtMostTwoCycleFamily T :=
  sixVertexPositiveVerticalWindingFamily seed.secondWindingColumn



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingFlows_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (row : Fin T.height) :
    seed.firstWindingFamily.verticalFlow (seed.firstWindingColumn, row) ≠
      seed.secondWindingFamily.verticalFlow (seed.firstWindingColumn, row) := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.firstWindingFamily,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.secondWindingFamily,
    seed.windingColumns_ne]



theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.windingTargets_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    {source : SixVertexArrows T × SixVertexArrows T}
    (first : SixVertexSignedWindingCycleTarget source
      seed.firstWindingFamily true)
    (second : SixVertexSignedWindingCycleTarget source
      seed.secondWindingFamily true) :
    first.target ≠ second.target :=
  first.targets_ne_of_signedVerticalFlow_ne second
    (seed.firstWindingColumn, svFinLast T.height_pos)
    (by simpa using seed.windingFlows_ne (svFinLast T.height_pos))

end

end StatMech.FrontierD
