/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalFineFiberFactorization
import Code.FrontierD.FKMedialLoopTopology











namespace StatMech.FrontierD

noncomputable section


def sixVertexPairUnionHorizontal
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  (pair.1.horizontal v).toNat + (pair.2.horizontal v).toNat


def sixVertexPairUnionVertical
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  (pair.1.vertical v).toNat + (pair.2.vertical v).toNat


def SixVertexTorusCirculation
    (T : EvenTorus) (horizontal vertical : T.Vertex -> Int) : Prop :=
  forall v,
    horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        vertical (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) =
      horizontal v + vertical v


theorem sixVertexFlowConservation_of_ice
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex) :
    ((omega.horizontal
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)).toNat : Int) +
        (omega.vertical
          (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)).toNat =
      (omega.horizontal v).toNat + (omega.vertical v).toNat := by
  have hice := homega v
  unfold SixVertexArrows.incomingCount at hice
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hice ⊢
  generalize he : omega.horizontal v = e at hice ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hice ⊢
  generalize hn : omega.vertical v = n at hice ⊢
  cases w <;> cases e <;> cases s <;> cases n
  all_goals norm_num at hice
  all_goals norm_num


theorem sixVertexPairUnion_isCirculation
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T)
    (hfirst : pair.1.IceRule) (hsecond : pair.2.IceRule) :
    SixVertexTorusCirculation T
      (sixVertexPairUnionHorizontal pair)
      (sixVertexPairUnionVertical pair) := by
  intro v
  have hfirstFlow := sixVertexFlowConservation_of_ice pair.1 hfirst v
  have hsecondFlow := sixVertexFlowConservation_of_ice pair.2 hsecond v
  unfold sixVertexPairUnionHorizontal sixVertexPairUnionVertical
  omega


def sixVertexPairUnionHorizontalDelta
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  sixVertexPairUnionHorizontal target v -
    sixVertexPairUnionHorizontal source v


def sixVertexPairUnionVerticalDelta
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (v : T.Vertex) : Int :=
  sixVertexPairUnionVertical target v -
    sixVertexPairUnionVertical source v



theorem sixVertexPairUnionDelta_isCirculation
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (hsourceFirst : source.1.IceRule) (hsourceSecond : source.2.IceRule)
    (htargetFirst : target.1.IceRule) (htargetSecond : target.2.IceRule) :
    SixVertexTorusCirculation T
      (sixVertexPairUnionHorizontalDelta source target)
      (sixVertexPairUnionVerticalDelta source target) := by
  intro v
  have hsource := sixVertexPairUnion_isCirculation
    source hsourceFirst hsourceSecond v
  have htarget := sixVertexPairUnion_isCirculation
    target htargetFirst htargetSecond v
  unfold sixVertexPairUnionHorizontalDelta
    sixVertexPairUnionVerticalDelta
  omega

theorem sixVertexTorusCirculation_zero (T : EvenTorus) :
    SixVertexTorusCirculation T (fun _ => 0) (fun _ => 0) := by
  intro v
  simp

theorem SixVertexTorusCirculation.add
    {T : EvenTorus} {horizontal₁ vertical₁ horizontal₂ vertical₂ :
      T.Vertex -> Int}
    (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
    (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
    SixVertexTorusCirculation T
      (fun v => horizontal₁ v + horizontal₂ v)
      (fun v => vertical₁ v + vertical₂ v) := by
  intro v
  have h₁ := hfirst v
  have h₂ := hsecond v
  change
    (horizontal₁ (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        horizontal₂ (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)) +
      (vertical₁ (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) +
        vertical₂ (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)) =
    (horizontal₁ v + horizontal₂ v) + (vertical₁ v + vertical₂ v)
  omega

theorem SixVertexTorusCirculation.neg
    {T : EvenTorus} {horizontal vertical : T.Vertex -> Int}
    (hcirculation : SixVertexTorusCirculation T horizontal vertical) :
    SixVertexTorusCirculation T (fun v => -horizontal v)
      (fun v => -vertical v) := by
  intro v
  have h := hcirculation v
  change
    -horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) +
        -vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) =
      -horizontal v + -vertical v
  omega

theorem SixVertexTorusCirculation.sub
    {T : EvenTorus} {horizontal₁ vertical₁ horizontal₂ vertical₂ :
      T.Vertex -> Int}
    (hfirst : SixVertexTorusCirculation T horizontal₁ vertical₁)
    (hsecond : SixVertexTorusCirculation T horizontal₂ vertical₂) :
    SixVertexTorusCirculation T
      (fun v => horizontal₁ v - horizontal₂ v)
      (fun v => vertical₁ v - vertical₂ v) :=
  hfirst.add hsecond.neg


def sixVertexHorizontalWindingCirculation
    {T : EvenTorus} (row : Fin T.height) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v => if v.2 = row then coefficient else 0, fun _ => 0)

theorem sixVertexHorizontalWindingCirculation_isCirculation
    {T : EvenTorus} (row : Fin T.height) (coefficient : Int) :
    SixVertexTorusCirculation T
      (sixVertexHorizontalWindingCirculation row coefficient).1
      (sixVertexHorizontalWindingCirculation row coefficient).2 := by
  intro v
  simp [sixVertexHorizontalWindingCirculation]


def sixVertexVerticalWindingCirculation
    {T : EvenTorus} (column : Fin T.width) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun _ => 0, fun v => if v.1 = column then coefficient else 0)

theorem sixVertexVerticalWindingCirculation_isCirculation
    {T : EvenTorus} (column : Fin T.width) (coefficient : Int) :
    SixVertexTorusCirculation T
      (sixVertexVerticalWindingCirculation column coefficient).1
      (sixVertexVerticalWindingCirculation column coefficient).2 := by
  intro v
  simp [sixVertexVerticalWindingCirculation]



def sixVertexPlaquetteBoundaryCirculation
    {T : EvenTorus} (cell : T.Vertex) (coefficient : Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v => coefficient *
      ((if v = cell then 1 else 0) -
        if v = (cell.1, finitePeriodicSucc T.height_pos cell.2)
        then 1 else 0),
   fun v => coefficient *
      ((if v = (finitePeriodicSucc T.width_pos cell.1, cell.2)
        then 1 else 0) - if v = cell then 1 else 0))

theorem sixVertexPlaquetteBoundaryCirculation_isCirculation
    {T : EvenTorus} (cell : T.Vertex) (coefficient : Int) :
    SixVertexTorusCirculation T
      (sixVertexPlaquetteBoundaryCirculation cell coefficient).1
      (sixVertexPlaquetteBoundaryCirculation cell coefficient).2 := by
  intro v
  have hx :
      SixVertexArrows.cyclicPred T.width_pos v.1 = cell.1 ↔
        v.1 = finitePeriodicSucc T.width_pos cell.1 := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.width_pos v.1, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  have hy :
      SixVertexArrows.cyclicPred T.height_pos v.2 = cell.2 ↔
        v.2 = finitePeriodicSucc T.height_pos cell.2 := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.height_pos v.2, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  unfold sixVertexPlaquetteBoundaryCirculation
  by_cases hvx : v.1 = cell.1 <;>
    by_cases hvxSucc :
      v.1 = finitePeriodicSucc T.width_pos cell.1 <;>
    by_cases hvy : v.2 = cell.2 <;>
    by_cases hvySucc :
      v.2 = finitePeriodicSucc T.height_pos cell.2 <;>
    simp_all [Prod.ext_iff]

theorem sixVertexTorusCirculation_sum
    {T : EvenTorus} {Index : Type*} [Fintype Index]
    (horizontal vertical : Index -> T.Vertex -> Int)
    (hcirculation : forall index,
      SixVertexTorusCirculation T (horizontal index) (vertical index)) :
    SixVertexTorusCirculation T
      (fun v => ∑ index, horizontal index v)
      (fun v => ∑ index, vertical index v) := by
  intro v
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hcirculation index v



def sixVertexGeneratedCycleCombination
    (T : EvenTorus)
    (plaquetteWeight : T.Vertex -> Int)
    (horizontalWindingWeight : Fin T.height -> Int)
    (verticalWindingWeight : Fin T.width -> Int) :
    (T.Vertex -> Int) × (T.Vertex -> Int) :=
  (fun v =>
    (∑ cell : T.Vertex,
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).1 v) +
    (∑ row : Fin T.height,
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).1 v) +
    ∑ column : Fin T.width,
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).1 v,
   fun v =>
    (∑ cell : T.Vertex,
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).2 v) +
    (∑ row : Fin T.height,
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).2 v) +
    ∑ column : Fin T.width,
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).2 v)

theorem sixVertexGeneratedCycleCombination_isCirculation
    (T : EvenTorus)
    (plaquetteWeight : T.Vertex -> Int)
    (horizontalWindingWeight : Fin T.height -> Int)
    (verticalWindingWeight : Fin T.width -> Int) :
    SixVertexTorusCirculation T
      (sixVertexGeneratedCycleCombination T plaquetteWeight
        horizontalWindingWeight verticalWindingWeight).1
      (sixVertexGeneratedCycleCombination T plaquetteWeight
        horizontalWindingWeight verticalWindingWeight).2 := by
  let plaquettes := sixVertexTorusCirculation_sum
    (fun cell : T.Vertex =>
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).1)
    (fun cell : T.Vertex =>
      (sixVertexPlaquetteBoundaryCirculation
        cell (plaquetteWeight cell)).2)
    (fun cell =>
      sixVertexPlaquetteBoundaryCirculation_isCirculation
        cell (plaquetteWeight cell))
  let horizontalWindings := sixVertexTorusCirculation_sum
    (fun row : Fin T.height =>
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).1)
    (fun row : Fin T.height =>
      (sixVertexHorizontalWindingCirculation
        row (horizontalWindingWeight row)).2)
    (fun row =>
      sixVertexHorizontalWindingCirculation_isCirculation
        row (horizontalWindingWeight row))
  let verticalWindings := sixVertexTorusCirculation_sum
    (fun column : Fin T.width =>
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).1)
    (fun column : Fin T.width =>
      (sixVertexVerticalWindingCirculation
        column (verticalWindingWeight column)).2)
    (fun column =>
      sixVertexVerticalWindingCirculation_isCirculation
        column (verticalWindingWeight column))
  exact (plaquettes.add horizontalWindings).add verticalWindings

end

end StatMech.FrontierD
