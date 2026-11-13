/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairUnionCirculation












namespace StatMech.FrontierD

noncomputable section


inductive SixVertexDirectedTorusEdge (T : EvenTorus) where
  | horizontal (base : T.Vertex) (positive : Bool)
  | vertical (base : T.Vertex) (positive : Bool)

namespace SixVertexDirectedTorusEdge

def tail {T : EvenTorus} : SixVertexDirectedTorusEdge T -> T.Vertex
  | .horizontal base true => base
  | .horizontal base false =>
      (finitePeriodicSucc T.width_pos base.1, base.2)
  | .vertical base true => base
  | .vertical base false =>
      (base.1, finitePeriodicSucc T.height_pos base.2)

def head {T : EvenTorus} : SixVertexDirectedTorusEdge T -> T.Vertex
  | .horizontal base true =>
      (finitePeriodicSucc T.width_pos base.1, base.2)
  | .horizontal base false => base
  | .vertical base true =>
      (base.1, finitePeriodicSucc T.height_pos base.2)
  | .vertical base false => base

def physical {T : EvenTorus} :
    SixVertexDirectedTorusEdge T -> Bool × T.Vertex
  | .horizontal base _ => (false, base)
  | .vertical base _ => (true, base)

def horizontalFlow {T : EvenTorus}
    (edge : SixVertexDirectedTorusEdge T) (v : T.Vertex) : Int :=
  match edge with
  | .horizontal base positive =>
      if v = base then if positive then 1 else -1 else 0
  | .vertical _ _ => 0

def verticalFlow {T : EvenTorus}
    (edge : SixVertexDirectedTorusEdge T) (v : T.Vertex) : Int :=
  match edge with
  | .horizontal _ _ => 0
  | .vertical base positive =>
      if v = base then if positive then 1 else -1 else 0

end SixVertexDirectedTorusEdge



structure SixVertexDirectedSimpleCycle (T : EvenTorus) where
  length : Nat
  length_pos : 0 < length
  edge : Fin length -> SixVertexDirectedTorusEdge T
  head_eq_next_tail : forall i,
    (edge i).head =
      (edge (finitePeriodicSucc length_pos i)).tail
  tail_injective : Function.Injective (fun i => (edge i).tail)
  physical_injective : Function.Injective (fun i => (edge i).physical)

def SixVertexDirectedSimpleCycle.horizontalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (v : T.Vertex) : Int :=
  ∑ i, (cycle.edge i).horizontalFlow v

def SixVertexDirectedSimpleCycle.verticalFlow
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T)
    (v : T.Vertex) : Int :=
  ∑ i, (cycle.edge i).verticalFlow v


structure SixVertexAtMostTwoCycleFamily (T : EvenTorus) where
  count : Nat
  count_le_two : count <= 2
  cycle : Fin count -> SixVertexDirectedSimpleCycle T
  tail_disjoint : forall i j, i != j -> forall a b,
    ((cycle i).edge a).tail != ((cycle j).edge b).tail

def SixVertexAtMostTwoCycleFamily.horizontalFlow
    {T : EvenTorus} (family : SixVertexAtMostTwoCycleFamily T)
    (v : T.Vertex) : Int :=
  ∑ i, (family.cycle i).horizontalFlow v

def SixVertexAtMostTwoCycleFamily.verticalFlow
    {T : EvenTorus} (family : SixVertexAtMostTwoCycleFamily T)
    (v : T.Vertex) : Int :=
  ∑ i, (family.cycle i).verticalFlow v

def SixVertexAtMostTwoCycleFamily.empty (T : EvenTorus) :
    SixVertexAtMostTwoCycleFamily T where
  count := 0
  count_le_two := by omega
  cycle := fun i => Fin.elim0 i
  tail_disjoint := by
    intro i
    exact Fin.elim0 i



def sixVertexPairAtMostTwoCycleRelated
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) : Prop :=
  exists family : SixVertexAtMostTwoCycleFamily T, exists sign : Bool,
    And
      (sixVertexPairUnionHorizontalDelta source target =
        (fun v => if sign then family.horizontalFlow v
          else -family.horizontalFlow v))
      (sixVertexPairUnionVerticalDelta source target =
        (fun v => if sign then family.verticalFlow v
          else -family.verticalFlow v))


def sixVertexPairAtMostTwoCycleFineRelated
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) : Prop :=
  sixVertexPairAtMostTwoCycleRelated source target /\
    sixVertexHorizontalPairBoundedFineRowProfile
        (source.1.horizontal, source.2.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (target.1.horizontal, target.2.horizontal)

theorem sixVertexPairAtMostTwoCycleRelated_refl
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    sixVertexPairAtMostTwoCycleRelated pair pair := by
  refine ⟨SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  all_goals funext v
  all_goals simp [sixVertexPairUnionHorizontalDelta,
    sixVertexPairUnionVerticalDelta,
    SixVertexAtMostTwoCycleFamily.horizontalFlow,
    SixVertexAtMostTwoCycleFamily.verticalFlow,
    SixVertexAtMostTwoCycleFamily.empty]



theorem sixVertexPairAtMostTwoCycleRelated_of_union_eq
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hhorizontal : sixVertexPairUnionHorizontal source =
      sixVertexPairUnionHorizontal target)
    (hvertical : sixVertexPairUnionVertical source =
      sixVertexPairUnionVertical target) :
    sixVertexPairAtMostTwoCycleRelated source target := by
  refine ⟨SixVertexAtMostTwoCycleFamily.empty T, true, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    simp [sixVertexPairUnionHorizontalDelta,
      SixVertexAtMostTwoCycleFamily.horizontalFlow,
      SixVertexAtMostTwoCycleFamily.empty, h]
  · funext v
    have h := congrFun hvertical v
    simp [sixVertexPairUnionVerticalDelta,
      SixVertexAtMostTwoCycleFamily.verticalFlow,
      SixVertexAtMostTwoCycleFamily.empty, h]

theorem sixVertexPairAtMostTwoCycleFineRelated_refl
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    sixVertexPairAtMostTwoCycleFineRelated pair pair := by
  exact ⟨sixVertexPairAtMostTwoCycleRelated_refl pair, rfl⟩

theorem sixVertexPairAtMostTwoCycleRelated_symm
    {T : EvenTorus} {source target :
      SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
    sixVertexPairAtMostTwoCycleRelated target source := by
  rcases hrelated with ⟨family, sign, hhorizontal, hvertical⟩
  refine ⟨family, !sign, ?_, ?_⟩
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVerticalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega

theorem sixVertexPairAtMostTwoCycleFineRelated_symm
    {T : EvenTorus} {source target :
      SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexPairAtMostTwoCycleFineRelated target source := by
  exact ⟨sixVertexPairAtMostTwoCycleRelated_symm hrelated.1,
    hrelated.2.symm⟩





theorem sixVertexPairAtMostTwoCycleFineRelated_totalC
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
    sixVertexTorusCTypeCount source.1 +
        sixVertexTorusCTypeCount source.2 =
      sixVertexTorusCTypeCount target.1 +
        sixVertexTorusCTypeCount target.2 := by
  have hgrade :
      sixVertexHorizontalPairBigrade
          (source.1.horizontal, source.2.horizontal) =
        sixVertexHorizontalPairBigrade
          (target.1.horizontal, target.2.horizontal) := by
    rw [sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
      sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade,
      hrelated.2]
  have hfirst := congrArg Prod.fst hgrade
  simpa [sixVertexHorizontalPairBigrade,
    sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount] using
      hfirst

end

end StatMech.FrontierD
