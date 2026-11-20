/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRightStripConnection
import Code.FrontierD.FKRectTorusCrossingEvents



namespace StatMech.FrontierD

noncomputable section

theorem FKRectDependsOnOutsideRegion.inter
    (R : FKRectTorus) (S : Set R.Vertex)
    {A B : Set R.Configuration}
    (hA : FKRectDependsOnOutsideRegion R S A)
    (hB : FKRectDependsOnOutsideRegion R S B) :
    FKRectDependsOnOutsideRegion R S (A ∩ B) := by
  intro omega tau hot
  exact and_congr (hA omega tau hot) (hB omega tau hot)

theorem FKRectDependsOnOutsideRegion.compl
    (R : FKRectTorus) (S : Set R.Vertex)
    {A : Set R.Configuration}
    (hA : FKRectDependsOnOutsideRegion R S A) :
    FKRectDependsOnOutsideRegion R S Aᶜ := by
  intro omega tau hot
  exact not_congr (hA omega tau hot)



def fkRectSetConnectionWithinEvent (R : FKRectTorus)
    (T X Y : Set R.Vertex) : Set R.Configuration :=
  {omega | ∃ x : T, x.1 ∈ X ∧ ∃ y : T, y.1 ∈ Y ∧
    FKRectConnectedWithin R omega T x y}



theorem fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint
    (R : FKRectTorus) (S T : Set R.Vertex)
    (hdisj : ∀ v, v ∈ T → v ∉ S)
    (omega tau : R.Configuration)
    (hot : ∀ a : R.EdgeIndex,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)) →
      omega a = tau a) :
    (fkRectOpenGraph R omega).induce T =
      (fkRectOpenGraph R tau).induce T := by
  ext x y
  constructor
  · rintro ⟨a, hopen, ha⟩
    refine ⟨a, ?_, ha⟩
    rw [← hot a]
    · exact hopen
    · intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff
        R S x.1 y.1).1 (by simpa only [ha] using hrange)
      exact hdisj x.1 x.2 hxy.1
  · rintro ⟨a, hopen, ha⟩
    refine ⟨a, ?_, ha⟩
    rw [hot a]
    · exact hopen
    · intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff
        R S x.1 y.1).1 (by simpa only [ha] using hrange)
      exact hdisj x.1 x.2 hxy.1

theorem fkRectSetConnectionWithinEvent_dependsOnOutsideRegion
    (R : FKRectTorus) (S T X Y : Set R.Vertex)
    (hdisj : ∀ v, v ∈ T → v ∉ S) :
    FKRectDependsOnOutsideRegion R S
      (fkRectSetConnectionWithinEvent R T X Y) := by
  intro omega tau hot
  have hgraph := fkRect_inducedOpenGraph_eq_of_agreesOutside_disjoint
    R S T hdisj omega tau hot
  constructor
  · rintro ⟨x, hx, y, hy, hreach⟩
    exact ⟨x, hx, y, hy, by
      unfold FKRectConnectedWithin at hreach ⊢
      rwa [← hgraph]⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    exact ⟨x, hx, y, hy, by
      unfold FKRectConnectedWithin at hreach ⊢
      rwa [hgraph]⟩


def fkRectLeftStrip (R : FKRectTorus) (right : Nat) : Set R.Vertex :=
  {v | v.1.val ≤ right}

def fkRectColumnSet (R : FKRectTorus) (column : Nat) : Set R.Vertex :=
  {v | v.1.val = column}


def fkRectNoLeftStripCrossingEvent (R : FKRectTorus)
    (right : Nat) : Set R.Configuration :=
  (fkRectSetConnectionWithinEvent R
    (fkRectLeftStrip R right)
    (fkRectColumnSet R 0)
    (fkRectColumnSet R right))ᶜ

theorem fkRectSetConnectionWithinEvent_isIncreasing
    (R : FKRectTorus) (T X Y : Set R.Vertex) :
    IsIncreasing (fkRectSetConnectionWithinEvent R T X Y) := by
  intro omega tau hot
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, hxy.mono_configuration R hot T⟩

theorem fkRectNoLeftStripCrossingEvent_isDecreasing
    (R : FKRectTorus) (right : Nat) :
    IsDecreasing (fkRectNoLeftStripCrossingEvent R right) := by
  exact (fkRectSetConnectionWithinEvent_isIncreasing R
    (fkRectLeftStrip R right) (fkRectColumnSet R 0)
    (fkRectColumnSet R right)).compl

theorem fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectNoLeftStripCrossingEvent R leftRight) := by
  apply FKRectDependsOnOutsideRegion.compl
  apply fkRectSetConnectionWithinEvent_dependsOnOutsideRegion
  intro v hvT hvS
  exact (not_lt_of_ge (hvS.1.trans hvT)) hsep



def fkRectLeftBarrierWithSeamPattern (R : FKRectTorus)
    (leftRight : Nat) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectIndexedPatternEvent R I eta

theorem fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    (I : Finset R.EdgeIndex)
    (hI : ∀ a ∈ I,
      fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a))
    (eta : R.Configuration) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectLeftBarrierWithSeamPattern R leftRight I eta) := by
  apply FKRectDependsOnOutsideRegion.inter
  · exact fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand
      R leftRight cut lower upper hsep
  · exact fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand
      R cut lower upper hlower I hI eta

end

end StatMech.FrontierD
