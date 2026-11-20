/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBarrierConnectionProduct
import Code.FrontierD.FKRectCutSquareEmbedding
import Code.FrontierD.FKRectTorusNetFull



namespace StatMech.FrontierD

noncomputable section



def fkRectAllButOneOpenConfiguration (R : FKRectTorus)
    (gap : R.EdgeIndex) : R.Configuration :=
  fun a => decide (a ≠ gap)



theorem fkRectHorizontalCutEdge_crossesVerticalSeam
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩


def fkRectAllButOneOpenSeamEvent (R : FKRectTorus)
    (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectIndexedPatternEvent R (fkRectHorizontalCutEdges R)
    (fkRectAllButOneOpenConfiguration R gap)

theorem mem_fkRectAllButOneOpenSeamEvent_iff
    (R : FKRectTorus) (gap : R.EdgeIndex) (omega : R.Configuration) :
    omega ∈ fkRectAllButOneOpenSeamEvent R gap ↔
      ∀ a ∈ fkRectHorizontalCutEdges R, omega a = decide (a ≠ gap) :=
  Iff.rfl

theorem fkRectAllButOneOpenSeamEvent_open_iff
    (R : FKRectTorus) {gap : R.EdgeIndex} {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
    {a : R.EdgeIndex} (ha : a ∈ fkRectHorizontalCutEdges R) :
    omega a = true ↔ a ≠ gap := by
  rw [homega a ha]
  simp [fkRectAllButOneOpenConfiguration]

theorem fkRectAllButOneOpenSeamEvent_gap_closed
    (R : FKRectTorus) {gap : R.EdgeIndex}
    (hgap : gap ∈ fkRectHorizontalCutEdges R)
    {omega : R.Configuration}
    (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
    omega gap = false := by
  rw [homega gap hgap]
  simp [fkRectAllButOneOpenConfiguration]


def fkRectSourceLeftBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectAllButOneOpenSeamEvent R gap

theorem fkRectSourceLeftBarrier_eq_generic
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex) :
    fkRectSourceLeftBarrier R leftRight gap =
      fkRectLeftBarrierWithSeamPattern R leftRight
        (fkRectHorizontalCutEdges R)
        (fkRectAllButOneOpenConfiguration R gap) :=
  rfl

theorem fkRectSourceLeftBarrier_dependsOnOutsideRightStripBand
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    (gap : R.EdgeIndex) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectSourceLeftBarrier R leftRight gap) := by
  exact fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand
    R leftRight cut lower upper hsep hlower
      (fkRectHorizontalCutEdges R)
      (fkRectHorizontalCutEdge_crossesVerticalSeam R)
      (fkRectAllButOneOpenConfiguration R gap)



def fkRectSourceBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (gap : R.EdgeIndex)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  fkRectRightBandBarrierConnectionEvent R leftRight cut lower upper
    (fkRectHorizontalCutEdges R)
    (fkRectAllButOneOpenConfiguration R gap) t



theorem fkRectSource_barrierConnectionProduct_le
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    {q : Real} (hq : 1 ≤ q)
    (gap : R.EdgeIndex)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      ∑ rho,
        (fkRectSourceBarrierConnectionEvent R
          leftRight cut lower upper gap t).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  exact fkRectRightBand_barrierConnectionProduct_le R
    leftRight cut lower upper hsep hlower hq
    (fkRectHorizontalCutEdges R)
    (fkRectHorizontalCutEdge_crossesVerticalSeam R)
    (fkRectAllButOneOpenConfiguration R gap) t

end

end StatMech.FrontierD
