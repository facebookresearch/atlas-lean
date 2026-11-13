/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectAugmentedSourceBarrier
import Code.FrontierD.FKRectIndexedPatternPushforward



namespace StatMech.FrontierD

noncomputable section



theorem fkRectNoLeftStripCrossing_dependsOnOutside_attachment
    (R : FKRectTorus) (leftRight : Nat) (x : Fin R.width)
    (hx : leftRight < x.val) :
    FKRectDependsOnOutsideEdges R {fkRectRowZeroAttachmentEdgeAt R x}
      (fkRectNoLeftStripCrossingEvent R leftRight) := by
  let S : Set R.Vertex :=
    {v | v = fkRectRowZeroVertex R x ∨ v = fkRectRowOneVertex R x}
  have hregion : FKRectDependsOnOutsideRegion R S
      (fkRectNoLeftStripCrossingEvent R leftRight) := by
    apply FKRectDependsOnOutsideRegion.compl
    apply fkRectSetConnectionWithinEvent_dependsOnOutsideRegion
    intro v hv hS
    rcases hS with hzero | hone
    · have hcol := congrArg (fun z : R.Vertex => z.1.val) hzero
      exact (not_lt_of_ge hv) (by simpa using hx.trans_eq hcol.symm)
    · have hcol := congrArg (fun z : R.Vertex => z.1.val) hone
      exact (not_lt_of_ge hv) (by simpa using hx.trans_eq hcol.symm)
  intro omega tau hagree
  apply hregion omega tau
  intro a ha
  apply hagree a
  simp only [Finset.mem_singleton]
  intro haeq
  subst a
  apply ha
  let u : FKRectInducedVertex R S :=
    ⟨fkRectRowOneVertex R x, Or.inr rfl⟩
  let v : FKRectInducedVertex R S :=
    ⟨fkRectRowZeroVertex R x, Or.inl rfl⟩
  refine ⟨s(u, v), ?_⟩
  rw [FK.ocd_innerEdge_mk]
  exact (fkRectRowZeroAttachmentEdgeAt_indexedEdge R x).symm


theorem fkRectSourceLeftBarrier_dependsOnOutside_attachment
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex)
    (x : Fin R.width) (hx : leftRight < x.val) :
    FKRectDependsOnOutsideEdges R {fkRectRowZeroAttachmentEdgeAt R x}
      (fkRectSourceLeftBarrier R leftRight gap) := by
  intro omega tau hagree
  constructor
  · rintro ⟨hcross, hseam⟩
    constructor
    · exact (fkRectNoLeftStripCrossing_dependsOnOutside_attachment
        R leftRight x hx omega tau hagree).1 hcross
    · intro a ha
      have hne : a ∉ ({fkRectRowZeroAttachmentEdgeAt R x} :
          Finset R.EdgeIndex) := by
        simp only [Finset.mem_singleton]
        intro haeq
        subst a
        exact (fkRectRowZeroAttachmentEdgeAt_not_crosses R x)
          (fkRectHorizontalCutEdge_crossesVerticalSeam R _ ha)
      exact (hagree a hne).symm.trans (hseam a ha)
  · rintro ⟨hcross, hseam⟩
    constructor
    · exact (fkRectNoLeftStripCrossing_dependsOnOutside_attachment
        R leftRight x hx omega tau hagree).2 hcross
    · intro a ha
      have hne : a ∉ ({fkRectRowZeroAttachmentEdgeAt R x} :
          Finset R.EdgeIndex) := by
        simp only [Finset.mem_singleton]
        intro haeq
        subst a
        exact (fkRectRowZeroAttachmentEdgeAt_not_crosses R x)
          (fkRectHorizontalCutEdge_crossesVerticalSeam R _ ha)
      exact (hagree a hne).trans (hseam a ha)

theorem fkRectAugmentedSourceBarrier_eq_attachment_inter_source
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex)
    (x : Fin R.width) :
    fkRectAugmentedSourceBarrier R leftRight gap x =
      fkRectIndexedPatternEvent R {fkRectRowZeroAttachmentEdgeAt R x}
          (fkRectAllButOneOpenConfiguration R gap) ∩
        fkRectSourceLeftBarrier R leftRight gap := by
  ext omega
  simp only [fkRectAugmentedSourceBarrier,
    fkRectAugmentedSourcePatternEdges, fkRectLeftBarrierWithSeamPattern,
    fkRectSourceLeftBarrier, fkRectAllButOneOpenSeamEvent,
    fkRectIndexedPatternEvent, Set.mem_inter_iff, Finset.mem_union,
    Finset.mem_singleton]
  aesop



theorem fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex)
    (x : Fin R.width) (hx : leftRight < x.val)
    {q : Real} (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      fkRectCriticalEventMass R q
        (fkRectAugmentedSourceBarrier R leftRight gap x) := by
  have h := fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter
    R hq {fkRectRowZeroAttachmentEdgeAt R x}
      (fkRectAllButOneOpenConfiguration R gap)
      (fkRectSourceLeftBarrier R leftRight gap)
      (fkRectSourceLeftBarrier_dependsOnOutside_attachment
        R leftRight gap x hx)
  rw [Finset.card_singleton, pow_one,
    ← fkRectAugmentedSourceBarrier_eq_attachment_inter_source] at h
  exact h

end

end StatMech.FrontierD
