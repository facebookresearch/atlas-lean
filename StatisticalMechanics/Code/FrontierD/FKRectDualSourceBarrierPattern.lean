/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDualSourceBarrierRate
import Code.FrontierD.FKRectIndexedPatternPushforward



namespace StatMech.FrontierD

noncomputable section


def fkRectDualPullbackIndexSet (R : FKRectTorus)
    (I : Finset R.EdgeIndex) : Finset R.EdgeIndex :=
  I.image (fkRectDualEdgeToEdge R)


def fkRectDualPullbackConfiguration (R : FKRectTorus)
    (eta : R.Configuration) : R.Configuration :=
  fun e => !(eta (fkRectEdgeToDualEdge R e))

theorem fkRectDualPullbackIndexSet_card
    (R : FKRectTorus) (I : Finset R.EdgeIndex) :
    (fkRectDualPullbackIndexSet R I).card = I.card := by
  unfold fkRectDualPullbackIndexSet
  rw [Finset.card_image_of_injective]
  exact (fkRectEdgeDualEquiv R).symm.injective



theorem fkRectDualPreimage_indexedPatternEvent_eq
    (R : FKRectTorus) (I : Finset R.EdgeIndex) (eta : R.Configuration) :
    fkRectDualPreimageEvent R (fkRectIndexedPatternEvent R I eta) =
      fkRectIndexedPatternEvent R (fkRectDualPullbackIndexSet R I)
        (fkRectDualPullbackConfiguration R eta) := by
  ext omega
  constructor
  · intro homega e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have h := homega d hd
    rw [fkRectDualConfigurationEquiv_apply] at h
    simpa [fkRectDualPullbackConfiguration] using
      congrArg (fun b : Bool => !b) h
  · intro homega d hd
    have he : fkRectDualEdgeToEdge R d ∈
        fkRectDualPullbackIndexSet R I :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h := homega (fkRectDualEdgeToEdge R d) he
    rw [fkRectDualConfigurationEquiv_apply]
    simpa [fkRectDualPullbackConfiguration] using
      congrArg (fun b : Bool => !b) h

theorem fkRectDualPullbackHorizontalCutEdges_card (R : FKRectTorus) :
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)).card =
      2 * R.width := by
  rw [fkRectDualPullbackIndexSet_card,
    fkRectHorizontalCutEdges_card]

theorem fkRectDualPullbackIndexSet_horizontalCutEdges (R : FKRectTorus) :
    fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R) =
      fkRectHorizontalCutEdges R := by
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    rw [mem_fkRectHorizontalCutEdges_iff] at hd ⊢
    rcases d with ⟨b, x, y⟩
    cases b <;> simpa [fkRectDualEdgeToEdge] using hd
  · intro he
    refine Finset.mem_image.mpr
      ⟨fkRectEdgeToDualEdge R e, ?_, by simp⟩
    rw [mem_fkRectHorizontalCutEdges_iff] at he ⊢
    rcases e with ⟨b, x, y⟩
    cases b <;> simpa [fkRectEdgeToDualEdge] using he

theorem fkRectDualPreimage_noLeftStripCrossing_isIncreasing
    (R : FKRectTorus) (leftRight : Nat) :
    IsIncreasing (fkRectDualPreimageEvent R
      (fkRectNoLeftStripCrossingEvent R leftRight)) :=
  fkRectDualPreimageEvent_isIncreasing R
    (fkRectNoLeftStripCrossingEvent_isDecreasing R leftRight)



theorem fkRectDualPullbackSourceLeftBarrier_eq
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex) :
    fkRectDualPullbackSourceLeftBarrier R leftRight gap =
      fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R leftRight) ∩
        fkRectIndexedPatternEvent R
          (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
          (fkRectDualPullbackConfiguration R
            (fkRectAllButOneOpenConfiguration R gap)) := by
  rw [fkRectDualPullbackSourceLeftBarrier,
    fkRectSourceLeftBarrier, fkRectDualPreimageEvent]
  rw [Set.preimage_inter]
  congr 1
  exact fkRectDualPreimage_indexedPatternEvent_eq R _ _




theorem fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource
    (R : FKRectTorus) (leftRight : Nat) {q : Real} (hq : 1 <= q)
    (gap : R.EdgeIndex) (A : Set R.Configuration)
    (hforce : ∀ omega ∈ A,
      fkRectForceIndexedPattern R
          (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
          (fkRectDualPullbackConfiguration R
            (fkRectAllButOneOpenConfiguration R gap)) omega ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R leftRight)) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q A <=
      fkRectCriticalEventMass R q
        (fkRectDualPullbackSourceLeftBarrier R leftRight gap) := by
  let I := fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R gap)
  let target := fkRectDualPullbackSourceLeftBarrier R leftRight gap
  have hsubset : A ⊆ fkRectForceIndexedPattern R I eta ⁻¹' target := by
    intro omega homega
    change fkRectForceIndexedPattern R I eta omega ∈ target
    dsimp only [target]
    rw [fkRectDualPullbackSourceLeftBarrier_eq]
    constructor
    · exact hforce omega homega
    · intro edge hedge
      exact fkRectForceIndexedPattern_of_mem R eta omega hedge
  have hmono := fkRectCriticalEventMass_mono R
    (zero_lt_one.trans_le hq) hsubset
  have hc : 0 <= FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  have hmul := mul_le_mul_of_nonneg_left hmono
    (pow_nonneg hc (2 * R.width))
  have hpattern :=
    fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
      R hq I eta target
  rw [fkRectDualPullbackHorizontalCutEdges_card] at hpattern
  exact hmul.trans hpattern

end

end StatMech.FrontierD
