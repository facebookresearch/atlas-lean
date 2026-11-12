/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutPushforward
import Code.FrontierD.FKRectRightStripConnection



open Finset

namespace StatMech.FrontierD

noncomputable section


def fkRectPatternOpenEdges (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Finset R.EdgeIndex :=
  I.filter fun a => eta a = true


def fkRectPatternClosedEdges (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Finset R.EdgeIndex :=
  I.filter fun a => eta a = false


def fkRectForceIndexedPattern (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta omega : R.Configuration) : R.Configuration :=
  fkRectForceEdgesOpen R (fkRectPatternOpenEdges R I eta)
    (fkRectForceEdgesClosed R (fkRectPatternClosedEdges R I eta) omega)

@[simp] theorem fkRectForceIndexedPattern_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceIndexedPattern R I eta omega a = eta a := by
  cases h : eta a
  · simp [fkRectForceIndexedPattern, fkRectPatternOpenEdges,
      fkRectPatternClosedEdges, ha, h]
  · simp [fkRectForceIndexedPattern, fkRectPatternOpenEdges,
      fkRectPatternClosedEdges, ha, h]

@[simp] theorem fkRectForceIndexedPattern_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (eta omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceIndexedPattern R I eta omega a = omega a := by
  simp [fkRectForceIndexedPattern, fkRectPatternOpenEdges,
    fkRectPatternClosedEdges, ha]

theorem fkRectPatternOpenEdges_card_add_closedEdges_card
    (R : FKRectTorus) (I : Finset R.EdgeIndex) (eta : R.Configuration) :
    (fkRectPatternOpenEdges R I eta).card +
        (fkRectPatternClosedEdges R I eta).card = I.card := by
  classical
  simpa [fkRectPatternOpenEdges, fkRectPatternClosedEdges] using
    (Finset.card_filter_add_card_filter_not
      (s := I) (fun a => eta a = true))



theorem fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceIndexedPattern R I eta ⁻¹' A) ≤
      fkRectCriticalEventMass R q A := by
  let O := fkRectPatternOpenEdges R I eta
  let C := fkRectPatternClosedEdges R I eta
  let c := FK.cFE (fkRectCriticalP q) q
  have hc : 0 ≤ c := fkRectCritical_cFE_nonneg hq
  have hclosed :=
    fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
      R hq C (fkRectForceEdgesOpen R O ⁻¹' A)
  have hopen :=
    fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event
      R hq O A
  have hmul := mul_le_mul_of_nonneg_left hclosed (pow_nonneg hc O.card)
  have hchain : c ^ O.card *
        (c ^ C.card * fkRectCriticalEventMass R q
          (fkRectForceEdgesClosed R C ⁻¹'
            (fkRectForceEdgesOpen R O ⁻¹' A))) ≤
      fkRectCriticalEventMass R q A := hmul.trans hopen
  have hcard : O.card + C.card = I.card := by
    exact fkRectPatternOpenEdges_card_add_closedEdges_card R I eta
  have hpre : fkRectForceEdgesClosed R C ⁻¹'
        (fkRectForceEdgesOpen R O ⁻¹' A) =
      fkRectForceIndexedPattern R I eta ⁻¹' A := by
    rfl
  rw [← hpre, ← hcard, pow_add]
  simpa only [mul_assoc] using hchain


def FKRectDependsOnOutsideEdges (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (B : Set R.Configuration) : Prop :=
  ∀ omega tau : R.Configuration,
    (∀ a ∉ I, omega a = tau a) → (omega ∈ B ↔ tau ∈ B)



theorem fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (B : Set R.Configuration)
    (hB : FKRectDependsOnOutsideEdges R I B) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q B ≤
      fkRectCriticalEventMass R q
        (fkRectIndexedPatternEvent R I eta ∩ B) := by
  have hpre : fkRectForceIndexedPattern R I eta ⁻¹'
        (fkRectIndexedPatternEvent R I eta ∩ B) = B := by
    ext omega
    constructor
    · intro homega
      have hout : ∀ a ∉ I,
          fkRectForceIndexedPattern R I eta omega a = omega a := by
        intro a ha
        exact fkRectForceIndexedPattern_of_not_mem R eta omega ha
      exact (hB (fkRectForceIndexedPattern R I eta omega) omega hout).1
        homega.2
    · intro homega
      constructor
      · intro a ha
        exact fkRectForceIndexedPattern_of_mem R eta omega ha
      · have hout : ∀ a ∉ I,
            omega a = fkRectForceIndexedPattern R I eta omega a := by
          intro a ha
          exact (fkRectForceIndexedPattern_of_not_mem R eta omega ha).symm
        exact (hB omega (fkRectForceIndexedPattern R I eta omega) hout).1
          homega
  calc
    _ = FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalEventMass R q
          (fkRectForceIndexedPattern R I eta ⁻¹'
            (fkRectIndexedPatternEvent R I eta ∩ B)) := by rw [hpre]
    _ ≤ _ :=
      fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event
        R hq I eta (fkRectIndexedPatternEvent R I eta ∩ B)

end

end StatMech.FrontierD
