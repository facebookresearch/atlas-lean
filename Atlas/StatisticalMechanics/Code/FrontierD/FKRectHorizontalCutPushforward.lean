/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCutPushforward










open Finset

namespace StatMech.FrontierD

noncomputable section


def fkRectForceHorizontalCutClosed (R : FKRectTorus)
    (omega : R.Configuration) : R.Configuration :=
  fkRectForceEdgesClosed R (fkRectHorizontalCutEdges R) omega


def FKRectHorizontalCutClosedConfiguration
    (R : FKRectTorus) (eta : R.Configuration) : Prop :=
  ∀ a ∈ fkRectHorizontalCutEdges R, eta a = false

@[simp] theorem fkRectHorizontalCutClosedConfiguration_force
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHorizontalCutClosedConfiguration R
      (fkRectForceHorizontalCutClosed R omega) := by
  intro a ha
  simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, ha]

theorem fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta} =
      fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
  classical
  unfold fkRectCriticalEventMass fkRectCriticalClosedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta _
  by_cases hclosed : FKRectHorizontalCutClosedConfiguration R eta
  · rw [Set.indicator_of_mem hclosed,
      if_pos (show ∀ a ∈ fkRectHorizontalCutEdges R, eta a = false from
        hclosed)]
  · rw [Set.indicator_of_notMem hclosed,
      if_neg (show ¬∀ a ∈ fkRectHorizontalCutEdges R, eta a = false from
        hclosed)]

theorem fkRectCriticalClosedMass_horizontalCut_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
  have hlower := fkRectCritical_cFE_pow_le_closedMass
    R hq (fkRectHorizontalCutEdges R)
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  exact (pow_pos hc _).trans_le hlower

theorem fkRectCriticalClosedMass_horizontalCut_le_one
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) <= 1 := by
  rw [← fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass]
  calc
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta} <=
      fkRectCriticalEventMass R q Set.univ :=
        fkRectCriticalEventMass_mono R
          (lt_of_lt_of_le zero_lt_one hq) (Set.subset_univ _)
    _ = 1 := by
      unfold fkRectCriticalEventMass
      simpa using sum_fkRectCriticalRandomClusterProb R
        (lt_of_lt_of_le zero_lt_one hq)


def fkRectCriticalHorizontalCutEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  fkRectCriticalEventMass R q
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} /
    fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R)

theorem fkRectCriticalHorizontalCutEventMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    0 <= fkRectCriticalHorizontalCutEventMass R q A := by
  unfold fkRectCriticalHorizontalCutEventMass
  exact div_nonneg
    (fkRectCriticalEventMass_nonneg R
      (lt_of_lt_of_le zero_lt_one hq) _)
    (fkRectCriticalClosedMass_horizontalCut_pos R hq).le

theorem closedMass_mul_fkRectCriticalHorizontalCutEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) *
        fkRectCriticalHorizontalCutEventMass R q A =
      fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := by
  unfold fkRectCriticalHorizontalCutEventMass
  field_simp [ne_of_gt (fkRectCriticalClosedMass_horizontalCut_pos R hq)]



theorem fkRectCritical_horizontalCutPushforward_event
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q
          (fkRectForceHorizontalCutClosed R ⁻¹' A) <=
      fkRectCriticalEventMass R q A := by
  simpa only [fkRectForceHorizontalCutClosed,
    fkRectHorizontalCutEdges_card] using
      fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event
        R hq (fkRectHorizontalCutEdges R) A




theorem fkRectCritical_eventMass_le_horizontalCutEventMass_of_force
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (Source Target : Set R.Configuration)
    (hforce : ∀ omega, omega ∈ Source ->
      fkRectForceHorizontalCutClosed R omega ∈ Target) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q Source <=
      fkRectCriticalHorizontalCutEventMass R q Target := by
  let ClosedTarget : Set R.Configuration :=
    {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ Target}
  have hsubset : Source ⊆
      fkRectForceHorizontalCutClosed R ⁻¹' ClosedTarget := by
    intro omega homega
    exact ⟨fkRectHorizontalCutClosedConfiguration_force R omega,
      hforce omega homega⟩
  have hpush := fkRectCritical_horizontalCutPushforward_event
    R hq ClosedTarget
  have hmono := fkRectCriticalEventMass_mono R
    (lt_of_lt_of_le zero_lt_one hq) hsubset
  have hnonneg : 0 <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) :=
    pow_nonneg (fkRectCritical_cFE_nonneg hq) _
  have hclosed :
      fkRectCriticalEventMass R q ClosedTarget =
        fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) *
          fkRectCriticalHorizontalCutEventMass R q Target := by
    symm
    exact closedMass_mul_fkRectCriticalHorizontalCutEventMass R hq Target
  calc
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q Source <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) *
        fkRectCriticalEventMass R q
          (fkRectForceHorizontalCutClosed R ⁻¹' ClosedTarget) :=
        mul_le_mul_of_nonneg_left hmono hnonneg
    _ <= fkRectCriticalEventMass R q ClosedTarget := hpush
    _ = fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) *
        fkRectCriticalHorizontalCutEventMass R q Target := hclosed
    _ <= fkRectCriticalHorizontalCutEventMass R q Target := by
      have htarget := fkRectCriticalHorizontalCutEventMass_nonneg
        R hq Target
      nlinarith [fkRectCriticalClosedMass_horizontalCut_le_one R hq]

end

end StatMech.FrontierD
