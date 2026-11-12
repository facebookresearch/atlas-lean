/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCrossingExploration
import Code.FrontierD.FKRectZeroTurnEssential










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def FKRectMedialHitsHorizontalSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) : Prop :=
  ∃ i : Fin R.medialTorus.width,
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus i) = C



theorem fkRectMedialLoopCanonicalVerticalFlux_eq_zero_of_not_hitsHorizontalSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C = 0 := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro hcomponent
  exact havoid ⟨i, hcomponent⟩

noncomputable def fkRectMedialHorizontalSeamComponents
    (R : FKRectTorus) (omega : R.Configuration) :
    Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) := by
  classical
  exact Finset.univ.filter fun C =>
    FKRectMedialHitsHorizontalSeam R omega C

@[simp] theorem mem_fkRectMedialHorizontalSeamComponents
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    C ∈ fkRectMedialHorizontalSeamComponents R omega ↔
      FKRectMedialHitsHorizontalSeam R omega C := by
  classical
  simp [fkRectMedialHorizontalSeamComponents]



theorem fkRectMedialHorizontalSeamComponents_card_le_two_width
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectMedialHorizontalSeamComponents R omega).card ≤
      2 * R.width := by
  classical
  let pairing := fkRectConfigurationToMedialPairing R omega
  let componentAt : Fin R.medialTorus.width →
      FKMedialLoop R.medialTorus pairing := fun i =>
    (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      (fkMedialVerticalSeamDart R.medialTorus i)
  have hsub : fkRectMedialHorizontalSeamComponents R omega ⊆
      (Finset.univ : Finset (Fin R.medialTorus.width)).image componentAt := by
    intro C hC
    rw [Finset.mem_image]
    rw [mem_fkRectMedialHorizontalSeamComponents] at hC
    rcases hC with ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact hi
  calc
    (fkRectMedialHorizontalSeamComponents R omega).card ≤
        ((Finset.univ : Finset (Fin R.medialTorus.width)).image
          componentAt).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin R.medialTorus.width)).card :=
      Finset.card_image_le
    _ = 2 * R.width := by
      rw [Finset.card_univ, Fintype.card_fin]
      rfl


noncomputable def fkRectZeroTurnCutRemainderComponents
    (R : FKRectTorus) (omega : R.Configuration) :
    Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) := by
  classical
  exact Finset.univ.filter fun C =>
    FKMedialTurningFiber.canonicalComponentTurn
          (fkRectConfigurationToMedialPairing R omega) C = 0 ∧
        ¬ FKRectMedialHitsHorizontalSeam R omega C

@[simp] theorem mem_fkRectZeroTurnCutRemainderComponents
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    C ∈ fkRectZeroTurnCutRemainderComponents R omega ↔
      FKMedialTurningFiber.canonicalComponentTurn
          (fkRectConfigurationToMedialPairing R omega) C = 0 ∧
        ¬ FKRectMedialHitsHorizontalSeam R omega C := by
  classical
  simp [fkRectZeroTurnCutRemainderComponents]

def fkRectZeroTurnCutRemainderCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  (fkRectZeroTurnCutRemainderComponents R omega).card



theorem fkRectZeroTurnLoopCount_le_seam_add_cutRemainder
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnLoopCount R omega ≤
      (fkRectMedialHorizontalSeamComponents R omega).card +
        fkRectZeroTurnCutRemainderCount R omega := by
  classical
  let Z := Finset.univ.filter fun C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega) =>
    FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0
  let H := fkRectMedialHorizontalSeamComponents R omega
  let B := fkRectZeroTurnCutRemainderComponents R omega
  have hsub : Z ⊆ H ∪ B := by
    intro C hC
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    by_cases hhit : FKRectMedialHitsHorizontalSeam R omega C
    · exact Finset.mem_union_left B (by
        change C ∈ fkRectMedialHorizontalSeamComponents R omega
        exact (mem_fkRectMedialHorizontalSeamComponents R omega C).2 hhit)
    · exact Finset.mem_union_right H (by
        change C ∈ fkRectZeroTurnCutRemainderComponents R omega
        exact (mem_fkRectZeroTurnCutRemainderComponents R omega C).2
          ⟨hC, hhit⟩)
  change Z.card ≤ H.card + B.card
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le H B)

theorem fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnLoopCount R omega ≤
      2 * R.width + fkRectZeroTurnCutRemainderCount R omega := by
  exact (fkRectZeroTurnLoopCount_le_seam_add_cutRemainder R omega).trans
    (Nat.add_le_add_right
      (fkRectMedialHorizontalSeamComponents_card_le_two_width R omega) _)



theorem fkRectZeroTurnLoopCount_le_two_width_add_primalDualCrossings
    (R : FKRectTorus) (omega : R.Configuration)
    (hinj : fkRectZeroTurnCutRemainderCount R omega ≤
      fkRectRawPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega)) :
    fkRectZeroTurnLoopCount R omega ≤
      2 * R.width +
        fkRectPrimalDualHorizontalCrossingClusterCount R omega :=
  (fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder R omega).trans
    (Nat.add_le_add_left hinj _)




theorem fkRectCritical_zeroTurnAbove_le_primalDualCrossings
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (hinj : ∀ omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega ≤
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) ≤
      fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} := by
  apply fkRectCritical_zeroTurnAbove_cut_transfer R hq
    (fkRectPrimalDualHorizontalCrossingClusterCount R) _ n
  intro omega
  simpa only
      [fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed] using
    (fkRectZeroTurnLoopCount_le_two_width_add_primalDualCrossings
      R omega (hinj omega))



theorem fkRectCritical_zeroTurnAbove_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) (a : Real)
    (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
    (hcover : forall eta : R.Configuration,
      FKRectCutClosedConfiguration R eta ->
        n < fkRectPrimalDualHorizontalCrossingClusterCount R eta ->
        exists S : Finset (Fin (2 * R.height)),
          S.card = n + 1 /\ Witness S eta)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ (n + 1)) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  calc
    _ <= fkRectCriticalEventMass R q
          {eta | FKRectCutClosedConfiguration R eta ∧ n <
            fkRectPrimalDualHorizontalCrossingClusterCount R eta} :=
      fkRectCritical_zeroTurnAbove_le_primalDualCrossings R hq hinj n
    _ <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) :=
      fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow
        R (lt_of_lt_of_le zero_lt_one hq) n a Witness hcover hmass



theorem fkRectCritical_zeroTurnAbove_le_choose_mul_pow_of_sourceMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) (a : Real)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
        a ^ (n + 1)) :
    FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) *
        fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  calc
    _ <= fkRectCriticalEventMass R q
          {eta | FKRectCutClosedConfiguration R eta ∧ n <
            fkRectPrimalDualHorizontalCrossingClusterCount R eta} :=
      fkRectCritical_zeroTurnAbove_le_primalDualCrossings R hq hinj n
    _ <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) :=
      fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass
        R (lt_of_lt_of_le zero_lt_one hq) n a hmass



theorem fkRectCritical_zeroTurnAbove_le_half_of_sourceMass
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) (a : Real)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
        a ^ (n + 1))
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <=
      (1 : Real) / 2 := by
  have htail :=
    fkRectCritical_zeroTurnAbove_le_choose_mul_pow_of_sourceMass
      R hq hinj n a hmass
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  have hpow : 0 <
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) :=
    pow_pos hc _
  nlinarith



theorem fkRectCritical_zeroTurnAbove_le_half_of_step
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <=
      (1 : Real) / 2 := by
  apply fkRectCritical_zeroTurnAbove_le_half_of_sourceMass
    R hq hinj n a
  · intro S hS
    simpa only [hS] using
      fkRectCritical_sourceWitnessMass_le_pow_of_step R
        (lt_of_lt_of_le zero_lt_one hq) ha hstep S
  · exact hsmall



theorem fkRectCritical_zeroTurnAbove_le_half_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <=
      (1 : Real) / 2 := by
  apply fkRectCritical_zeroTurnAbove_le_half_of_step
    R hq hinj n ha
  · intro T i hi
    exact fkRectCritical_sourceWitnessStep_of_cutFreeStep
      R hq a hstep T i hi
  · exact hsmall



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_sourceMass
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) (a : Real)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
        a ^ (n + 1))
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply
    zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
      R hq (2 * R.width + n)
  exact fkRectCritical_zeroTurnAbove_le_half_of_sourceMass R
    (by linarith) hinj n a hmass hsmall



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_step
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply
    zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
      R hq (2 * R.width + n)
  exact fkRectCritical_zeroTurnAbove_le_half_of_step R
    (by linarith) hinj n ha hstep hsmall



theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (hinj : forall omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega <=
        fkRectRawPrimalDualHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega))
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
    (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <=
      FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
    (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <=
      fkRectAllSectorNormalization R q := by
  apply
    zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
      R hq (2 * R.width + n)
  exact fkRectCritical_zeroTurnAbove_le_half_of_cutFreeStep R
    (by linarith) hinj n ha hstep hsmall

end

end StatMech.FrontierD
