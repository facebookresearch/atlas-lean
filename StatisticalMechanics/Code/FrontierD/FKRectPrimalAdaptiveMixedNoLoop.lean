/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectZeroTurnMixedCandidates
import Code.FrontierD.FKRectPrimalAdaptiveNoLoop





namespace StatMech.FrontierD

noncomputable section




theorem fkRectCritical_zeroTurnAbove_le_half_of_mixedAdaptiveTail
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (hinj : ∀ omega : R.Configuration,
      fkRectZeroTurnCutRemainderCount R omega ≤
        2 * fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R omega) + 2)
    (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 := by
  let K : R.Configuration → Nat := fun eta =>
    2 * fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta) + 2
  have htop : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + K (fkRectForceCutClosed R omega) := by
    intro omega
    apply (fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder
      R omega).trans
    apply Nat.add_le_add_left
    dsimp [K]
    simpa using hinj omega
  have htransfer := fkRectCritical_zeroTurnAbove_cut_transfer
    R hq K htop (2 * n + 2)
  let A : Set R.Configuration :=
    {eta | n < fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta)}
  have hset :
      {eta | FKRectCutClosedConfiguration R eta ∧ 2 * n + 2 < K eta} =
        {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    ext eta
    simp only [Set.mem_setOf_eq, A, K]
    constructor <;> intro h
    · exact ⟨h.1, by omega⟩
    · exact ⟨h.1, by omega⟩
  rw [hset] at htransfer
  have htop' : FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) *
      fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + 2 * n + 2) ≤
    fkRectCriticalEventMass R q
      {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
    simpa only [Nat.add_assoc] using htransfer
  rw [← closedMass_mul_fkRectCriticalCutFreeEventMass R hq A] at htop'
  have hcutNonneg : 0 ≤ fkRectCriticalCutFreeEventMass R q A :=
    fkRectCriticalCutFreeEventMass_nonneg R hq A
  have hmassLe :
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) *
          fkRectCriticalCutFreeEventMass R q A ≤
        fkRectCriticalCutFreeEventMass R q A := by
    nlinarith [fkRectCriticalClosedMass_cut_le_one R hq]
  have hbinom : fkRectCriticalCutFreeEventMass R q A ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
    exact fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
      R hq n
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  have hpow : 0 < FK.cFE (fkRectCriticalP q) q ^
      (2 * R.width + R.height) := pow_pos hc _
  have hfinal := htop'.trans (hmassLe.trans (hbinom.trans hsmall))
  nlinarith


theorem fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (charge : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedAnnulusCharge R omega)
    (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 :=
  fkRectCritical_zeroTurnAbove_le_half_of_mixedAdaptiveTail
    R hq (fun omega =>
      fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge
        R omega (charge omega)) n hsmall


theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (charge : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedAnnulusCharge R omega)
    (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (by linarith : 0 < q))
          (fkRectCriticalP_lt_one (by linarith : 0 < q))
          (by linarith : 0 < q) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * n + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q := by
  apply zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half
    R hq
  exact fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge
    R (by linarith) charge n (by simpa only using hsmall)


theorem fkRectCritical_zeroTurnAbove_le_half_of_mixedTouchedCrossings
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (certificate : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedTouchedCertificate R omega)
    (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    fkRectCriticalZeroTurnAboveMass R q
        (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 :=
  fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge R hq
    (fun omega => (certificate omega).toCharge R omega) n hsmall


theorem zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (certificate : ∀ omega : R.Configuration,
      FKRectZeroTurnMixedTouchedCertificate R omega)
    (n : Nat)
    (hsmall : Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (by linarith : 0 < q))
          (fkRectCriticalP_lt_one (by linarith : 0 < q))
          (by linarith : 0 < q) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤
      FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) / 2) :
    (2 / Real.sqrt q) ^ (2 * R.width + 2 * n + 2) / (2 * q) ≤
      fkRectAllSectorNormalization R q :=
  zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge
    R hq (fun omega => (certificate omega).toCharge R omega) n hsmall

end

end StatMech.FrontierD
