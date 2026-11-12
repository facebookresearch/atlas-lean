/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldNormalRotatedSlack









open Filter Topology

namespace StatMech.FK.PeriodicPlanar



theorem tendsto_three_max_one_fixedBranches_subsequence
    (H0 H1 V0 V1 K0 K1 : Nat -> Real)
    (hH : Tendsto (fun n => max (H0 n) (H1 n)) atTop (nhds 1))
    (hV : Tendsto (fun n => max (V0 n) (V1 n)) atTop (nhds 1))
    (hK : Tendsto (fun n => max (K0 n) (K1 n)) atTop (nhds 1)) :
    exists phi : Nat -> Nat, StrictMono phi /\
      exists hBranch vBranch kBranch : Bool,
        Tendsto (fun n => if hBranch then H1 (phi n) else H0 (phi n))
          atTop (nhds 1) /\
        Tendsto (fun n => if vBranch then V1 (phi n) else V0 (phi n))
          atTop (nhds 1) /\
        Tendsto (fun n => if kBranch then K1 (phi n) else K0 (phi n))
          atTop (nhds 1) := by
  obtain hH0 | hH1 :=
    tendsto_max_one_fixedBranch_subsequence H0 H1 hH
  · obtain ⟨phiH, hphiH, _, hHfixed⟩ := hH0
    have hVsub := hV.comp hphiH.tendsto_atTop
    obtain hV0 | hV1 := tendsto_max_one_fixedBranch_subsequence
      (fun n => V0 (phiH n)) (fun n => V1 (phiH n)) hVsub
    · obtain ⟨phiV, hphiV, _, hVfixed⟩ := hV0
      have hKsub := hK.comp (hphiH.comp hphiV).tendsto_atTop
      obtain hK0 | hK1 := tendsto_max_one_fixedBranch_subsequence
        (fun n => K0 (phiH (phiV n)))
        (fun n => K1 (phiH (phiV n))) hKsub
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK0
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), false, false, false, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK1
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), false, false, true, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
    · obtain ⟨phiV, hphiV, _, hVfixed⟩ := hV1
      have hKsub := hK.comp (hphiH.comp hphiV).tendsto_atTop
      obtain hK0 | hK1 := tendsto_max_one_fixedBranch_subsequence
        (fun n => K0 (phiH (phiV n)))
        (fun n => K1 (phiH (phiV n))) hKsub
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK0
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), false, true, false, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK1
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), false, true, true, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
  · obtain ⟨phiH, hphiH, _, hHfixed⟩ := hH1
    have hVsub := hV.comp hphiH.tendsto_atTop
    obtain hV0 | hV1 := tendsto_max_one_fixedBranch_subsequence
      (fun n => V0 (phiH n)) (fun n => V1 (phiH n)) hVsub
    · obtain ⟨phiV, hphiV, _, hVfixed⟩ := hV0
      have hKsub := hK.comp (hphiH.comp hphiV).tendsto_atTop
      obtain hK0 | hK1 := tendsto_max_one_fixedBranch_subsequence
        (fun n => K0 (phiH (phiV n)))
        (fun n => K1 (phiH (phiV n))) hKsub
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK0
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), true, false, false, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK1
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), true, false, true, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
    · obtain ⟨phiV, hphiV, _, hVfixed⟩ := hV1
      have hKsub := hK.comp (hphiH.comp hphiV).tendsto_atTop
      obtain hK0 | hK1 := tendsto_max_one_fixedBranch_subsequence
        (fun n => K0 (phiH (phiV n)))
        (fun n => K1 (phiH (phiV n))) hKsub
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK0
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), true, true, false, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed
      · obtain ⟨phiK, hphiK, _, hKfixed⟩ := hK1
        refine ⟨fun n => phiH (phiV (phiK n)),
          hphiH.comp (hphiV.comp hphiK), true, true, true, ?_, ?_, ?_⟩
        · simpa using hHfixed.comp (hphiV.comp hphiK).tendsto_atTop
        · simpa using hVfixed.comp hphiK.tendsto_atTop
        · simpa using hKfixed



theorem NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    [Countable V] [Countable W]
    {P : PeriodicGraph V} {Pdual : PeriodicGraph W}
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : MeasureTheory.Measure (ConfigSpace (Sym2 V))}
    {muDual : MeasureTheory.Measure (ConfigSpace (Sym2 W))}
    [MeasureTheory.IsProbabilityMeasure muDual]
    (data : NormalTwoRotatedEndpointLimitData E Edual mu muDual) :
    let primalH : Nat -> Real := fun n => mu.real
      (E.horizontalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY)
    let primalV : Nat -> Real := fun n => mu.real
      (E.verticalCrossingEvent
        (data.level n).normal.raw.data.wideLeft
        (data.level n).normal.raw.data.wideRight 0
        (data.level n).normalY)
    let dualVertical0 : Nat -> Real := fun n => muDual.real
      (Edual.verticalCrossingEvent
        0 (data.level n).normalX 0 (data.level n).normalY)
    let dualHorizontal0 : Nat -> Real := fun n => muDual.real
      (Edual.horizontalCrossingEvent 0 (data.level n).normalX
        (data.rotatedVerticalLevel n).raw.data.wideLeft
        (data.rotatedVerticalLevel n).raw.data.wideRight)
    let dualVertical1 : Nat -> Real := fun n => muDual.real
      (Edual.verticalCrossingEvent 0 (data.level n).rotatedHorizontalY
        0 (data.level n).rotatedHorizontalX)
    let dualHorizontal1 : Nat -> Real := fun n => muDual.real
      (Edual.horizontalCrossingEvent 0 (data.level n).rotatedHorizontalY
        (data.rotatedHorizontalLevel n).raw.data.wideLeft
        (data.rotatedHorizontalLevel n).raw.data.wideRight)
    exists phi : Nat -> Nat, StrictMono phi /\
      exists primalBranch dualBranch0 dualBranch1 : Bool,
        Tendsto (fun n => if primalBranch then primalV (phi n)
          else primalH (phi n)) atTop (nhds 1) /\
        Tendsto (fun n => if dualBranch0 then dualHorizontal0 (phi n)
          else dualVertical0 (phi n)) atTop (nhds 1) /\
        Tendsto (fun n => if dualBranch1 then dualHorizontal1 (phi n)
          else dualVertical1 (phi n)) atTop (nhds 1) := by
  dsimp only
  exact tendsto_three_max_one_fixedBranches_subsequence _ _ _ _ _ _
    data.normalLimit data.dualRotatedVerticalOriginalLimit
      data.dualRotatedHorizontalOriginalLimit

end StatMech.FK.PeriodicPlanar
