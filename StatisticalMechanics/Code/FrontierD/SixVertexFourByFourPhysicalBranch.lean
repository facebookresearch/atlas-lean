/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexFourByFourGradeCount
import Code.FrontierD.SixVertexConfigurationPhysicalParticleHole

open Finset

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexVerticalRowsTotalC_le
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width) :
    sixVertexVerticalRowsTotalC vertical ≤ T.height * T.width := by
  unfold sixVertexVerticalRowsTotalC
  calc
    _ ≤ ∑ _j : Fin T.height, T.width := by
      apply Finset.sum_le_sum
      intro j _
      exact sixVertexRowDistance_le_width _ _
    _ = _ := by simp [mul_comm]

theorem sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat)
    (hlarge : T.height * T.width < totalC) :
    sixVertexMarkedSectorRowCycleGradeCount T sector totalC = 0 := by
  unfold sixVertexMarkedSectorRowCycleGradeCount
  apply Finset.sum_eq_zero
  intro vertical _
  rw [if_neg]
  intro heq
  have hle := sixVertexVerticalRowsTotalC_le vertical.1
  omega

def sixVertexFourByFourGradeCountNat
    (sector : Fin 5) (totalC : Nat) : Nat :=
  if htotal : totalC < 17 then
    sixVertexFourByFourGradeCountTable sector ⟨totalC, htotal⟩
  else 0

theorem sixVertexFourByFourRowCycleGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCount
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourGradeCountNat sector totalC := by
  by_cases htotal : totalC < 17
  · rw [sixVertexFourByFourGradeCountNat, dif_pos htotal]
    exact sixVertexFourByFourRowCycleGradeCount_certificate
      sector ⟨totalC, htotal⟩
  · rw [sixVertexFourByFourGradeCountNat, dif_neg htotal]
    apply sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt
    norm_num [sixVertexFourByFourTorus]
    omega

def sixVertexFourByFourPairGradeCountNat
    (left right : Fin 5) (totalC : Nat) : Nat :=
  ∑ grade : Fin (totalC + 1),
    sixVertexFourByFourGradeCountNat left grade.val *
      sixVertexFourByFourGradeCountNat right (totalC - grade.val)

theorem sixVertexFourByFourRowCyclePairGradeCount_eq_nat
    (left right : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCyclePairGradeCount
        sixVertexFourByFourTorus left right totalC =
      sixVertexFourByFourPairGradeCountNat left right totalC := by
  rw [sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution]
  unfold sixVertexFourByFourPairGradeCountNat
  apply Finset.sum_congr rfl
  intro grade _
  rw [sixVertexFourByFourRowCycleGradeCount_eq_nat,
    sixVertexFourByFourRowCycleGradeCount_eq_nat]

theorem sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleDiagonalGradeCount T sector totalC =
      if totalC % 2 = 0 then
        sixVertexMarkedSectorRowCycleGradeCount T sector (totalC / 2)
      else 0 := by
  unfold sixVertexMarkedSectorRowCycleDiagonalGradeCount
    sixVertexMarkedSectorRowCycleGradeCount
  by_cases heven : totalC % 2 = 0
  · rw [if_pos heven]
    apply Finset.sum_congr rfl
    intro vertical _
    apply if_congr
    · constructor <;> intro h <;> omega
    · rfl
    · rfl
  · rw [if_neg heven]
    apply Finset.sum_eq_zero
    intro vertical _
    rw [if_neg]
    intro hgrade
    have : totalC % 2 = 0 := by omega
    exact heven this

def sixVertexFourByFourDiagonalGradeCountNat
    (sector : Fin 5) (totalC : Nat) : Nat :=
  if totalC % 2 = 0 then
    sixVertexFourByFourGradeCountNat sector (totalC / 2)
  else 0

theorem sixVertexFourByFourDiagonalGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleDiagonalGradeCount
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourDiagonalGradeCountNat sector totalC := by
  rw [sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat]
  unfold sixVertexFourByFourDiagonalGradeCountNat
  split
  · rw [sixVertexFourByFourRowCycleGradeCount_eq_nat]
  · rfl

def sixVertexFourByFourOffDiagonalGradeCountNat
    (sector : Fin 5) (totalC : Nat) : Nat :=
  sixVertexFourByFourPairGradeCountNat sector sector totalC -
    sixVertexFourByFourDiagonalGradeCountNat sector totalC

theorem sixVertexFourByFourOffDiagonalGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    Nat.card
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget
            sixVertexFourByFourTorus sector //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
      sixVertexFourByFourOffDiagonalGradeCountNat sector totalC := by
  have hcard :
      Nat.card
          {target : SixVertexPhysicalRowCycleOffDiagonalTarget
              sixVertexFourByFourTorus sector //
            sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
        sixVertexMarkedSectorRowCyclePairGradeCount
            sixVertexFourByFourTorus sector sector totalC -
          sixVertexMarkedSectorRowCycleDiagonalGradeCount
            sixVertexFourByFourTorus sector totalC := by
    simpa only [← Nat.card_eq_fintype_card] using
      card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber
        sixVertexFourByFourTorus sector totalC
  rw [hcard]
  unfold sixVertexFourByFourOffDiagonalGradeCountNat
  rw [sixVertexFourByFourRowCyclePairGradeCount_eq_nat,
    sixVertexFourByFourDiagonalGradeCount_eq_nat]

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFour_middleOne_gradeCapacity_certificate :
    ∀ totalC : Fin 33,
      sixVertexFourByFourPairGradeCountNat 0 2 totalC.val ≤
        sixVertexFourByFourOffDiagonalGradeCountNat 1 totalC.val := by
  decide +revert

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFour_middleTwo_gradeCapacity_certificate :
    ∀ totalC : Fin 33,
      sixVertexFourByFourPairGradeCountNat 1 3 totalC.val ≤
        sixVertexFourByFourOffDiagonalGradeCountNat 2 totalC.val := by
  decide +revert

theorem sixVertexFourByFourSectorOne_pos :
    0 < sixVertexFourByFourSectorOne.val := by
  norm_num [sixVertexFourByFourSectorOne]

theorem sixVertexFourByFourSectorOne_lt_width :
    sixVertexFourByFourSectorOne.val < sixVertexFourByFourTorus.width := by
  norm_num [sixVertexFourByFourSectorOne, sixVertexFourByFourTorus]

theorem sixVertexFourByFourSectorTwo_pos :
    0 < sixVertexFourByFourSectorTwo.val := by
  norm_num [sixVertexFourByFourSectorTwo]

theorem sixVertexFourByFourSectorTwo_lt_width :
    sixVertexFourByFourSectorTwo.val < sixVertexFourByFourTorus.width := by
  norm_num [sixVertexFourByFourSectorTwo, sixVertexFourByFourTorus]

theorem sixVertexFourByFourPhysicalSourceGradeCount_middleOne
    (totalC : Nat) :
    Nat.card
        {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
            sixVertexFourByFourSectorOne
            sixVertexFourByFourSectorOne_pos
            sixVertexFourByFourSectorOne_lt_width //
          sixVertexPhysicalRowCyclePairTotalC source = totalC} =
      sixVertexFourByFourPairGradeCountNat 0 2 totalC := by
  change Nat.card
      {source : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 0 ×
          SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 2 //
        sixVertexMarkedSectorRowCyclePairTotalC source = totalC} = _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCyclePairGradeFiber,
    sixVertexFourByFourRowCyclePairGradeCount_eq_nat]
  rfl

theorem sixVertexFourByFourPhysicalSourceGradeCount_middleTwo
    (totalC : Nat) :
    Nat.card
        {source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
            sixVertexFourByFourSectorTwo
            sixVertexFourByFourSectorTwo_pos
            sixVertexFourByFourSectorTwo_lt_width //
          sixVertexPhysicalRowCyclePairTotalC source = totalC} =
      sixVertexFourByFourPairGradeCountNat 1 3 totalC := by
  change Nat.card
      {source : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 1 ×
          SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus 3 //
        sixVertexMarkedSectorRowCyclePairTotalC source = totalC} = _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCyclePairGradeFiber,
    sixVertexFourByFourRowCyclePairGradeCount_eq_nat]
  rfl

theorem sixVertexFourByFourRowCycleTotalC_le
    {sector : Fin 5}
    (rows : SixVertexMarkedSectorRowCycle sixVertexFourByFourTorus sector) :
    sixVertexMarkedSectorRowCycleTotalC rows ≤ 16 := by
  change sixVertexVerticalRowsTotalC rows.1.2 ≤ 16
  simpa [sixVertexFourByFourTorus] using
    sixVertexVerticalRowsTotalC_le rows.1.2

theorem sixVertexFourByFourPhysicalSourceTotalC_le
    {middle : Fin 5} {hmiddle_pos : 0 < middle.val}
    {hmiddle_lt : middle.val < sixVertexFourByFourTorus.width}
    (source : SixVertexPhysicalRowCycleSource sixVertexFourByFourTorus
      middle hmiddle_pos hmiddle_lt) :
    sixVertexPhysicalRowCyclePairTotalC source ≤ 32 := by
  change sixVertexMarkedSectorRowCycleTotalC source.1 +
    sixVertexMarkedSectorRowCycleTotalC source.2 ≤ 32
  have hleft := sixVertexFourByFourRowCycleTotalC_le source.1
  have hright := sixVertexFourByFourRowCycleTotalC_le source.2
  omega

theorem sixVertexFourByFourMiddleOneExactGradeCapacity :
    SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus
      sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width := by
  intro totalC
  apply Function.Embedding.nonempty_of_card_le
  simp only [← Nat.card_eq_fintype_card]
  rw [sixVertexFourByFourPhysicalSourceGradeCount_middleOne,
    sixVertexFourByFourOffDiagonalGradeCount_eq_nat]
  by_cases htotal : totalC < 33
  · exact sixVertexFourByFour_middleOne_gradeCapacity_certificate
      ⟨totalC, htotal⟩
  · have hzero : sixVertexFourByFourPairGradeCountNat 0 2 totalC = 0 := by
      rw [← sixVertexFourByFourPhysicalSourceGradeCount_middleOne]
      apply Nat.card_eq_zero.mpr
      left
      constructor
      intro source
      have hle := sixVertexFourByFourPhysicalSourceTotalC_le source.1
      omega
    simp [hzero]

theorem sixVertexFourByFourMiddleTwoExactGradeCapacity :
    SixVertexPhysicalRowCycleExactGradeCapacity sixVertexFourByFourTorus
      sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width := by
  intro totalC
  apply Function.Embedding.nonempty_of_card_le
  simp only [← Nat.card_eq_fintype_card]
  rw [sixVertexFourByFourPhysicalSourceGradeCount_middleTwo,
    sixVertexFourByFourOffDiagonalGradeCount_eq_nat]
  by_cases htotal : totalC < 33
  · exact sixVertexFourByFour_middleTwo_gradeCapacity_certificate
      ⟨totalC, htotal⟩
  · have hzero : sixVertexFourByFourPairGradeCountNat 1 3 totalC = 0 := by
      rw [← sixVertexFourByFourPhysicalSourceGradeCount_middleTwo]
      apply Nat.card_eq_zero.mpr
      left
      constructor
      intro source
      have hle := sixVertexFourByFourPhysicalSourceTotalC_le source.1
      omega
    simp [hzero]

noncomputable def sixVertexFourByFourMiddleOneRowCyclePairedBranchEmbeddings :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings sixVertexFourByFourTorus
      sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width :=
  sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    sixVertexFourByFourMiddleOneExactGradeCapacity

noncomputable def sixVertexFourByFourMiddleTwoRowCyclePairedBranchEmbeddings :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings sixVertexFourByFourTorus
      sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width :=
  sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    sixVertexFourByFourMiddleTwoExactGradeCapacity

noncomputable def sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorOne
      sixVertexFourByFourSectorOne_pos
      sixVertexFourByFourSectorOne_lt_width :=
  sixVertexFourByFourMiddleOneRowCyclePairedBranchEmbeddings.toPhysical

noncomputable def sixVertexFourByFourMiddleTwoPhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorTwo
      sixVertexFourByFourSectorTwo_pos
      sixVertexFourByFourSectorTwo_lt_width :=
  sixVertexFourByFourMiddleTwoRowCyclePairedBranchEmbeddings.toPhysical

noncomputable def sixVertexFourByFourMiddleThreePhysicalPairedBranchEmbeddings :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      sixVertexFourByFourTorus sixVertexFourByFourSectorThree
      (by norm_num [sixVertexFourByFourSectorThree])
      (by norm_num [sixVertexFourByFourSectorThree,
        sixVertexFourByFourTorus]) := by
  simpa [sixVertexFourByFourSectorOne, sixVertexFourByFourSectorThree,
    sixVertexFourByFourTorus, sixVertexPhysicalParticleHoleMiddle] using
    sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings.particleHole

theorem sixVertexFourByFourPhysicalPairedBranchEmbeddings_allSectors
    (n : Nat) (hn0 : 0 < n) (hn4 : n < 4) :
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        sixVertexFourByFourTorus
        ⟨n, by norm_num [sixVertexFourByFourTorus]; omega⟩ hn0 hn4) := by
  have hn : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl | rfl
  · simpa [sixVertexFourByFourSectorOne] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorOne
          sixVertexFourByFourSectorOne_pos
          sixVertexFourByFourSectorOne_lt_width) from
        ⟨sixVertexFourByFourMiddleOnePhysicalPairedBranchEmbeddings⟩)
  · simpa [sixVertexFourByFourSectorTwo] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorTwo
          sixVertexFourByFourSectorTwo_pos
          sixVertexFourByFourSectorTwo_lt_width) from
        ⟨sixVertexFourByFourMiddleTwoPhysicalPairedBranchEmbeddings⟩)
  · simpa [sixVertexFourByFourSectorThree] using
      (show Nonempty
        (SixVertexConfigurationPhysicalPairedBranchEmbeddings
          sixVertexFourByFourTorus sixVertexFourByFourSectorThree
          (by norm_num [sixVertexFourByFourSectorThree])
          (by norm_num [sixVertexFourByFourSectorThree,
            sixVertexFourByFourTorus])) from
        ⟨sixVertexFourByFourMiddleThreePhysicalPairedBranchEmbeddings⟩)

end

end StatMech.FrontierD
