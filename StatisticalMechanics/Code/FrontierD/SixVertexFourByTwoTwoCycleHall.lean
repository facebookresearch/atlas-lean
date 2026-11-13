/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleObstructionRepair











namespace StatMech.FrontierD

noncomputable section

local instance sixVertexFourByTwoHallIceRuleDecidable
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))


def sixVertexFourByTwoSectorZeroMasks : Fin 4 -> Nat × Nat := ![
  (0x00, 0x00), (0x0f, 0x00), (0xf0, 0x00), (0xff, 0x00)
]


def sixVertexFourByTwoSectorOneMasks : Fin 28 -> Nat × Nat := ![
  (0x00, 0x11), (0x00, 0x22), (0x00, 0x44), (0x00, 0x88),
  (0x0f, 0x11), (0x0f, 0x22), (0x0f, 0x44), (0x0f, 0x88),
  (0x1e, 0x21), (0x2d, 0x42), (0x3c, 0x41), (0x4b, 0x84),
  (0x69, 0x82), (0x78, 0x81), (0x87, 0x18), (0x96, 0x28),
  (0xb4, 0x48), (0xc3, 0x14), (0xd2, 0x24), (0xe1, 0x12),
  (0xf0, 0x11), (0xf0, 0x22), (0xf0, 0x44), (0xf0, 0x88),
  (0xff, 0x11), (0xff, 0x22), (0xff, 0x44), (0xff, 0x88)
]


def sixVertexFourByTwoSectorTwoMasks : Fin 50 -> Nat × Nat := ![
  (0x00, 0x33), (0x00, 0x55), (0x00, 0x66), (0x00, 0x99),
  (0x00, 0xaa), (0x00, 0xcc), (0x0f, 0x33), (0x0f, 0x55),
  (0x0f, 0x66), (0x0f, 0x99), (0x0f, 0xaa), (0x0f, 0xcc),
  (0x1e, 0x65), (0x1e, 0xa9), (0x2d, 0x53), (0x2d, 0xca),
  (0x3c, 0x63), (0x3c, 0xc9), (0x4b, 0x95), (0x4b, 0xa6),
  (0x5a, 0xa5), (0x69, 0x93), (0x69, 0xc6), (0x78, 0xa3),
  (0x78, 0xc5), (0x87, 0x3a), (0x87, 0x5c), (0x96, 0x39),
  (0x96, 0x6c), (0xa5, 0x5a), (0xb4, 0x59), (0xb4, 0x6a),
  (0xc3, 0x36), (0xc3, 0x9c), (0xd2, 0x35), (0xd2, 0xac),
  (0xe1, 0x56), (0xe1, 0x9a), (0xf0, 0x33), (0xf0, 0x55),
  (0xf0, 0x66), (0xf0, 0x99), (0xf0, 0xaa), (0xf0, 0xcc),
  (0xff, 0x33), (0xff, 0x55), (0xff, 0x66), (0xff, 0x99),
  (0xff, 0xaa), (0xff, 0xcc)
]

def sixVertexFourByTwoSectorZeroArrows (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorZeroMasks i).1
    (sixVertexFourByTwoSectorZeroMasks i).2

def sixVertexFourByTwoSectorOneArrows (i : Fin 28) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorOneMasks i).1
    (sixVertexFourByTwoSectorOneMasks i).2

def sixVertexFourByTwoSectorTwoArrows (i : Fin 50) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorTwoMasks i).1
    (sixVertexFourByTwoSectorTwoMasks i).2

def sixVertexFourByTwoSourceIndexArrows (i : Fin 4 × Fin 50) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  (sixVertexFourByTwoSectorZeroArrows i.1,
    sixVertexFourByTwoSectorTwoArrows i.2)

def sixVertexFourByTwoTargetIndexArrows (i : Fin 28 × Fin 28) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  (sixVertexFourByTwoSectorOneArrows i.1,
    sixVertexFourByTwoSectorOneArrows i.2)



def sixVertexFourByTwoMatchingTable : Fin 200 -> Fin 28 × Fin 28 := ![
  (0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3), (0, 5), (0, 6),
  (1, 6), (0, 7), (1, 7), (2, 7), (2, 8), (3, 8), (0, 9), (3, 9),
  (1, 10), (3, 10), (0, 11), (1, 11), (8, 11), (0, 12), (2, 12), (1, 13),
  (2, 13), (1, 14), (2, 14), (0, 15), (2, 15), (9, 14), (0, 16), (1, 16),
  (1, 17), (3, 17), (0, 18), (3, 18), (2, 19), (3, 19), (0, 21), (0, 22),
  (1, 22), (0, 23), (1, 23), (2, 23), (0, 25), (0, 26), (1, 26), (0, 27),
  (1, 27), (2, 27), (4, 1), (4, 2), (5, 2), (4, 3), (5, 3), (6, 3),
  (4, 5), (4, 6), (5, 6), (4, 7), (5, 7), (6, 7), (6, 8), (7, 8),
  (4, 9), (7, 9), (5, 10), (7, 10), (4, 11), (5, 11), (11, 8), (4, 12),
  (6, 12), (5, 13), (6, 13), (5, 14), (6, 14), (4, 15), (6, 15), (14, 9),
  (4, 16), (5, 16), (5, 17), (7, 17), (4, 18), (7, 18), (6, 19), (7, 19),
  (4, 21), (4, 22), (5, 22), (4, 23), (5, 23), (6, 23), (4, 25), (4, 26),
  (5, 26), (4, 27), (5, 27), (6, 27), (20, 1), (20, 2), (21, 2), (20, 3),
  (21, 3), (22, 3), (20, 5), (20, 6), (21, 6), (20, 7), (21, 7), (22, 7),
  (22, 8), (23, 8), (20, 9), (23, 9), (21, 10), (23, 10), (20, 11), (21, 11),
  (13, 18), (20, 12), (22, 12), (21, 13), (22, 13), (21, 14), (22, 14), (20, 15),
  (22, 15), (16, 19), (20, 16), (21, 16), (21, 17), (23, 17), (20, 18), (23, 18),
  (22, 19), (23, 19), (20, 21), (20, 22), (21, 22), (20, 23), (21, 23), (22, 23),
  (20, 25), (20, 26), (21, 26), (20, 27), (21, 27), (22, 27), (24, 1), (24, 2),
  (25, 2), (24, 3), (25, 3), (26, 3), (24, 5), (24, 6), (25, 6), (24, 7),
  (25, 7), (26, 7), (26, 8), (27, 8), (24, 9), (27, 9), (25, 10), (27, 10),
  (24, 11), (25, 11), (18, 13), (24, 12), (26, 12), (25, 13), (26, 13), (25, 14),
  (26, 14), (24, 15), (26, 15), (19, 16), (24, 16), (25, 16), (25, 17), (27, 17),
  (24, 18), (27, 18), (26, 19), (27, 19), (24, 21), (24, 22), (25, 22), (24, 23),
  (25, 23), (26, 23), (24, 25), (24, 26), (25, 26), (24, 27), (25, 27), (26, 27)
]


def sixVertexFourByTwoMatchingIndex (i : Fin 4 × Fin 50) :
    Fin 28 × Fin 28 :=
  sixVertexFourByTwoMatchingTable
    (finProdFinEquiv (m := 4) (n := 50) i)

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoMatchingTable_injective :
    Function.Injective sixVertexFourByTwoMatchingTable := by
  decide +revert

theorem sixVertexFourByTwoMatchingIndex_injective :
    Function.Injective sixVertexFourByTwoMatchingIndex := by
  exact sixVertexFourByTwoMatchingTable_injective.comp
    (finProdFinEquiv (m := 4) (n := 50)).injective

theorem sixVertexFourByTwoSectorZeroArrows_valid (i : Fin 4) :
    (sixVertexFourByTwoSectorZeroArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorZeroArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoSectorOneArrows_valid (i : Fin 28) :
    (sixVertexFourByTwoSectorOneArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorOneArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoSectorTwoArrows_valid (i : Fin 50) :
    (sixVertexFourByTwoSectorTwoArrows i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoSectorTwoArrows i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
  fin_cases i <;> decide +revert

def sixVertexFourByTwoSourceFlatArrows (i : Fin 200) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoSourceIndexArrows
    ((finProdFinEquiv (m := 4) (n := 50)).symm i)

def sixVertexFourByTwoTargetFlatArrows (i : Fin 200) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoTargetIndexArrows
    (sixVertexFourByTwoMatchingTable i)



def sixVertexFourByTwoExceptionalFlatIndex (i : Fin 200) : Prop :=
  i.val = 20 \/ i.val = 29 \/ i.val = 170 \/ i.val = 179

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoOrdinaryFlat_fineUnion
    (i : Fin 200) (hordinary : ¬ sixVertexFourByTwoExceptionalFlatIndex i) :
    sixVertexPairUnionHorizontal (sixVertexFourByTwoSourceFlatArrows i) =
        sixVertexPairUnionHorizontal (sixVertexFourByTwoTargetFlatArrows i) /\
      sixVertexPairUnionVertical (sixVertexFourByTwoSourceFlatArrows i) =
        sixVertexPairUnionVertical (sixVertexFourByTwoTargetFlatArrows i) /\
      sixVertexHorizontalPairBoundedFineRowProfile
          ((sixVertexFourByTwoSourceFlatArrows i).1.horizontal,
            (sixVertexFourByTwoSourceFlatArrows i).2.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
          ((sixVertexFourByTwoTargetFlatArrows i).1.horizontal,
            (sixVertexFourByTwoTargetFlatArrows i).2.horizontal) := by
  fin_cases i <;>
    simp [sixVertexFourByTwoExceptionalFlatIndex] at hordinary <;>
    decide +revert



def sixVertexFourByTwoExceptionalRepairFlatIndex : Fin 4 -> Fin 200 := ![
  20, 170, 29, 179
]

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoExceptionalFlat_fineRelated (i : Fin 4) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceFlatArrows
        (sixVertexFourByTwoExceptionalRepairFlatIndex i))
      (sixVertexFourByTwoTargetFlatArrows
        (sixVertexFourByTwoExceptionalRepairFlatIndex i)) := by
  fin_cases i
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 0,
        sixVertexFourByTwoExceptionalSourceSecond 0)
      (sixVertexFourByTwoExceptionalTargetFirst 0,
        sixVertexFourByTwoExceptionalTargetSecond 0)
    exact sixVertexFourByTwoExceptional_fineRelated 0
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 1,
        sixVertexFourByTwoExceptionalSourceSecond 1)
      (sixVertexFourByTwoExceptionalTargetFirst 1,
        sixVertexFourByTwoExceptionalTargetSecond 1)
    exact sixVertexFourByTwoExceptional_fineRelated 1
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 2,
        sixVertexFourByTwoExceptionalSourceSecond 2)
      (sixVertexFourByTwoExceptionalTargetFirst 2,
        sixVertexFourByTwoExceptionalTargetSecond 2)
    exact sixVertexFourByTwoExceptional_fineRelated 2
  · change sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst 3,
        sixVertexFourByTwoExceptionalSourceSecond 3)
      (sixVertexFourByTwoExceptionalTargetFirst 3,
        sixVertexFourByTwoExceptionalTargetSecond 3)
    exact sixVertexFourByTwoExceptional_fineRelated 3


theorem sixVertexFourByTwoMatchingTable_fineRelated (i : Fin 200) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceFlatArrows i)
      (sixVertexFourByTwoTargetFlatArrows i) := by
  by_cases hordinary : ¬ sixVertexFourByTwoExceptionalFlatIndex i
  · obtain ⟨hhorizontal, hvertical, hfine⟩ :=
      sixVertexFourByTwoOrdinaryFlat_fineUnion i hordinary
    exact ⟨sixVertexPairAtMostTwoCycleRelated_of_union_eq
      hhorizontal hvertical, hfine⟩
  · have hexceptional := Classical.not_not.mp hordinary
    rcases hexceptional with h20 | h29 | h170 | h179
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 0 := by
        apply Fin.ext
        exact h20
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 0
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 2 := by
        apply Fin.ext
        exact h29
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 2
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 1 := by
        apply Fin.ext
        exact h170
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 1
    · have hi : i = sixVertexFourByTwoExceptionalRepairFlatIndex 3 := by
        apply Fin.ext
        exact h179
      rw [hi]
      exact sixVertexFourByTwoExceptionalFlat_fineRelated 3

def sixVertexFourByTwoSectorZeroConfiguration (i : Fin 4) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  ⟨sixVertexFourByTwoSectorZeroArrows i,
    (sixVertexFourByTwoSectorZeroArrows_valid i).1,
    (sixVertexFourByTwoSectorZeroArrows_valid i).2⟩

def sixVertexFourByTwoSectorOneConfiguration (i : Fin 28) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoSectorOneArrows i,
    (sixVertexFourByTwoSectorOneArrows_valid i).1,
    (sixVertexFourByTwoSectorOneArrows_valid i).2⟩

def sixVertexFourByTwoSectorTwoConfiguration (i : Fin 50) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  ⟨sixVertexFourByTwoSectorTwoArrows i,
    (sixVertexFourByTwoSectorTwoArrows_valid i).1,
    (sixVertexFourByTwoSectorTwoArrows_valid i).2⟩

def sixVertexFourByTwoHorizontalMask
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Nat :=
  Nat.ofBits fun i : Fin 8 =>
    let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
    omega.horizontal (yx.2, yx.1)

def sixVertexFourByTwoVerticalMask
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Nat :=
  Nat.ofBits fun i : Fin 8 =>
    let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
    omega.vertical (yx.2, yx.1)

def sixVertexFourByTwoHorizontalMaskFin
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Fin 256 :=
  ⟨sixVertexFourByTwoHorizontalMask omega, by
    simpa [sixVertexFourByTwoHorizontalMask] using
      Nat.ofBits_lt_two_pow (fun i : Fin 8 =>
        let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
        omega.horizontal (yx.2, yx.1))⟩

def sixVertexFourByTwoVerticalMaskFin
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Fin 256 :=
  ⟨sixVertexFourByTwoVerticalMask omega, by
    simpa [sixVertexFourByTwoVerticalMask] using
      Nat.ofBits_lt_two_pow (fun i : Fin 8 =>
        let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
        omega.vertical (yx.2, yx.1))⟩

theorem sixVertexFourByTwoArrowsOf_encodedMasks
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    sixVertexFourByTwoArrowsOfMasks
        (sixVertexFourByTwoHorizontalMask omega)
        (sixVertexFourByTwoVerticalMask omega) = omega := by
  apply SixVertexArrows.ext
  · funext v
    let i : Fin 8 := finProdFinEquiv (m := 2) (n := 4) (v.2, v.1)
    change (Nat.ofBits _).testBit (v.2.val * 4 + v.1.val) = _
    have hval : v.2.val * 4 + v.1.val = i.val := by
      simp [i, finProdFinEquiv]
      omega
    rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
    change omega.horizontal
      ((finProdFinEquiv (m := 2) (n := 4)).symm i).swap =
        omega.horizontal v
    rw [(finProdFinEquiv (m := 2) (n := 4)).symm_apply_apply]
    rfl
  · funext v
    let i : Fin 8 := finProdFinEquiv (m := 2) (n := 4) (v.2, v.1)
    change (Nat.ofBits _).testBit (v.2.val * 4 + v.1.val) = _
    have hval : v.2.val * 4 + v.1.val = i.val := by
      simp [i, finProdFinEquiv]
      omega
    rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
    change omega.vertical
      ((finProdFinEquiv (m := 2) (n := 4)).symm i).swap =
        omega.vertical v
    rw [(finProdFinEquiv (m := 2) (n := 4)).symm_apply_apply]
    rfl

abbrev SixVertexFourByTwoVerticalMaskInSector (sector : Nat) :=
  {verticalMask : Fin 256 //
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        (sixVertexFourByTwoArrowsOfMasks 0 verticalMask.val)
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = sector}

def sixVertexFourByTwoVerticalMaskInSector
    (sector : Nat) (omega : SixVertexArrows sixVertexFourByTwoTorus)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus omega
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = sector) :
    SixVertexFourByTwoVerticalMaskInSector sector :=
  ⟨sixVertexFourByTwoVerticalMaskFin omega, by
    have hencoded := congrArg
      (fun arrows => sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByTwoTorus arrows
          (svFinLast sixVertexFourByTwoTorus.height_pos)))
      (sixVertexFourByTwoArrowsOf_encodedMasks omega)
    exact hencoded.trans hsector⟩

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorZeroMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 0)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule)
    :
    exists i : Fin 4,
      sixVertexFourByTwoSectorZeroMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorOneMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 1)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule) :
    exists i : Fin 28,
      sixVertexFourByTwoSectorOneMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxHeartbeats 1000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorTwoMasks_classify
    (horizontalMask : Fin 256)
    (verticalMask : SixVertexFourByTwoVerticalMaskInSector 2)
    (hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val).IceRule) :
    exists i : Fin 50,
      sixVertexFourByTwoSectorTwoMasks i =
        (horizontalMask.val, verticalMask.val.val) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorZeroArrows_injective :
    Function.Injective sixVertexFourByTwoSectorZeroArrows := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorOneArrows_injective :
    Function.Injective sixVertexFourByTwoSectorOneArrows := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoSectorTwoArrows_injective :
    Function.Injective sixVertexFourByTwoSectorTwoArrows := by
  decide +revert

theorem sixVertexFourByTwoSectorZeroConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorZeroConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorZeroArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorOneConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorOneConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorOneArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorTwoConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorTwoConfiguration := by
  intro i j hij
  apply sixVertexFourByTwoSectorTwoArrows_injective
  exact congrArg Subtype.val hij

theorem sixVertexFourByTwoSectorZeroConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorZeroConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 0
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorZeroMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorZeroArrows i = omega.1
  unfold sixVertexFourByTwoSectorZeroArrows
  rw [hmasks]
  exact hencoded

theorem sixVertexFourByTwoSectorOneConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorOneConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 1
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorOneMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorOneArrows i = omega.1
  unfold sixVertexFourByTwoSectorOneArrows
  rw [hmasks]
  exact hencoded

theorem sixVertexFourByTwoSectorTwoConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorTwoConfiguration := by
  intro omega
  let horizontalMask := sixVertexFourByTwoHorizontalMaskFin omega.1
  let verticalMask := sixVertexFourByTwoVerticalMaskInSector 2
    omega.1 omega.2.2
  have hencoded := sixVertexFourByTwoArrowsOf_encodedMasks omega.1
  have hice : (sixVertexFourByTwoArrowsOfMasks
      horizontalMask.val verticalMask.val.val).IceRule := by
    change (sixVertexFourByTwoArrowsOfMasks
      (sixVertexFourByTwoHorizontalMask omega.1)
      (sixVertexFourByTwoVerticalMask omega.1)).IceRule
    rw [hencoded]
    exact omega.2.1
  obtain ⟨i, hmasks⟩ :=
    sixVertexFourByTwoSectorTwoMasks_classify
      horizontalMask verticalMask hice
  refine ⟨i, Subtype.ext ?_⟩
  change sixVertexFourByTwoSectorTwoArrows i = omega.1
  unfold sixVertexFourByTwoSectorTwoArrows
  rw [hmasks]
  exact hencoded

def sixVertexFourByTwoSectorZeroEquiv :
    Fin 4 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  Equiv.ofBijective sixVertexFourByTwoSectorZeroConfiguration
    ⟨sixVertexFourByTwoSectorZeroConfiguration_injective,
      sixVertexFourByTwoSectorZeroConfiguration_surjective⟩

def sixVertexFourByTwoSectorOneEquiv :
    Fin 28 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  Equiv.ofBijective sixVertexFourByTwoSectorOneConfiguration
    ⟨sixVertexFourByTwoSectorOneConfiguration_injective,
      sixVertexFourByTwoSectorOneConfiguration_surjective⟩

def sixVertexFourByTwoSectorTwoEquiv :
    Fin 50 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  Equiv.ofBijective sixVertexFourByTwoSectorTwoConfiguration
    ⟨sixVertexFourByTwoSectorTwoConfiguration_injective,
      sixVertexFourByTwoSectorTwoConfiguration_surjective⟩

def sixVertexFourByTwoSourcePairEquiv :
    (Fin 4 × Fin 50) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorZero ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo) :=
  Equiv.prodCongr sixVertexFourByTwoSectorZeroEquiv
    sixVertexFourByTwoSectorTwoEquiv

def sixVertexFourByTwoTargetPairEquiv :
    (Fin 28 × Fin 28) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne) :=
  Equiv.prodCongr sixVertexFourByTwoSectorOneEquiv
    sixVertexFourByTwoSectorOneEquiv

theorem sixVertexFourByTwoMatchingIndex_fineRelated
    (i : Fin 4 × Fin 50) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoSourceIndexArrows i)
      (sixVertexFourByTwoTargetIndexArrows
        (sixVertexFourByTwoMatchingIndex i)) := by
  simpa [sixVertexFourByTwoSourceFlatArrows,
    sixVertexFourByTwoTargetFlatArrows,
    sixVertexFourByTwoMatchingIndex] using
      sixVertexFourByTwoMatchingTable_fineRelated
        (finProdFinEquiv (m := 4) (n := 50) i)


def sixVertexFourByTwoConfigurationPairMatching
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne :=
  sixVertexFourByTwoTargetPairEquiv
    (sixVertexFourByTwoMatchingIndex
      (sixVertexFourByTwoSourcePairEquiv.symm source))

theorem sixVertexFourByTwoConfigurationPairMatching_injective :
    Function.Injective sixVertexFourByTwoConfigurationPairMatching := by
  intro source₁ source₂ heq
  apply sixVertexFourByTwoSourcePairEquiv.symm.injective
  apply sixVertexFourByTwoMatchingIndex_injective
  apply sixVertexFourByTwoTargetPairEquiv.injective
  exact heq

theorem sixVertexFourByTwoConfigurationPairMatching_fineRelated
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((sixVertexFourByTwoConfigurationPairMatching source).1.1,
        (sixVertexFourByTwoConfigurationPairMatching source).2.1) := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hsource := sixVertexFourByTwoSourcePairEquiv.apply_symm_apply source
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1, source.2.1)
    ((sixVertexFourByTwoTargetPairEquiv
      (sixVertexFourByTwoMatchingIndex i)).1.1,
      (sixVertexFourByTwoTargetPairEquiv
      (sixVertexFourByTwoMatchingIndex i)).2.1)
  rw [← hsource]
  exact sixVertexFourByTwoMatchingIndex_fineRelated i



theorem sixVertexFourByTwo_configurationPairTwoCycleFineHall :
    SixVertexConfigurationPairTwoCycleFineHall sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorTwo := by
  rw [configurationPairTwoCycleFineHall_iff_exists_injective]
  exact ⟨sixVertexFourByTwoConfigurationPairMatching,
    sixVertexFourByTwoConfigurationPairMatching_injective,
    sixVertexFourByTwoConfigurationPairMatching_fineRelated⟩

theorem sixVertexFourByTwo_markedTraceCoefficientwiseLogConcave :
    SixVertexMarkedTraceCoefficientwiseLogConcave 4 2 1 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne])
      sixVertexFourByTwo_configurationPairTwoCycleFineHall

theorem sixVertexFourByTwo_sectorTrace_logConcave
    {c : Real} (hc : 2 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <=
      Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexSectorTrace_logConcave_of_twoCycleFineHall
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne])
      hc sixVertexFourByTwo_configurationPairTwoCycleFineHall

end

end StatMech.FrontierD
