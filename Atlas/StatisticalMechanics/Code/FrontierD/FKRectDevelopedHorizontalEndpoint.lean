/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectColumnTranslation



open Set

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section


noncomputable def fkRectDevelopedThreeByOneHorizontalEndpointPairs (n : Nat) :
    Finset ((fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) := by
  classical
  letI : Fintype (fkRectDevelopedThreeByOneRect n) := by
    rw [fkRectDevelopedThreeByOneRect]
    exact (rect_finite 0 (3 * (n : Int)) 0 n).fintype
  exact Finset.univ.filter fun p =>
    p.1.1 0 = 0 ∧ p.2.1 0 = 3 * (n : Int)

theorem mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs
    (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) :
    p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n ↔
      p.1.1 0 = 0 ∧ p.2.1 0 = 3 * (n : Int) := by
  classical
  unfold fkRectDevelopedThreeByOneHorizontalEndpointPairs
  simp

theorem fkRectDevelopedThreeByOneHorizontalCrossingEvent_eq_endpointUnion
    (R : FKRectTorus) (n : Nat) :
    fkRectDevelopedRectangleHorizontalCrossingEvent
        R n 0 (3 * (n : Int)) 0 n =
      fkRectFiniteEventUnion
        (fkRectDevelopedThreeByOneHorizontalEndpointPairs n)
        (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    let p : (fkRectDevelopedThreeByOneRect n) ×
        (fkRectDevelopedThreeByOneRect n) :=
      (⟨x.1, x.2.1⟩, ⟨y.1, y.2.1⟩)
    refine ⟨p, ?_, ?_⟩
    · classical
      simp [fkRectDevelopedThreeByOneHorizontalEndpointPairs, p,
        x.2.2, y.2.2]
    · simpa [fkRectDevelopedThreeByOneEndpointConnectionEvent, p,
        fkRectDevelopedThreeByOneRect] using hxy
  · rintro ⟨p, hp, hxy⟩
    have hend : p.1.1 0 = 0 ∧ p.2.1 0 = 3 * (n : Int) :=
      (mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs n p).mp hp
    refine ⟨⟨p.1.1, p.1.2, hend.1⟩,
      ⟨p.2.1, p.2.2, hend.2⟩, ?_⟩
    simpa [fkRectDevelopedThreeByOneEndpointConnectionEvent,
      fkRectDevelopedThreeByOneRect] using hxy

theorem fkRectDevelopedThreeByOneHorizontalEndpointPairs_nonempty (n : Nat) :
    (fkRectDevelopedThreeByOneHorizontalEndpointPairs n).Nonempty := by
  classical
  let x : Site 2 := ![0, 0]
  let y : Site 2 := ![3 * (n : Int), 0]
  have hx : x ∈ fkRectDevelopedThreeByOneRect n := by
    simp [fkRectDevelopedThreeByOneRect, mem_rect, x]
  have hy : y ∈ fkRectDevelopedThreeByOneRect n := by
    simp [fkRectDevelopedThreeByOneRect, mem_rect, y]
  refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
  simp [fkRectDevelopedThreeByOneHorizontalEndpointPairs, x, y]


theorem fkRectDevelopedThreeByOneHorizontalEndpointPairs_card_le (n : Nat) :
    (fkRectDevelopedThreeByOneHorizontalEndpointPairs n).card ≤
      (n + 1) ^ 2 := by
  classical
  let encode :
      {p // p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n} →
        Fin (n + 1) × Fin (n + 1) := fun p =>
    (⟨Int.toNat (p.1.1.1 1), by
        have hp := p.1.1.2
        change p.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp
        rw [mem_rect] at hp
        omega⟩,
      ⟨Int.toNat (p.1.2.1 1), by
        have hp := p.1.2.2
        change p.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp
        rw [mem_rect] at hp
        omega⟩)
  have hinj : Function.Injective encode := by
    intro p r hpr
    have hpEnds :=
      (mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs n p.1).mp p.2
    have hrEnds :=
      (mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs n r.1).mp r.2
    have hfirst : Int.toNat (p.1.1.1 1) =
        Int.toNat (r.1.1.1 1) := congrArg (fun z => z.1.val) hpr
    have hsecond : Int.toNat (p.1.2.1 1) =
        Int.toNat (r.1.2.1 1) := congrArg (fun z => z.2.val) hpr
    have hp1 := p.1.1.2
    have hp2 := p.1.2.2
    have hr1 := r.1.1.2
    have hr2 := r.1.2.2
    change p.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp1
    change p.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp2
    change r.1.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hr1
    change r.1.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hr2
    rw [mem_rect] at hp1 hp2 hr1 hr2
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.1.trans hrEnds.1.symm
      · calc
          p.1.1.1 1 = (Int.toNat (p.1.1.1 1) : Int) :=
            (Int.toNat_of_nonneg hp1.2.2.1).symm
          _ = (Int.toNat (r.1.1.1 1) : Int) := by exact_mod_cast hfirst
          _ = r.1.1.1 1 := Int.toNat_of_nonneg hr1.2.2.1
    · apply Subtype.ext
      apply funext
      intro i
      fin_cases i
      · exact hpEnds.2.trans hrEnds.2.symm
      · calc
          p.1.2.1 1 = (Int.toNat (p.1.2.1 1) : Int) :=
            (Int.toNat_of_nonneg hp2.2.2.1).symm
          _ = (Int.toNat (r.1.2.1 1) : Int) := by exact_mod_cast hsecond
          _ = r.1.2.1 1 := Int.toNat_of_nonneg hr2.2.2.1
  rw [← Fintype.card_coe]
  calc
    Fintype.card
        {p // p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n} ≤
      Fintype.card (Fin (n + 1) × Fin (n + 1)) :=
        Fintype.card_le_of_injective encode hinj
    _ = (n + 1) ^ 2 := by simp [pow_two]



theorem fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor
    (R : FKRectTorus) (n : Nat) {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcross : crossingFloor ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n,
      crossingFloor ≤ ((3 * n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
  rw [fkRectDevelopedThreeByOneHorizontalCrossingEvent_eq_endpointUnion]
    at hcross
  obtain ⟨p, hp, hlower⟩ := exists_card_mul_eventMass_ge_of_finiteUnion_ge
    R (zero_lt_one.trans_le hq)
    (fkRectDevelopedThreeByOneHorizontalEndpointPairs_nonempty n)
    (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) hcross
  refine ⟨p, hp, hlower.trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · have hcard :=
      (fkRectDevelopedThreeByOneHorizontalEndpointPairs_card_le n).trans
        (Nat.pow_le_pow_left (by omega : n + 1 ≤ 3 * n + 1) 2)
    exact_mod_cast hcard
  · exact fkRectCriticalEventMass_nonneg R
      (zero_lt_one.trans_le hq) _



theorem fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge
    (R : FKRectTorus) (n : Nat) {q : Real} (hq : 1 ≤ q)
    (hcross : 1 / (2 * (1 + q)) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n,
      1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) *
        fkRectCriticalEventMass R q
          (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) :=
  fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor
    R n hq hcross



theorem fkRectDevelopedThreeByOneHorizontalEndpoint_row_span
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hp : p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n) :
    (2 * n : Int) ≤
      ((fkRectDevelopedSquareVertex R n p.2).2.val : Int) -
        (fkRectDevelopedSquareVertex R n p.1).2.val := by
  have hend :=
    (mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs n p).mp hp
  have hp1 := p.1.2
  have hp2 := p.2.2
  change p.1.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp1
  change p.2.1 ∈ rect 0 (3 * (n : Int)) 0 n at hp2
  rw [mem_rect] at hp1 hp2
  rw [fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.1,
    fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight p.2,
    hend.1, hend.2]
  omega



theorem fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : crossingFloor ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n,
      let S := fkRectDevelopedThreeByOneTorusCarrier R n
      let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
      let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
      (n : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| + 2 ∧
        fkRectDevelopedReflectedEndpointLowerOf crossingFloor n ≤
          fkRectCriticalEventMass R q
            (fkRectReflectedCarrierConnectionEvent R S x y) := by
  obtain ⟨p, hp, havg⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor
      R n hq hcross
  refine ⟨p, hp, ?_⟩
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  let M : Real := (((3 * n + 1) ^ 2 : Nat) : Real)
  let a : Real := crossingFloor / M
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hplanar : a ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
    rw [show a = crossingFloor / M by rfl,
      div_le_iff₀ hM]
    simpa [M, mul_comm] using havg
  have hcarrier : a ≤ fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega S x y} :=
    hplanar.trans (fkRectCriticalEventMass_mono R
      (zero_lt_one.trans_le hq)
      (fkRectDevelopedThreeByOneEndpointConnection_subset_carrier
        R n hwidth hheight p))
  constructor
  · have hspan := fkRectDevelopedThreeByOneHorizontalEndpoint_row_span
      R n hwidth hheight p hp
    change (n : Int) ≤ 2 *
      |((fkRectDevelopedSquareVertex R n p.2).2.val : Int) -
        (fkRectDevelopedSquareVertex R n p.1).2.val| + 2
    rw [abs_of_nonneg (by omega)]
    omega
  · have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg hcrossingFloor.le hM.le
    have hreflect :=
      fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier
        R hq S x y ha hcarrier
    dsimp [a, M] at hreflect
    simpa [fkRectDevelopedReflectedEndpointLowerOf, S, x, y] using hreflect



theorem fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q)
    (hcross : 1 / (2 * (1 + q)) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n,
      let S := fkRectDevelopedThreeByOneTorusCarrier R n
      let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
      let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
      (n : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| + 2 ∧
        fkRectDevelopedReflectedEndpointLower q n ≤
          fkRectCriticalEventMass R q
            (fkRectReflectedCarrierConnectionEvent R S x y) := by
  simpa [fkRectDevelopedReflectedEndpointLower] using
    (fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor
      R n hn hwidth hheight hq
        (show 0 < 1 / (2 * (1 + q)) by positivity) hcross)




theorem fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : crossingFloor ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ B : FKRectPositiveRowOrientedBlock R q n,
      B.block.massFloor =
        fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
  have hwidth' : 4 * n < R.width := by omega
  have hheight' : 4 * n < R.height := by omega
  obtain ⟨p, hp, hspan, hlower⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor
      R n hn hwidth' hheight' hq hcrossingFloor hcross
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  have hrows : x.1.2.val ≤ 8 * n + 1 ∧
      y.1.2.val ≤ 8 * n + 1 := by
    constructor
    · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
        R n hwidth' hheight' x.2).trans (by omega)
    · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
        R n hwidth' hheight' y.2).trans (by omega)
  have hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * n := by
    intro v hv
    exact (fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
      R n hn hwidth' hheight' y.1.2.val hv).2
  let B0 := fkRectOrientedEvenRowBlockOfReflectedCarrier
    R q n S x y hspan hrows
      (fkRectDevelopedReflectedEndpointLowerOf_pos
        hcrossingFloor n).le hlower hcolumns
  have hoffset : Even (4 * n + 2) := by
    rw [show 4 * n + 2 = 2 * (2 * n + 1) by omega]
    exact even_two_mul _
  let B := B0.translate (4 * n + 2) hoffset
  have hBfloor : B.massFloor =
      fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
    simp [B, B0]
  refine ⟨⟨B, ?_⟩, hBfloor⟩
  · intro v hv
    have hcenter : y.1.2.val ≤ 4 * n :=
      fkRectDevelopedThreeByOneTorusCarrier_row_bounds
        R n hwidth' hheight' y.2
    have hv' : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2)
        (fkRectDevelopedThreeByOneTorusCarrier R n ∪
          fkRectDevelopedReflectionSet R y.1.2.val
            (fkRectDevelopedThreeByOneTorusCarrier R n)) := by
      simpa [B, B0, S] using hv
    have hb := fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds
      R n hwidth' hheight y.1.2.val hcenter hv'
    exact ⟨hb.1, hb.2.trans (by omega)⟩


theorem fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q : Real} (hq : 1 ≤ q)
    (hcross : 1 / (2 * (1 + q)) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    Nonempty (FKRectPositiveRowOrientedBlock R q n) := by
  obtain ⟨B, -⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor
      R n hn hwidth hheight hq
        (show 0 < 1 / (2 * (1 + q)) by positivity) hcross
  exact ⟨B⟩



theorem fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q crossingFloor : Real} (hq : 1 ≤ q)
    (hcrossingFloor : 0 < crossingFloor)
    (hcross : crossingFloor ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    ∃ B : FKRectPositiveBandOrientedBlock R q n,
      B.massFloor =
        fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
  obtain ⟨B, hB⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor
      R n hn hwidth hheight hq hcrossingFloor hcross
  exact ⟨B.columnSuccBand (by omega), hB⟩


theorem fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q : Real} (hq : 1 ≤ q)
    (hcross : 1 / (2 * (1 + q)) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n)) :
    Nonempty (FKRectPositiveBandOrientedBlock R q n) := by
  obtain ⟨B, -⟩ :=
    fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor
      R n hn hwidth hheight hq
        (show 0 < 1 / (2 * (1 + q)) by positivity) hcross
  exact ⟨B⟩

end

end StatMech.FrontierD
