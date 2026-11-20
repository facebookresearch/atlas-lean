/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectEvenRowBlockRepetition



open Set SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectReflectedRowStep (x y : Nat) : Nat :=
  2 * Int.natAbs ((y : Int) - x)

theorem fkRectReflectedRowStep_even (x y : Nat) :
    Even (fkRectReflectedRowStep x y) :=
  even_two_mul _

theorem fkRectReflectedRowStep_cast (x y : Nat) :
    (fkRectReflectedRowStep x y : Int) =
      2 * |(y : Int) - x| := by
  rw [fkRectReflectedRowStep, Nat.cast_mul, Nat.cast_ofNat,
    Int.natCast_natAbs]

theorem fkRectReflectedRowStep_of_le {x y : Nat} (hxy : x ≤ y) :
    fkRectReflectedRowStep x y = 2 * (y - x) := by
  unfold fkRectReflectedRowStep
  congr 1
  apply Int.ofNat_injective
  have hnat : (((y : Int) - x).natAbs : Int) = (y - x : Nat) := by
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    push_cast
    omega
  exact hnat

theorem fkRectReflectedRowStep_of_ge {x y : Nat} (hyx : y ≤ x) :
    fkRectReflectedRowStep x y = 2 * (x - y) := by
  unfold fkRectReflectedRowStep
  congr 1
  apply Int.ofNat_injective
  have hnat : (((y : Int) - x).natAbs : Int) = (x - y : Nat) := by
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega)]
    push_cast
    omega
  exact hnat

theorem fkRectReflectedRowStep_pos_of_span
    (n x y : Nat)
    (hspan : (n : Int) ≤ 2 * |(y : Int) - x| + 2) :
    0 < fkRectReflectedRowStep x y ∨ n ≤ 2 := by
  rw [← fkRectReflectedRowStep_cast] at hspan
  omega

theorem fkRectRowTranslate_eq_add_of_lt
    (R : FKRectTorus) (offset : Nat) (y : Fin R.height)
    (hlt : y.val + offset < R.height) :
    fkRectRowTranslate R offset y = ⟨y.val + offset, hlt⟩ := by
  apply Fin.ext
  rw [fkRectRowTranslate_nat_val, Nat.mod_eq_of_lt hlt]

theorem fkRectRowTranslate_reflection_eq_sub
    (R : FKRectTorus) (offset center : Nat) (y : Fin R.height)
    (hle : y.val ≤ offset + 2 * center)
    (hlt : offset + 2 * center - y.val < R.height) :
    fkRectRowTranslate R offset (fkRectRowReflection R center y) =
      ⟨offset + 2 * center - y.val, hlt⟩ := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    rw [show ((fkRectRowTranslate R offset
        (fkRectRowReflection R center y)).val : ZMod R.height) =
          ((fkRectRowReflection R center y).val : Int) + offset by
      simpa [fkRectRowTranslate] using
        fkRectIntModFin_cast R.height_pos
          (((fkRectRowReflection R center y).val : Int) + offset)]
    push_cast
    rw [fkRectRowReflection_cast, Nat.cast_sub hle]
    push_cast
    ring
  · exact (fkRectRowTranslate R offset
      (fkRectRowReflection R center y)).isLt
  · exact hlt



theorem fkRectEvenRowTranslation_reflection_of_row_le
    (R : FKRectTorus) (x y : R.Vertex) (hxy : x.2.val ≤ y.2.val) :
    fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val) x =
      fkRectDevelopedReflectionVertexEquiv R y.2.val x := by
  apply Prod.ext
  · rfl
  · change fkRectRowTranslate R
        (fkRectReflectedRowStep x.2.val y.2.val) x.2 =
      fkRectRowReflection R y.2.val x.2
    apply Fin.ext
    apply Nat.ModEq.eq_of_lt_of_lt
    · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
      rw [show ((fkRectRowTranslate R
          (fkRectReflectedRowStep x.2.val y.2.val) x.2).val :
            ZMod R.height) =
          (x.2.val : Int) + fkRectReflectedRowStep x.2.val y.2.val by
        simpa [fkRectRowTranslate] using
          fkRectIntModFin_cast R.height_pos
            ((x.2.val : Int) +
              fkRectReflectedRowStep x.2.val y.2.val)]
      rw [fkRectRowReflection_cast,
        fkRectReflectedRowStep_of_le hxy]
      push_cast
      rw [Nat.cast_sub hxy]
      push_cast
      ring
    · exact (fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val) x).2.isLt
    · exact (fkRectDevelopedReflectionVertexEquiv R y.2.val x).2.isLt



theorem fkRectEvenRowTranslation_reflection_of_row_ge
    (R : FKRectTorus) (x y : R.Vertex) (hyx : y.2.val ≤ x.2.val) :
    fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val)
        (fkRectDevelopedReflectionVertexEquiv R y.2.val x) = x := by
  apply Prod.ext
  · rfl
  · change fkRectRowTranslate R
        (fkRectReflectedRowStep x.2.val y.2.val)
          (fkRectRowReflection R y.2.val x.2) = x.2
    apply Fin.ext
    apply Nat.ModEq.eq_of_lt_of_lt
    · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
      rw [show ((fkRectRowTranslate R
          (fkRectReflectedRowStep x.2.val y.2.val)
            (fkRectRowReflection R y.2.val x.2)).val :
            ZMod R.height) =
          ((fkRectRowReflection R y.2.val x.2).val : Int) +
            fkRectReflectedRowStep x.2.val y.2.val by
        simpa [fkRectRowTranslate] using
          fkRectIntModFin_cast R.height_pos
            (((fkRectRowReflection R y.2.val x.2).val : Int) +
                fkRectReflectedRowStep x.2.val y.2.val)]
      push_cast
      rw [fkRectRowReflection_cast,
        fkRectReflectedRowStep_of_ge hyx]
      push_cast
      rw [Nat.cast_sub hyx]
      push_cast
      ring
    · exact (fkRectEvenRowTranslationVertexEquiv R
        (fkRectReflectedRowStep x.2.val y.2.val)
          (fkRectDevelopedReflectionVertexEquiv R y.2.val x)).2.isLt
    · exact x.2.isLt


structure FKRectOrientedEvenRowBlock
    (R : FKRectTorus) (q : Real) (scale : Nat) where
  carrier : Set R.Vertex
  start : carrier
  finish : carrier
  step : Nat
  step_even : Even step
  step_scale : scale ≤ step + 2
  step_upper : step ≤ 16 * scale + 2
  translate_start :
    fkRectEvenRowTranslationVertexEquiv R step start.1 = finish.1
  massFloor : Real
  massFloor_nonneg : 0 ≤ massFloor
  mass_lower : massFloor ≤
    fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega carrier start finish}
  column_bound : ∀ v ∈ carrier, v.1.val ≤ 4 * scale


noncomputable def FKRectOrientedEvenRowBlock.translate
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    FKRectOrientedEvenRowBlock R q scale := by
  let S := fkRectEvenRowTranslationSet R offset B.carrier
  let x : S := fkRectEvenRowTranslationSetEquiv
    R offset B.carrier B.start
  let y : S := fkRectEvenRowTranslationSetEquiv
    R offset B.carrier B.finish
  refine
    { carrier := S
      start := x
      finish := y
      step := B.step
      step_even := B.step_even
      step_scale := B.step_scale
      step_upper := B.step_upper
      translate_start := ?_
      massFloor := B.massFloor
      massFloor_nonneg := B.massFloor_nonneg
      mass_lower := ?_
      column_bound := ?_ }
  · change fkRectEvenRowTranslationVertexEquiv R B.step
        (fkRectEvenRowTranslationVertexEquiv R offset B.start.1) =
      fkRectEvenRowTranslationVertexEquiv R offset B.finish.1
    rw [fkRectEvenRowTranslationVertexEquiv_add, ← B.translate_start,
      fkRectEvenRowTranslationVertexEquiv_add]
    congr 2
    omega
  · rw [show fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          B.carrier B.start B.finish} by
      simpa [S, x, y] using
        (fkRectCritical_connectedWithinMass_evenRowTranslation
          R offset hoffset q B.carrier B.start B.finish)]
    exact B.mass_lower
  · intro v hv
    exact (fkRectEvenRowTranslationSet_column_bounds
      R B.carrier offset 0 (4 * scale)
      (fun w hw => ⟨Nat.zero_le _, B.column_bound w hw⟩) hv).2

@[simp] theorem FKRectOrientedEvenRowBlock.translate_carrier
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    (B.translate offset hoffset).carrier =
      fkRectEvenRowTranslationSet R offset B.carrier := rfl

@[simp] theorem FKRectOrientedEvenRowBlock.translate_massFloor
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectOrientedEvenRowBlock R q scale)
    (offset : Nat) (hoffset : Even offset) :
    (B.translate offset hoffset).massFloor = B.massFloor := rfl



structure FKRectPositiveRowOrientedBlock
    (R : FKRectTorus) (q : Real) (scale : Nat) where
  block : FKRectOrientedEvenRowBlock R q scale
  row_bound : ∀ v ∈ block.carrier,
    1 ≤ v.2.val ∧ v.2.val ≤ 24 * scale + 4



noncomputable def fkRectOrientedEvenRowBlockOfReflectedCarrier
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    FKRectOrientedEvenRowBlock R q scale := by
  let Sr := fkRectDevelopedReflectionSet R y.1.2.val S
  let U : Set R.Vertex := S ∪ Sr
  let xU : U := ⟨x.1, Or.inl x.2⟩
  let xr : R.Vertex :=
    fkRectDevelopedReflectionVertexEquiv R y.1.2.val x.1
  let xrU : U := ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩
  let step := fkRectReflectedRowStep x.1.2.val y.1.2.val
  have hstepCast : (step : Int) =
      2 * |(y.1.2.val : Int) - x.1.2.val| :=
    fkRectReflectedRowStep_cast _ _
  have hstepScale : scale ≤ step + 2 := by
    have hspan' : (scale : Int) ≤ (step : Int) + 2 := by
      rw [hstepCast]
      exact hspan
    exact_mod_cast hspan'
  have hstepUpper : step ≤ 16 * scale + 2 := by
    rw [show step = fkRectReflectedRowStep
      x.1.2.val y.1.2.val by rfl]
    rw [← Int.ofNat_le]
    rw [fkRectReflectedRowStep_cast]
    by_cases hxy : x.1.2.val ≤ y.1.2.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  by_cases hxy : x.1.2.val ≤ y.1.2.val
  · refine
      { carrier := U
        start := xU
        finish := xrU
        step := step
        step_even := fkRectReflectedRowStep_even _ _
        step_scale := hstepScale
        step_upper := hstepUpper
        translate_start := ?_
        massFloor := massFloor
        massFloor_nonneg := hmassFloor
        mass_lower := ?_
        column_bound := ?_ }
    · exact fkRectEvenRowTranslation_reflection_of_row_le
        R x.1 y.1 hxy
    · simpa [U, Sr, xU, xrU, xr,
        fkRectReflectedCarrierConnectionEvent] using hlower
    · intro v hv
      exact hcolumns v hv
  · have hyx : y.1.2.val ≤ x.1.2.val := by omega
    refine
      { carrier := U
        start := xrU
        finish := xU
        step := step
        step_even := fkRectReflectedRowStep_even _ _
        step_scale := hstepScale
        step_upper := hstepUpper
        translate_start := ?_
        massFloor := massFloor
        massFloor_nonneg := hmassFloor
        mass_lower := ?_
        column_bound := ?_ }
    · exact fkRectEvenRowTranslation_reflection_of_row_ge
        R x.1 y.1 hyx
    · have hevent :
          {omega | FKRectConnectedWithin R omega U xrU xU} =
            {omega | FKRectConnectedWithin R omega U xU xrU} := by
        ext omega
        exact SimpleGraph.reachable_comm
      rw [hevent]
      simpa [U, Sr, xU, xrU, xr,
        fkRectReflectedCarrierConnectionEvent] using hlower
    · intro v hv
      exact hcolumns v hv

@[simp] theorem fkRectOrientedEvenRowBlockOfReflectedCarrier_carrier
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    (fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q scale S x y hspan hrows hmassFloor hlower hcolumns).carrier =
        S ∪ fkRectDevelopedReflectionSet R y.1.2.val S := by
  by_cases hxy : x.1.2.val ≤ y.1.2.val <;>
    simp [fkRectOrientedEvenRowBlockOfReflectedCarrier, hxy]

@[simp] theorem fkRectOrientedEvenRowBlockOfReflectedCarrier_massFloor
    (R : FKRectTorus) (q : Real) (scale : Nat)
    (S : Set R.Vertex) (x y : S)
    (hspan : (scale : Int) ≤
      2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
    (hrows : x.1.2.val ≤ 8 * scale + 1 ∧
      y.1.2.val ≤ 8 * scale + 1)
    {massFloor : Real} (hmassFloor : 0 ≤ massFloor)
    (hlower : massFloor ≤
      fkRectCriticalEventMass R q
        (fkRectReflectedCarrierConnectionEvent R S x y))
    (hcolumns : ∀ v ∈
      S ∪ fkRectDevelopedReflectionSet R y.1.2.val S,
      v.1.val ≤ 4 * scale) :
    (fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q scale S x y hspan hrows hmassFloor hlower hcolumns).massFloor =
        massFloor := by
  by_cases hxy : x.1.2.val ≤ y.1.2.val <;>
    simp [fkRectOrientedEvenRowBlockOfReflectedCarrier, hxy]



theorem fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectQuarterTurnSet R hH
      (fkRectDevelopedThreeByOneTorusCarrier R n)) :
    v.2.val ≤ 8 * n + 1 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectQuarterTurnVertexEquiv_apply,
    fkRectQuarterTurnVertex_snd_val]
  have hwcol := fkRectDevelopedThreeByOneTorusCarrier_column_bounds
    R n hn hwidth hheight hw
  have hwmod := Nat.mod_lt w.2.val (by norm_num : 0 < 2)
  omega

theorem fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 12 * n + 2 < R.height)
    (center : Nat) (hcenter : center ≤ 4 * n)
    {v : R.Vertex}
    (hv : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2)
      (fkRectDevelopedThreeByOneTorusCarrier R n ∪
        fkRectDevelopedReflectionSet R center
          (fkRectDevelopedThreeByOneTorusCarrier R n))) :
    1 ≤ v.2.val ∧ v.2.val ≤ 12 * n + 2 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectEvenRowTranslationVertexEquiv_apply]
  rcases hw with hw | hw
  · have hwrow := fkRectDevelopedThreeByOneTorusCarrier_row_bounds
      R n hwidth (by omega) hw
    rw [fkRectRowTranslate_eq_add_of_lt R (4 * n + 2) w.2 (by omega)]
    simp only [Fin.val_mk]
    omega
  · rcases hw with ⟨z, hz, rfl⟩
    have hzrow := fkRectDevelopedThreeByOneTorusCarrier_row_bounds
      R n hwidth (by omega) hz
    rw [fkRectDevelopedReflectionVertexEquiv_apply,
      fkRectRowTranslate_reflection_eq_sub R (4 * n + 2) center z.2
        (by omega) (by omega)]
    simp only [Fin.val_mk]
    omega

theorem fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height)
    (hrotHeight : 24 * n + 4 <
      (fkRectQuarterTurnTorus R hH).height)
    (center : Nat) (hcenter : center ≤ 8 * n + 1)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectEvenRowTranslationSet
      (fkRectQuarterTurnTorus R hH) (8 * n + 2)
      (fkRectQuarterTurnSet R hH
          (fkRectDevelopedThreeByOneTorusCarrier R n) ∪
        fkRectDevelopedReflectionSet
          (fkRectQuarterTurnTorus R hH) center
          (fkRectQuarterTurnSet R hH
            (fkRectDevelopedThreeByOneTorusCarrier R n)))) :
    1 ≤ v.2.val ∧ v.2.val ≤ 24 * n + 4 := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectEvenRowTranslationVertexEquiv_apply]
  rcases hw with hw | hw
  · have hwrow := fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
      R n hn hwidth hheight hH hw
    rw [fkRectRowTranslate_eq_add_of_lt
      (fkRectQuarterTurnTorus R hH) (8 * n + 2) w.2 (by omega)]
    simp only [Fin.val_mk]
    omega
  · rcases hw with ⟨z, hz, rfl⟩
    have hzrow := fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
      R n hn hwidth hheight hH hz
    rw [fkRectDevelopedReflectionVertexEquiv_apply,
      fkRectRowTranslate_reflection_eq_sub
        (fkRectQuarterTurnTorus R hH) (8 * n + 2) center z.2
        (by omega) (by omega)]
    simp only [Fin.val_mk]
    omega



theorem fkRectCritical_developedThreeByOne_exists_orientedEvenRowBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    let hH : 4 < R.height := by omega
    Nonempty (FKRectOrientedEvenRowBlock R q n) ∨
      Nonempty (FKRectOrientedEvenRowBlock
        (fkRectQuarterTurnTorus R hH) q n) := by
  dsimp only
  let hH : 4 < R.height := by omega
  obtain ⟨p, hp, haxis⟩ :=
    fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge
      R n hn hwidth hheight hq
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  rcases haxis with horiginal | hturned
  · left
    constructor
    apply fkRectOrientedEvenRowBlockOfReflectedCarrier
      R q n S x y
    · have hrow : (n : Int) ≤
          2 * |(y.1.2.val : Int) - x.1.2.val| := by
        simpa [x, y] using horiginal.1
      exact hrow.trans (by omega)
    · constructor
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth hheight x.2).trans (by omega)
      · exact (fkRectDevelopedThreeByOneTorusCarrier_row_bounds
          R n hwidth hheight y.2).trans (by omega)
    · exact (fkRectDevelopedReflectedEndpointLower_pos hq n).le
    · exact horiginal.2
    · intro v hv
      exact (fkRectDevelopedThreeByOne_reflectedUnion_column_bounds
        R n hn hwidth hheight y.1.2.val hv).2
  · right
    constructor
    let ST := fkRectQuarterTurnSet R hH S
    let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
    let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
    apply fkRectOrientedEvenRowBlockOfReflectedCarrier
      (fkRectQuarterTurnTorus R hH) q n ST xT yT
    · exact hturned.1
    · constructor
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth hheight hH xT.2
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth hheight hH yT.2
    · exact (fkRectDevelopedReflectedEndpointLower_pos hq n).le
    · exact hturned.2
    · intro v hv
      exact (fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds
        R n hwidth hheight hH yT.1.2.val hv).trans (by omega)



theorem fkRectCritical_developedThreeByOne_exists_positiveRowOrientedBlock
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 12 * n + 2 < R.width)
    (hheight : 12 * n + 2 < R.height)
    {q : Real} (hq : 1 ≤ q) :
    let hH : 4 < R.height := by omega
    Nonempty (FKRectPositiveRowOrientedBlock R q n) ∨
      Nonempty (FKRectPositiveRowOrientedBlock
        (fkRectQuarterTurnTorus R hH) q n) := by
  dsimp only
  let hH : 4 < R.height := by omega
  have hwidth' : 4 * n < R.width := by omega
  have hheight' : 4 * n < R.height := by omega
  obtain ⟨p, hp, haxis⟩ :=
    fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge
      R n hn hwidth' hheight' hq
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  rcases haxis with horiginal | hturned
  · left
    have hspan : (n : Int) ≤
        2 * |(y.1.2.val : Int) - x.1.2.val| + 2 := by
      have hspan' : (n : Int) ≤
          2 * |(y.1.2.val : Int) - x.1.2.val| := by
        simpa [x, y] using horiginal.1
      exact hspan'.trans (by omega)
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
        (fkRectDevelopedReflectedEndpointLower_pos hq n).le
        horiginal.2 hcolumns
    have hoffset : Even (4 * n + 2) := by
      rw [show 4 * n + 2 = 2 * (2 * n + 1) by omega]
      exact even_two_mul _
    let B := B0.translate (4 * n + 2) hoffset
    refine ⟨⟨B, ?_⟩⟩
    intro v hv
    have hcenter : y.1.2.val ≤ 4 * n :=
      fkRectDevelopedThreeByOneTorusCarrier_row_bounds
        R n hwidth' hheight' y.2
    have hv' : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2)
        (fkRectDevelopedThreeByOneTorusCarrier R n ∪
          fkRectDevelopedReflectionSet R y.1.2.val
            (fkRectDevelopedThreeByOneTorusCarrier R n)) := by
      simpa [B, B0, S] using hv
    have hb :=
      fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds
        R n hwidth' hheight y.1.2.val hcenter hv'
    exact ⟨hb.1, hb.2.trans (by omega)⟩
  · right
    let ST := fkRectQuarterTurnSet R hH S
    let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
    let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
    have hrows : xT.1.2.val ≤ 8 * n + 1 ∧
        yT.1.2.val ≤ 8 * n + 1 := by
      constructor
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth' hheight' hH xT.2
      · exact fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds
          R n hn hwidth' hheight' hH yT.2
    have hcolumns : ∀ v ∈
        ST ∪ fkRectDevelopedReflectionSet
          (fkRectQuarterTurnTorus R hH) yT.1.2.val ST,
        v.1.val ≤ 4 * n := by
      intro v hv
      exact (fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds
        R n hwidth' hheight' hH yT.1.2.val hv).trans (by omega)
    let B0 := fkRectOrientedEvenRowBlockOfReflectedCarrier
      (fkRectQuarterTurnTorus R hH) q n ST xT yT
        hturned.1 hrows
        (fkRectDevelopedReflectedEndpointLower_pos hq n).le
        hturned.2 hcolumns
    have hoffset : Even (8 * n + 2) := by
      rw [show 8 * n + 2 = 2 * (4 * n + 1) by omega]
      exact even_two_mul _
    let B := B0.translate (8 * n + 2) hoffset
    refine ⟨⟨B, ?_⟩⟩
    intro v hv
    apply fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds
      R n hn hwidth' hheight' hH (by simp; omega)
        yT.1.2.val hrows.2
    simpa [B, B0] using hv

end

end StatMech.FrontierD
