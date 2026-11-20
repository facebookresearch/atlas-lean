/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedEndpointRate
import Code.FrontierD.FKRectQuarterTurn



open Set

namespace StatMech.FrontierD

noncomputable section



def fkRectReflectedCarrierConnectionEvent
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) :
    Set R.Configuration :=
  let center := y.1.2.val
  let Sr := fkRectDevelopedReflectionSet R center S
  let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
  {omega | FKRectConnectedWithin R omega (S ∪ Sr)
    ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩}



theorem fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier
    (R : FKRectTorus) {q a : Real} (hq : 1 ≤ q)
    (S : Set R.Vertex) (x y : S)
    (ha : 0 ≤ a)
    (hlower : a ≤ fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega S x y}) :
    a ^ 2 ≤ fkRectCriticalEventMass R q
      (fkRectReflectedCarrierConnectionEvent R S x y) := by
  have hsq : a ^ 2 ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} ^ 2 :=
    pow_le_pow_left₀ ha hlower 2
  exact hsq.trans (by
    simpa [fkRectReflectedCarrierConnectionEvent] using
      (fkRectCritical_connectedWithinMass_sq_le_reflectedUnion
        R hq S x y))



theorem fkRectDevelopedThreeByOneTorusCarrier_row_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {v : R.Vertex} (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n) :
    v.2.val ≤ 4 * n := by
  rcases hv with ⟨z, rfl⟩
  have hz := z.2
  change z.1 ∈ StatMech.RSW.Box.rect
    0 (3 * (n : Int)) 0 n at hz
  rw [StatMech.RSW.Box.mem_rect] at hz
  have hrow := fkRectDevelopedThreeByOneVertex_row_val
    R n hwidth hheight z
  have hrow' :
      ((fkRectDevelopedSquareVertex R n z.1).2.val : Int) ≤ 4 * n := by
    omega
  exact_mod_cast hrow'



theorem fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectQuarterTurnSet R hH
      (fkRectDevelopedThreeByOneTorusCarrier R n)) :
    v.1.val ≤ 2 * n := by
  rcases hv with ⟨w, hw, rfl⟩
  rw [fkRectQuarterTurnVertexEquiv_apply,
    fkRectQuarterTurnVertex_fst_val]
  have hwrow := fkRectDevelopedThreeByOneTorusCarrier_row_bounds
    R n hwidth hheight hw
  omega



theorem fkRectQuarterTurn_developedThreeByOne_reflectedUnion_column_bounds
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (hH : 4 < R.height) (center : Nat)
    {v : (fkRectQuarterTurnTorus R hH).Vertex}
    (hv : v ∈ fkRectQuarterTurnSet R hH
          (fkRectDevelopedThreeByOneTorusCarrier R n) ∪
        fkRectDevelopedReflectionSet
          (fkRectQuarterTurnTorus R hH) center
          (fkRectQuarterTurnSet R hH
            (fkRectDevelopedThreeByOneTorusCarrier R n))) :
    v.1.val ≤ 2 * n := by
  rcases hv with hv | hv
  · exact fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds
      R n hwidth hheight hH hv
  · exact (fkRectDevelopedReflectionSet_column_bounds
      (fkRectQuarterTurnTorus R hH) center 0 (2 * n)
      (fkRectQuarterTurnSet R hH
        (fkRectDevelopedThreeByOneTorusCarrier R n))
      (fun w hw => ⟨Nat.zero_le _,
        fkRectQuarterTurn_developedThreeByOneCarrier_column_bounds
          R n hwidth hheight hH hw⟩) hv).2



theorem fkRectQuarterTurn_row_span_of_column_span
    (R : FKRectTorus) (hH : 4 < R.height) (n : Nat)
    (x y : R.Vertex)
    (hspan : (n : Int) ≤
      4 * |(y.1.val : Int) - x.1.val|) :
    (n : Int) ≤ 2 *
        |((fkRectQuarterTurnVertexEquiv R hH y).2.val : Int) -
          (fkRectQuarterTurnVertexEquiv R hH x).2.val| + 2 := by
  rw [fkRectQuarterTurnVertexEquiv_apply,
    fkRectQuarterTurnVertexEquiv_apply,
    fkRectQuarterTurnVertex_snd_val,
    fkRectQuarterTurnVertex_snd_val]
  have hxmod := Nat.mod_lt x.2.val (by norm_num : 0 < 2)
  have hymod := Nat.mod_lt y.2.val (by norm_num : 0 < 2)
  push_cast
  by_cases hd : 0 ≤ (y.1.val : Int) - x.1.val
  · rw [abs_of_nonneg hd] at hspan
    by_cases ht : 0 ≤
        (2 * (y.1.val : Int) + (y.2.val : Int) % 2) -
          (2 * (x.1.val : Int) + (x.2.val : Int) % 2)
    · rw [abs_of_nonneg ht]
      omega
    · rw [abs_of_nonpos (le_of_not_ge ht)]
      omega
  · rw [abs_of_nonpos (le_of_not_ge hd)] at hspan
    by_cases ht : 0 ≤
        (2 * (y.1.val : Int) + (y.2.val : Int) % 2) -
          (2 * (x.1.val : Int) + (x.2.val : Int) % 2)
    · rw [abs_of_nonneg ht]
      omega
    · rw [abs_of_nonpos (le_of_not_ge ht)]
      omega





theorem fkRectCritical_developedThreeByOne_exists_axisSelectedWindingBlock_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    let hH : 4 < R.height := by omega
    let RT := fkRectQuarterTurnTorus R hH
    ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n,
      let S := fkRectDevelopedThreeByOneTorusCarrier R n
      let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
      let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
      ((n : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| ∧
        fkRectDevelopedReflectedEndpointLower q n ≤
          fkRectCriticalEventMass R q
            (fkRectReflectedCarrierConnectionEvent R S x y)) ∨
      (let ST := fkRectQuarterTurnSet R hH S
       let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
       let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
       (n : Int) ≤ 2 * |(yT.1.2.val : Int) - xT.1.2.val| + 2 ∧
        fkRectDevelopedReflectedEndpointLower q n ≤
          fkRectCriticalEventMass RT q
            (fkRectReflectedCarrierConnectionEvent RT ST xT yT)) := by
  dsimp only
  let hH : 4 < R.height := by omega
  obtain ⟨p, hp, hlower, hspan⟩ :=
    fkRectCritical_developedThreeByOne_exists_carrierConnection_span_ge
      R n hn hwidth hheight hq
  refine ⟨p, hp, ?_⟩
  let S := fkRectDevelopedThreeByOneTorusCarrier R n
  let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1
  let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2
  let a : Real := 1 / (2 * (1 + q)) /
    (((3 * n + 1) ^ 2 : Nat) : Real)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hcarrier : a ≤ fkRectCriticalEventMass R q
      {omega | FKRectConnectedWithin R omega S x y} := by
    simpa [a, S, x, y,
      fkRectDevelopedThreeByOneCarrierConnectionEvent] using hlower
  rcases hspan with hrow | hcolumn
  · left
    refine ⟨hrow, ?_⟩
    simpa [fkRectDevelopedReflectedEndpointLower,
      fkRectDevelopedReflectedEndpointLowerOf, a, S, x, y] using
      (fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier
        R hq S x y ha hcarrier)
  · right
    let ST := fkRectQuarterTurnSet R hH S
    let xT : ST := fkRectQuarterTurnSetEquiv R hH S x
    let yT : ST := fkRectQuarterTurnSetEquiv R hH S y
    have hturnLower : a ≤
        fkRectCriticalEventMass (fkRectQuarterTurnTorus R hH) q
          {omega | FKRectConnectedWithin
            (fkRectQuarterTurnTorus R hH) omega ST xT yT} := by
      rw [show fkRectCriticalEventMass
          (fkRectQuarterTurnTorus R hH) q
            {omega | FKRectConnectedWithin
              (fkRectQuarterTurnTorus R hH) omega ST xT yT} =
          fkRectCriticalEventMass R q
            {omega | FKRectConnectedWithin R omega S x y} by
        simpa [ST, xT, yT] using
          (fkRectCritical_connectedWithinMass_quarterTurn
            R hH q S x y)]
      exact hcarrier
    refine ⟨fkRectQuarterTurn_row_span_of_column_span
      R hH n x.1 y.1 hcolumn, ?_⟩
    simpa [fkRectDevelopedReflectedEndpointLower,
      fkRectDevelopedReflectedEndpointLowerOf, a, ST, xT, yT] using
      (fkRectCritical_connectedWithinLower_sq_le_reflectedCarrier
        (fkRectQuarterTurnTorus R hH) hq ST xT yT ha hturnLower)

end

end StatMech.FrontierD
