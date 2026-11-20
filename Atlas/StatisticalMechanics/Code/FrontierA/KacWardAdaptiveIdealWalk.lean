/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveConnectorScales










namespace StatMech.FrontierA

noncomputable def KWAdaptivePatchedData.idealMiddleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℂ :=
  patch.data.base i q.succ.castSucc.castSucc +
    (1 / 2 : ℝ) *
      (patch.data.base i q.succ.castSucc.succ -
        patch.data.base i q.succ.castSucc.castSucc)

noncomputable def KWAdaptivePatchedData.idealPathCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.connectorCorner (i + 1))
    (fun q : Fin M ↦ patch.idealMiddleCorner i q) k

@[simp] theorem KWAdaptivePatchedData.idealPathCorner_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealPathCorner i q.castSucc = patch.idealMiddleCorner i q := by
  simp [KWAdaptivePatchedData.idealPathCorner]

@[simp] theorem KWAdaptivePatchedData.idealPathCorner_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.idealPathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
  simp [KWAdaptivePatchedData.idealPathCorner]

noncomputable def KWAdaptivePatchedData.idealLocalVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (l : Fin (2 * (M + 1))) : ℂ :=
  if l.val % 2 = 0 then
    patch.pathBase i (kwStairSliceIndex l)
  else
    patch.idealPathCorner i (kwStairSliceIndex l)

@[simp] theorem KWAdaptivePatchedData.idealLocalVertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealLocalVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.idealLocalVertex, kwStairSliceIndex_even]

@[simp] theorem KWAdaptivePatchedData.idealLocalVertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealLocalVertex i (kwStairOddLocal k) =
      patch.idealPathCorner i k := by
  simp [KWAdaptivePatchedData.idealLocalVertex, kwStairSliceIndex_odd]

noncomputable def KWAdaptivePatchedData.idealVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    Fin (n * (2 * (M + 1))) → ℂ :=
  fun j ↦ patch.idealLocalVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

@[simp] theorem KWAdaptivePatchedData.idealVertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealVertex (kwStairEvenIndex i k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.idealVertex, kwStairEvenIndex]

@[simp] theorem KWAdaptivePatchedData.idealVertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.idealVertex (kwStairOddIndex i k) =
      patch.idealPathCorner i k := by
  simp [KWAdaptivePatchedData.idealVertex, kwStairOddIndex]

theorem KWAdaptivePatchedData.idealMiddleCorner_sub_base
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.idealMiddleCorner i q -
        patch.data.base i q.succ.castSucc.castSucc =
      (1 / 2 : ℝ) *
        (patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            polygon.edgeVector i := by
  rw [KWAdaptivePatchedData.idealMiddleCorner]
  have hbase := lineMap_sub_lineMap (polygon.vertex i)
    (polygon.vertex (i + 1))
    (patch.data.parameter i q.succ.castSucc.castSucc)
    (patch.data.parameter i q.succ.castSucc.succ)
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [hbase]
  ring_nf

theorem KWAdaptivePatchedData.base_succ_sub_idealMiddleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.data.base i q.succ.castSucc.succ -
        patch.idealMiddleCorner i q =
      (1 / 2 : ℝ) *
        (patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            polygon.edgeVector i := by
  rw [show patch.data.base i q.succ.castSucc.succ -
        patch.idealMiddleCorner i q =
      (patch.data.base i q.succ.castSucc.succ -
        patch.data.base i q.succ.castSucc.castSucc) -
      (patch.idealMiddleCorner i q -
        patch.data.base i q.succ.castSucc.castSucc) by ring,
    patch.idealMiddleCorner_sub_base]
  have hbase := lineMap_sub_lineMap (polygon.vertex i)
    (polygon.vertex (i + 1))
    (patch.data.parameter i q.succ.castSucc.castSucc)
    (patch.data.parameter i q.succ.castSucc.succ)
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [hbase]
  norm_num [div_eq_mul_inv]
  ring

theorem KWAdaptivePatchedData.idealRawEdge_even_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) =
      (1 / 2 : ℝ) *
        (patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            polygon.edgeVector i := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.idealVertex_even,
    patch.idealVertex_odd, patch.pathBase_castSucc,
    patch.idealPathCorner_castSucc]
  exact patch.idealMiddleCorner_sub_base i q

theorem KWAdaptivePatchedData.idealRawEdge_odd_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.idealVertex (kwStairOddIndex i q.castSucc) =
      (1 / 2 : ℝ) *
        (patch.data.parameter i q.succ.castSucc.succ -
          patch.data.parameter i q.succ.castSucc.castSucc) *
            polygon.edgeVector i := by
  unfold kwRawEdge
  rw [kwStairOddIndex_castSucc_add_one, patch.idealVertex_even,
    patch.idealVertex_odd, patch.idealPathCorner_castSucc]
  have hbase : patch.pathBase i q.succ =
      patch.data.base i q.succ.castSucc.succ := by
    by_cases hq : q = patch.lastMiddleIndex
    · subst q
      have hlast : patch.lastMiddleIndex.succ = Fin.last M := by
        apply Fin.ext
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        have := patch.hM
        omega
      rw [hlast, patch.pathBase_last]
      unfold KWAdaptivePatchedData.incomingPort
      congr 2
    · have hsucc_ne : q.succ ≠ Fin.last M := by
        intro h
        apply hq
        apply Fin.ext
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hval
        simp [KWAdaptivePatchedData.lastMiddleIndex]
        omega
      obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hsucc_ne
      rw [← hr, patch.pathBase_castSucc]
      congr 2
  rw [hbase]
  exact patch.base_succ_sub_idealMiddleCorner i q

theorem KWAdaptivePatchedData.idealRawEdge_even_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) =
      (patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.idealVertex_even,
    patch.idealVertex_odd, patch.pathBase_last,
    patch.idealPathCorner_last, patch.incomingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  ring

theorem KWAdaptivePatchedData.idealRawEdge_odd_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    kwRawEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) =
      patch.beta * polygon.edgeVector (i + 1) -
        (patch.connector (i + 1)).corner := by
  unfold kwRawEdge
  rw [kwStairOddIndex_last_add_one, patch.idealVertex_odd,
    patch.idealVertex_even, patch.idealPathCorner_last]
  have hzero : (0 : Fin (M + 1)) = (0 : Fin M).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero, patch.pathBase_castSucc]
  have hport : patch.data.base (i + 1)
      (0 : Fin M).succ.castSucc.castSucc = patch.outgoingPort (i + 1) := by
    unfold KWAdaptivePatchedData.outgoingPort
    congr 2
  rw [hport, patch.outgoingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  ring

end StatMech.FrontierA
