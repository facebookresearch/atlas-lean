/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardRawNonbacktrackingSimple











namespace StatMech.FrontierA

open Set

structure KWAdaptivePatchedData
    {n M : ℕ} [NeZero n] [NeZero M]
    (polygon : KWFiniteSimplePolygon n) where
  data : KWStairParameterData (S := M + 2) polygon
  beta : ℝ
  alpha : Fin n → ℝ
  hM : 2 ≤ M
  hbeta : 0 < beta
  halpha : ∀ i, 0 < alpha i
  hsum : ∀ i, alpha i + beta < 1
  parameter_one : ∀ i,
    data.parameter i (0 : Fin (M + 2)).succ = beta
  parameter_penultimate : ∀ i,
    data.parameter i (Fin.last (M + 1)).castSucc = 1 - alpha (i + 1)
  connector : ∀ i : Fin n, KWAdaptiveConnectorData
    (alpha i * (-polygon.edgeVector (i - 1)))
    (beta * polygon.edgeVector i)

noncomputable def kwAdaptivePatchedData
    {n M : ℕ} [NeZero n] [NeZero M] (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 2 ≤ M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (hconnector : ∀ i : Fin n, Nonempty (KWAdaptiveConnectorData
      (alpha i * (-polygon.edgeVector (i - 1)))
      (beta * polygon.edgeVector i))) :
    KWAdaptivePatchedData (M := M) polygon where
  data := kwEndpointParameterData polygon M beta alpha (by omega) hbeta halpha hsum
  beta := beta
  alpha := alpha
  hM := hM
  hbeta := hbeta
  halpha := halpha
  hsum := hsum
  parameter_one := kwEndpointParameterData_parameter_one
    polygon beta alpha (by omega) hbeta halpha hsum
  parameter_penultimate := kwEndpointParameterData_parameter_penultimate
    polygon beta alpha (by omega) hbeta halpha hsum
  connector i := (hconnector i).some

noncomputable def KWAdaptivePatchedData.incomingPort
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  patch.data.base i (Fin.last (M + 1)).castSucc

noncomputable def KWAdaptivePatchedData.outgoingPort
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  patch.data.base i (0 : Fin (M + 2)).succ

noncomputable def KWAdaptivePatchedData.connectorCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  polygon.vertex i + (patch.connector i).corner

noncomputable def KWAdaptivePatchedData.pathBase
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.incomingPort i)
    (fun q : Fin M ↦ patch.data.base i q.succ.castSucc.castSucc) k



def KWAdaptivePatchedData.connectorUsesVerticalFirst
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : Prop :=
  (patch.connector i).corner = kwVHConnectorCorner
    (patch.alpha i * (-polygon.edgeVector (i - 1)))
    (patch.beta * polygon.edgeVector i)

noncomputable instance KWAdaptivePatchedData.connectorUsesVerticalFirst_decidable
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    Decidable (patch.connectorUsesVerticalFirst i) := Classical.dec _



def KWAdaptivePatchedData.lastMiddleIndex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) : Fin M :=
  ⟨M - 1, by have := patch.hM; omega⟩

@[simp] theorem KWAdaptivePatchedData.lastMiddleIndex_val
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    patch.lastMiddleIndex.val = M - 1 := rfl



def KWAdaptivePatchedData.sliceUsesVerticalFirst
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
  (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : Prop :=
  (q = 0 ∧ patch.connectorUsesVerticalFirst i) ∨
    (q = patch.lastMiddleIndex ∧
      patch.connectorUsesVerticalFirst (i + 1))

noncomputable instance KWAdaptivePatchedData.sliceUsesVerticalFirst_decidable
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : Decidable (patch.sliceUsesVerticalFirst i q) :=
  Classical.dec _


noncomputable def KWAdaptivePatchedData.middleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) : ℂ :=
  if patch.sliceUsesVerticalFirst i q then
    patch.data.base i q.succ.castSucc.castSucc +
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
          kwVerticalPart (polygon.edgeVector i)
  else
    patch.data.corner i q.succ.castSucc

noncomputable def KWAdaptivePatchedData.pathCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.connectorCorner (i + 1))
    (fun q : Fin M ↦ patch.middleCorner i q) k

@[simp] theorem KWAdaptivePatchedData.pathBase_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.castSucc =
      patch.data.base i q.succ.castSucc.castSucc := by
  simp [KWAdaptivePatchedData.pathBase]

@[simp] theorem KWAdaptivePatchedData.pathBase_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.pathBase i (Fin.last M) = patch.incomingPort i := by
  simp [KWAdaptivePatchedData.pathBase]

@[simp] theorem KWAdaptivePatchedData.pathCorner_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.pathCorner i q.castSucc =
      patch.middleCorner i q := by
  simp [KWAdaptivePatchedData.pathCorner]

@[simp] theorem KWAdaptivePatchedData.pathCorner_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.pathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
  simp [KWAdaptivePatchedData.pathCorner]

noncomputable def KWAdaptivePatchedData.localVertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (l : Fin (2 * (M + 1))) : ℂ :=
  if l.val % 2 = 0 then
    patch.pathBase i (kwStairSliceIndex l)
  else
    patch.pathCorner i (kwStairSliceIndex l)

@[simp] theorem KWAdaptivePatchedData.localVertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.localVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWAdaptivePatchedData.localVertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.localVertex i (kwStairOddLocal k) = patch.pathCorner i k := by
  simp [KWAdaptivePatchedData.localVertex, kwStairSliceIndex_odd]

noncomputable def KWAdaptivePatchedData.vertex
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) :
    Fin (n * (2 * (M + 1))) → ℂ :=
  fun j ↦ patch.localVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

@[simp] theorem KWAdaptivePatchedData.vertex_even
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.vertex (kwStairEvenIndex i k) = patch.pathBase i k := by
  simp [KWAdaptivePatchedData.vertex, kwStairEvenIndex]

@[simp] theorem KWAdaptivePatchedData.vertex_odd
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) :
    patch.vertex (kwStairOddIndex i k) = patch.pathCorner i k := by
  simp [KWAdaptivePatchedData.vertex, kwStairOddIndex]

theorem KWAdaptivePatchedData.incomingPort_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.incomingPort i = polygon.vertex (i + 1) +
      patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  unfold KWAdaptivePatchedData.incomingPort
  rw [patch.data.base_penultimate_eq_incomingPatchBase i
    (patch.alpha (i + 1)) (patch.parameter_penultimate i)]
  rfl

theorem KWAdaptivePatchedData.outgoingPort_eq
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    patch.outgoingPort i = polygon.vertex i +
      patch.beta * polygon.edgeVector i := by
  unfold KWAdaptivePatchedData.outgoingPort
  rw [patch.data.base_one_eq_outgoingPatchEnd i patch.beta
    (patch.parameter_one i)]
  rfl

theorem KWAdaptivePatchedData.middleCorner_sub_base
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.middleCorner i q -
        patch.data.base i q.succ.castSucc.castSucc =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwVerticalPart (polygon.edgeVector i)
        else kwHorizontalPart (polygon.edgeVector i)) := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp [KWAdaptivePatchedData.middleCorner, hv]
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_false]
    exact patch.data.corner_sub_base i q.succ.castSucc

theorem KWAdaptivePatchedData.base_succ_sub_middleCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    patch.data.base i q.succ.castSucc.succ - patch.middleCorner i q =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwHorizontalPart (polygon.edgeVector i)
        else kwVerticalPart (polygon.edgeVector i)) := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_true]
    have hbase : patch.data.base i q.succ.castSucc.succ -
        patch.data.base i q.succ.castSucc.castSucc =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
          polygon.edgeVector i := by
      unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
      exact lineMap_sub_lineMap _ _ _ _
    rw [show patch.data.base i q.succ.castSucc.succ -
          (patch.data.base i q.succ.castSucc.castSucc +
            (patch.data.parameter i q.succ.castSucc.succ -
              patch.data.parameter i q.succ.castSucc.castSucc) *
                kwVerticalPart (polygon.edgeVector i)) =
        (patch.data.base i q.succ.castSucc.succ -
          patch.data.base i q.succ.castSucc.castSucc) -
            (patch.data.parameter i q.succ.castSucc.succ -
              patch.data.parameter i q.succ.castSucc.castSucc) *
                kwVerticalPart (polygon.edgeVector i) by ring,
      hbase]
    rw [← mul_sub]
    have hdecomp := kwHorizontalPart_add_verticalPart
      (polygon.edgeVector i)
    have : polygon.edgeVector i - kwVerticalPart (polygon.edgeVector i) =
        kwHorizontalPart (polygon.edgeVector i) := by
      nth_rewrite 1 [← hdecomp]
      ring
    rw [this]
  · simp only [KWAdaptivePatchedData.middleCorner, hv, if_false]
    exact patch.data.base_succ_sub_corner i q.succ.castSucc


theorem KWAdaptivePatchedData.rawEdge_even_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.vertex (kwStairEvenIndex i q.castSucc) =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwVerticalPart (polygon.edgeVector i)
        else kwHorizontalPart (polygon.edgeVector i)) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathBase_castSucc, patch.pathCorner_castSucc]
  exact patch.middleCorner_sub_base i q


theorem KWAdaptivePatchedData.rawEdge_odd_castSucc
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    kwRawEdge patch.vertex (kwStairOddIndex i q.castSucc) =
      (patch.data.parameter i q.succ.castSucc.succ -
        patch.data.parameter i q.succ.castSucc.castSucc) *
        (if patch.sliceUsesVerticalFirst i q then
          kwHorizontalPart (polygon.edgeVector i)
        else kwVerticalPart (polygon.edgeVector i)) := by
  unfold kwRawEdge
  rw [kwStairOddIndex_castSucc_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathCorner_castSucc]
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
  exact patch.base_succ_sub_middleCorner i q


theorem KWAdaptivePatchedData.rawEdge_even_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    kwRawEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) =
      (patch.connector (i + 1)).corner -
        patch.alpha (i + 1) * (-polygon.edgeVector i) := by
  unfold kwRawEdge
  rw [kwStairEvenIndex_add_one, patch.vertex_even, patch.vertex_odd,
    patch.pathBase_last, patch.pathCorner_last, patch.incomingPort_eq]
  unfold KWAdaptivePatchedData.connectorCorner
  ring


theorem KWAdaptivePatchedData.rawEdge_odd_last
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) :
    kwRawEdge patch.vertex (kwStairOddIndex i (Fin.last M)) =
      patch.beta * polygon.edgeVector (i + 1) -
        (patch.connector (i + 1)).corner := by
  unfold kwRawEdge
  rw [kwStairOddIndex_last_add_one, patch.vertex_odd, patch.vertex_even,
    patch.pathCorner_last]
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
