/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAdaptiveActualCarrierContainment





namespace StatMech.FrontierA

open scoped NNReal

private theorem exists_uniform_radius_finset
    {ι : Type*} (s : Finset ι) (Q : ι → ℝ≥0 → Prop)
    (hQ : ∀ i ∈ s, ∃ r : ℝ≥0, 0 < r ∧ Q i r)
    (hmono : ∀ i ∈ s, ∀ {r r' : ℝ≥0}, r' ≤ r → Q i r → Q i r') :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ i ∈ s, Q i r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert j s hj ih =>
      obtain ⟨rj, hrj, hQj⟩ := hQ j (by simp)
      obtain ⟨rs, hrs, hQs⟩ := ih
        (fun i hi ↦ hQ i (by simp [hi]))
        (fun i hi r r' hle h ↦ hmono i (by simp [hi]) hle h)
      refine ⟨min rj rs, lt_min hrj hrs, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact hmono _ (by simp) (min_le_left _ _) hQj
      · exact hmono i (by simp [his]) (min_le_right _ _) (hQs i his)

theorem KWAdaptivePatchedData.exists_uniform_remoteParameter_dist_separation
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
    ∃ sep : ℝ≥0, 0 < sep ∧
      ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y := by
  classical
  let Q : (Fin n × Bool) → ℝ≥0 → Prop := fun p sep ↦
    ∀ x ∈ (if p.2 then
        kwRawClosedEdge patch.idealVertex
          (kwStairEvenIndex p.1 (Fin.last M))
      else kwRawClosedEdge patch.idealVertex
        (kwStairOddIndex p.1 (Fin.last M))),
    ∀ y ∈ (if p.2 then patch.outgoingParameterCarrier (p.1 + 1)
      else patch.incomingParameterCarrier p.1),
      (sep : ℝ) < dist x y
  have hQ : ∀ p ∈ (Finset.univ : Finset (Fin n × Bool)),
      ∃ sep : ℝ≥0, 0 < sep ∧ Q p sep := by
    intro p _hp
    exact patch.exists_remoteParameter_dist_separation
      hcross hcoords p.1 p.2
  have hmono : ∀ p ∈ (Finset.univ : Finset (Fin n × Bool)),
      ∀ {r r' : ℝ≥0}, r' ≤ r → Q p r → Q p r' := by
    intro p _hp r r' hle h x hx y hy
    exact_mod_cast (show (r' : ℝ) ≤ r from by exact_mod_cast hle).trans_lt
      (h x hx y hy)
  obtain ⟨sep, hsep, hall⟩ := exists_uniform_radius_finset
    (Finset.univ : Finset (Fin n × Bool)) Q hQ hmono
  refine ⟨sep, hsep, ?_⟩
  intro i first
  exact hall (i, first) (Finset.mem_univ _)

theorem KWSmallAdaptiveConnectorScales.exists_uniform_remoteParameter_radius
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {R : ℝ} (scales : KWSmallAdaptiveConnectorScales polygon R)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
    ∃ sep : ℝ≥0, 0 < sep ∧
      ∀ {M : ℕ} [NeZero M] (hM : 2 ≤ M),
      let patch := scales.toPatchedData hM
      ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y := by
  let patchTwo := scales.toPatchedData (M := 2) (by omega)
  obtain ⟨sep, hsep, hall⟩ :=
    patchTwo.exists_uniform_remoteParameter_dist_separation hcross hcoords
  refine ⟨sep, hsep, ?_⟩
  intro M inst hM
  dsimp only
  intro i first
  have h := hall i first
  cases first with
  | false =>
      simpa only [Bool.false_eq_true, if_false,
        KWAdaptivePatchedData.idealConnectorSecondClosedEdge_eq,
        KWAdaptivePatchedData.incomingPort_eq,
        KWAdaptivePatchedData.outgoingPort_eq,
        KWAdaptivePatchedData.connectorCorner,
        KWAdaptivePatchedData.incomingParameterCarrier,
        KWSmallAdaptiveConnectorScales.toPatchedData, patchTwo] using h
  | true =>
      simpa only [if_true,
        KWAdaptivePatchedData.idealConnectorFirstClosedEdge_eq,
        KWAdaptivePatchedData.incomingPort_eq,
        KWAdaptivePatchedData.outgoingPort_eq,
        KWAdaptivePatchedData.connectorCorner,
        KWAdaptivePatchedData.outgoingParameterCarrier,
        KWSmallAdaptiveConnectorScales.toPatchedData, patchTwo] using h

theorem KWAdaptivePatchedData.firstConnector_disjoint_outgoingMiddle_of_fine
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hsep : ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep)
    (i : Fin n) (q : Fin M) (even : Bool) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)))
      (patch.middleClosedEdge (i + 1) q even) := by
  apply patch.actualConnectorMiddle_disjoint_of_carrier r sep hr hfine
    (kwStairEvenIndex i (Fin.last M)) (i + 1) q even
    (patch.outgoingParameterCarrier (i + 1))
    (patch.idealMiddle_subset_outgoingParameterCarrier (i + 1) q even)
    (by simpa only [if_true] using hsep i true) hsmall

theorem KWAdaptivePatchedData.secondConnector_disjoint_incomingMiddle_of_fine
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hsep : ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep)
    (i : Fin n) (q : Fin M) (even : Bool) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.middleClosedEdge i q even) := by
  apply patch.actualConnectorMiddle_disjoint_of_carrier r sep hr hfine
    (kwStairOddIndex i (Fin.last M)) i q even
    (patch.incomingParameterCarrier i)
    (patch.idealMiddle_subset_incomingParameterCarrier i q even)
    (by simpa only [Bool.false_eq_true, if_false] using hsep i false) hsmall

theorem KWAdaptivePatchedData.connector_disjoint_incomingMiddle_of_fine
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hsep : ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ∪
        kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.middleClosedEdge i q even) := by
  apply Disjoint.union_left
  · exact patch.firstConnector_disjoint_incomingMiddle
      hcoords i q even hnotLast
  · exact patch.secondConnector_disjoint_incomingMiddle_of_fine
      r sep hr hfine hsep hsmall i q even

theorem KWAdaptivePatchedData.connector_disjoint_outgoingMiddle_of_fine
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (r sep : ℝ≥0) (hr : 0 < r)
    (hfine : KWEndpointInteriorMeshWithin patch.data r)
    (hsep : ∀ i : Fin n, ∀ first : Bool,
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.idealVertex
            (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.idealVertex
          (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1)
        else patch.incomingParameterCarrier i),
        (sep : ℝ) < dist x y)
    (hsmall : 4 * (r : ℝ) < sep)
    (i : Fin n) (q : Fin M) (even : Bool)
    (hnotFirst : q ≠ 0 ∨ even = false) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ∪
        kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.middleClosedEdge (i + 1) q even) := by
  apply Disjoint.union_left
  · exact patch.firstConnector_disjoint_outgoingMiddle_of_fine
      r sep hr hfine hsep hsmall i q even
  · exact patch.secondConnector_disjoint_outgoingMiddle
      hcoords i q even hnotFirst

theorem KWSmallAdaptiveConnectorScales.exists_interiorMesh_patch
    {n : ℕ} [NeZero n] {polygon : KWFiniteSimplePolygon n}
    {R : ℝ} (scales : KWSmallAdaptiveConnectorScales polygon R)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ M : ℕ, ∃ hM : 2 ≤ M,
      letI : NeZero M := ⟨by omega⟩
      KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  let M : ℕ := N + 2
  have hM : 2 ≤ M := by simp [M]
  refine ⟨M, hM, ?_⟩
  letI : NeZero M := ⟨by omega⟩
  intro i k hk0 hklast
  have hstep := kwEndpointParameter_middle_step_le_inv
    M scales.beta (scales.alpha (i + 1)) (by omega)
      scales.hbeta.le (scales.halpha (i + 1)).le k hk0 hklast
  have hinv : (M : ℝ)⁻¹ ≤ (N + 1 : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast (show N + 1 ≤ M by simp [M])
  calc
    ((scales.toPatchedData hM).data.parameter i k.succ -
          (scales.toPatchedData hM).data.parameter i k.castSucc) *
        ‖polygon.edgeVector i‖ ≤
      (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ ≤ (N + 1 : ℝ)⁻¹ * ‖polygon.edgeVector i‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ = ‖polygon.edgeVector i‖ / (N + 1 : ℝ) := by
      rw [div_eq_mul_inv, mul_comm]
    _ < r := hmesh i

end StatMech.FrontierA
