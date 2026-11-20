/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardShearPhaseHomotopy










namespace StatMech.FrontierA



def KWGenericCoordinatePolygonPhaseSign : Prop :=
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n),
    (∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) →
    (∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) →
    kwVectorPhaseCycle polygon.edgeList = -1




theorem kwFiniteSimplePolygonPhaseSign_of_genericCoordinate
    (hgeneric : KWGenericCoordinatePolygonPhaseSign) :
    KWFiniteSimplePolygonPhaseSign := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro inst polygon
      have hnthree := polygon.three_le
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 :=
        ⟨n - 3, by omega⟩
      by_cases hm0 : m = 0
      · subst m
        exact polygon.earDecomposition_three.phaseCycle_eq_neg_one
      have hm : 1 ≤ m := by omega
      by_cases hcol : ∃ i : Fin (m + 3), Collinear ℝ
          ({polygon.vertex i, polygon.vertex (i + 1),
            polygon.vertex (i + 2)} : Set ℂ)
      · obtain ⟨r, hsimple, hphase⟩ :=
          polygon.exists_removable_of_exists_collinear hm hcol
        let rotated := polygon.rotate r
        have hreduced : kwVectorPhaseCycle
            (rotated.removeVertexOne hm hsimple).edgeList = -1 := by
          exact ih (m + 2) (by omega)
            (rotated.removeVertexOne hm hsimple)
        calc
          kwVectorPhaseCycle polygon.edgeList =
              kwVectorPhaseCycle rotated.edgeList := by
            change kwVectorPhaseCycle polygon.edgeList =
              kwVectorPhaseCycle (polygon.rotate r).edgeList
            rw [polygon.rotate_edgeList, kwVectorPhaseCycle_rotate]
          _ = kwVectorPhaseCycle
                (rotated.removeVertexOne hm hsimple).edgeList :=
            rotated.phaseCycle_removeVertexOne hm hsimple hphase
          _ = -1 := hreduced
      · have hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
            ({polygon.vertex i, polygon.vertex (i + 1),
              polygon.vertex (i + 2)} : Set ℂ) := by
          simpa only [not_exists] using hcol
        obtain ⟨tx, ty, hcoords⟩ := polygon.exists_generic_shear
        let e := kwDoubleShearLinearEquiv tx ty 1
        let transformed := polygon.mapLinearEquiv e
        have hcross (i : Fin (m + 3)) :
            kwComplexCross (transformed.edgeVector i)
                (transformed.edgeVector (i + 1)) ≠ 0 := by
          have horiginal :=
            polygon.edge_cross_ne_zero_of_not_collinear hnoncollinear i
          simpa only [transformed, e,
            KWFiniteSimplePolygon.mapLinearEquiv_edgeVector,
            kwDoubleShearLinearEquiv_one,
            kwComplexCross_shearY, kwComplexCross_shearX] using horiginal
        have hcoords' (i : Fin (m + 3)) :
            (transformed.edgeVector i).re ≠ 0 ∧
              (transformed.edgeVector i).im ≠ 0 := by
          simpa only [transformed, e,
            KWFiniteSimplePolygon.mapLinearEquiv_edgeVector,
            kwDoubleShearLinearEquiv_one] using hcoords i
        calc
          kwVectorPhaseCycle polygon.edgeList =
              kwVectorPhaseCycle transformed.edgeList := by
            simpa only [transformed, e] using
              polygon.phaseCycle_mapDoubleShear tx ty
          _ = -1 := hgeneric transformed hcross hcoords'

end StatMech.FrontierA
