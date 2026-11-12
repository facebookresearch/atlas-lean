/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordEndpointOrderReverse









namespace StatMech.FrontierA


theorem KWFiniteSimplePolygon.phaseCycle_eq_neg_one_four
    (polygon : KWFiniteSimplePolygon 4) :
    kwVectorPhaseCycle polygon.edgeList = -1 := by
  by_cases hcol : ∃ i : Fin 4, Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)
  · obtain ⟨r, hsimple, hphase⟩ :=
      polygon.exists_removable_of_exists_collinear (by omega) hcol
    let rotated := polygon.rotate r
    have hreduced : kwVectorPhaseCycle
        (rotated.removeVertexOne (by omega) hsimple).edgeList = -1 :=
      (rotated.removeVertexOne (by omega) hsimple).earDecomposition_three
        |>.phaseCycle_eq_neg_one
    calc
      kwVectorPhaseCycle polygon.edgeList =
          kwVectorPhaseCycle rotated.edgeList := by
        change kwVectorPhaseCycle polygon.edgeList =
          kwVectorPhaseCycle (polygon.rotate r).edgeList
        rw [polygon.rotate_edgeList, kwVectorPhaseCycle_rotate]
      _ = kwVectorPhaseCycle
            (rotated.removeVertexOne (by omega) hsimple).edgeList :=
        rotated.phaseCycle_removeVertexOne (by omega) hsimple hphase
      _ = -1 := hreduced
  · have hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ) := by
      simpa only [not_exists] using hcol
    obtain ⟨r, hear⟩ :=
      polygon.exists_rotated_vertexOneGeometricEar_four hnoncollinear
    let rotated := polygon.rotate r
    obtain ⟨hsimple, hphase⟩ :=
      rotated.removable_of_geometricEar (by omega) hear
    have hreduced : kwVectorPhaseCycle
        (rotated.removeVertexOne (by omega) hsimple).edgeList = -1 :=
      (rotated.removeVertexOne (by omega) hsimple).earDecomposition_three
        |>.phaseCycle_eq_neg_one
    calc
      kwVectorPhaseCycle polygon.edgeList =
          kwVectorPhaseCycle rotated.edgeList := by
        change kwVectorPhaseCycle polygon.edgeList =
          kwVectorPhaseCycle (polygon.rotate r).edgeList
        rw [polygon.rotate_edgeList, kwVectorPhaseCycle_rotate]
      _ = kwVectorPhaseCycle
            (rotated.removeVertexOne (by omega) hsimple).edgeList :=
        rotated.phaseCycle_removeVertexOne (by omega) hsimple hphase
      _ = -1 := hreduced



theorem KWFiniteSimplePolygon.cleanChordEndpointOrder_four
    (polygon : KWFiniteSimplePolygon 4) (j : Fin 4)
    (hj : 2 ≤ j.val) (hjupper : j.val + 2 ≤ 4)
    (hclean : polygon.ChordIsClean 0 j) :
    polygon.CleanChordEndpointOrder j (by omega) := by
  have hjval : j.val = 2 := by omega
  have hjEq : j = (2 : Fin 4) := Fin.ext hjval
  subst j
  have hneg : -(2 : Fin 4) = 2 := by decide
  have hcleanComplement :
      (polygon.rotate (2 : Fin 4)).ChordIsClean 0 (-(2 : Fin 4)) := by
    have h := polygon.rotate_chordIsClean_zero
      (polygon.chordIsClean_symm hclean)
    simpa only [zero_sub] using h
  have hfirst : kwVectorPhaseCycle
      (polygon.prefixOfCleanChord (2 : Fin 4) (by decide) hclean).edgeList = -1 :=
    (polygon.prefixOfCleanChord (2 : Fin 4) (by decide) hclean)
      |>.earDecomposition_three |>.phaseCycle_eq_neg_one
  have hsecond : kwVectorPhaseCycle
      ((polygon.rotate (2 : Fin 4)).prefixOfCleanChord (-(2 : Fin 4))
        (by omega) hcleanComplement).edgeList = -1 := by
    have hcleanComplement' :
        (polygon.rotate (2 : Fin 4)).ChordIsClean 0 (2 : Fin 4) := by
      simpa only [hneg] using hcleanComplement
    have hsecond' : kwVectorPhaseCycle
        ((polygon.rotate (2 : Fin 4)).prefixOfCleanChord (2 : Fin 4)
          (by decide) hcleanComplement').edgeList = -1 :=
      ((polygon.rotate (2 : Fin 4)).prefixOfCleanChord
        (2 : Fin 4) (by decide) hcleanComplement')
        |>.earDecomposition_three |>.phaseCycle_eq_neg_one
    simpa only [hneg] using hsecond'
  exact polygon.cleanChordEndpointOrder_of_three_phaseSigns
    (2 : Fin 4) (by decide) hclean (by omega) hcleanComplement
    polygon.phaseCycle_eq_neg_one_four hfirst hsecond

end StatMech.FrontierA
