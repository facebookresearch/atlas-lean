/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordEndpointOrder





namespace StatMech.FrontierA



def KWCleanChordPhaseCompatibility : Prop :=
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (_hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (j : Fin n) (hj : 2 ≤ j.val) (_hjupper : j.val + 2 ≤ n)
    (_hclean : polygon.ChordIsClean 0 j),
    polygon.CleanChordEndpointOrder j (by omega)




theorem KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChordCompatibility
    (hcompat : KWCleanChordPhaseCompatibility) :
    ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n),
      kwVectorPhaseCycle polygon.edgeList = -1 := by
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
            rw [polygon.rotate_edgeList,
              kwVectorPhaseCycle_rotate]
          _ = kwVectorPhaseCycle
                (rotated.removeVertexOne hm hsimple).edgeList :=
            rotated.phaseCycle_removeVertexOne hm hsimple hphase
          _ = -1 := hreduced
      · have hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
            ({polygon.vertex i, polygon.vertex (i + 1),
              polygon.vertex (i + 2)} : Set ℂ) := by
          simpa only [not_exists] using hcol
        rcases polygon.exists_visibleChord_or_rotated_strictlySeparated
            hnoncollinear with hchord | hear
        · obtain ⟨i, j, hij, hforward, hbackward, hclean⟩ := hchord
          let rotated := polygon.rotate i
          let d : Fin (m + 3) := j - i
          have hcleanZero : rotated.ChordIsClean 0 d := by
            simpa only [rotated, d] using
              polygon.rotate_chordIsClean_zero hclean
          have hbounds := polygon.cleanChord_two_sided_bounds hclean
            hij hforward hbackward
          have hd : 2 ≤ d.val := by simpa only [d] using hbounds.1.1
          have hdupper : d.val + 2 ≤ m + 3 := by
            simpa only [d] using hbounds.1.2
          have hnegEq : -d = i - j := by
            dsimp only [d]
            abel
          have hnegd : 2 ≤ (-d).val := by
            rw [hnegEq]
            exact hbounds.2.1
          have hcleanComplement :
              (rotated.rotate d).ChordIsClean 0 (-d) := by
            have h := rotated.rotate_chordIsClean_zero
              (rotated.chordIsClean_symm hcleanZero)
            simpa only [zero_sub] using h
          have hfirst : kwVectorPhaseCycle
              (rotated.prefixOfCleanChord d hd hcleanZero).edgeList = -1 := by
            apply ih (d.val + 1)
            omega
          have hsecond : kwVectorPhaseCycle
              ((rotated.rotate d).prefixOfCleanChord (-d) hnegd
                hcleanComplement).edgeList = -1 := by
            apply ih ((-d).val + 1)
            have hreverseUpper : (-d).val + 2 ≤ m + 3 := by
              rw [hnegEq]
              exact hbounds.2.2
            omega
          have horder := hcompat rotated
            (polygon.rotate_not_collinear hnoncollinear i)
            d hd hdupper hcleanZero
          have hturn :=
            rotated.cleanChordEndpointOddFullTurn_of_endpointOrder
              d (by omega) horder
          have hcompatible :=
            rotated.cleanChordBoundaryPhaseCompatible_of_oddFullTurn
              d (by omega) hturn
          calc
            kwVectorPhaseCycle polygon.edgeList =
                kwVectorPhaseCycle rotated.edgeList := by
              change kwVectorPhaseCycle polygon.edgeList =
                kwVectorPhaseCycle (polygon.rotate i).edgeList
              rw [polygon.rotate_edgeList,
                kwVectorPhaseCycle_rotate]
            _ = -1 := rotated.phaseCycle_eq_neg_one_of_cleanChord
              d hd hcleanZero hnegd hcleanComplement hcompatible
              hfirst hsecond
        · obtain ⟨r, hseparated⟩ := hear
          let rotated := polygon.rotate r
          have hnoncollinearRotated :=
            polygon.rotate_not_collinear hnoncollinear r
          have haligned : rotated.VertexOneAlignedSideEar :=
            rotated.vertexOneAlignedSideEar_of_strictlySeparated hm
              hseparated
          have hgeometric : rotated.VertexOneGeometricEar hm :=
            rotated.vertexOneGeometricEar_of_alignedSideEar hm
              hnoncollinearRotated haligned
          obtain ⟨hsimple, hphase⟩ :=
            rotated.removable_of_geometricEar hm hgeometric
          have hreduced : kwVectorPhaseCycle
              (rotated.removeVertexOne hm hsimple).edgeList = -1 := by
            exact ih (m + 2) (by omega)
              (rotated.removeVertexOne hm hsimple)
          calc
            kwVectorPhaseCycle polygon.edgeList =
                kwVectorPhaseCycle rotated.edgeList := by
              change kwVectorPhaseCycle polygon.edgeList =
                kwVectorPhaseCycle (polygon.rotate r).edgeList
              rw [polygon.rotate_edgeList,
                kwVectorPhaseCycle_rotate]
            _ = kwVectorPhaseCycle
                  (rotated.removeVertexOne hm hsimple).edgeList :=
              rotated.phaseCycle_removeVertexOne hm hsimple hphase
            _ = -1 := hreduced

end StatMech.FrontierA
