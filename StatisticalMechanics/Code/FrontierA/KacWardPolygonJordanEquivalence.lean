/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordEndpointOrderFour
import Code.FrontierA.KacWardPolygonPhaseInduction











namespace StatMech.FrontierA


def KWFiniteSimplePolygonPhaseSign : Prop :=
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n),
    kwVectorPhaseCycle polygon.edgeList = -1



theorem kwCleanChordPhaseCompatibility_iff_polygonPhaseSign :
    KWCleanChordPhaseCompatibility ↔ KWFiniteSimplePolygonPhaseSign := by
  constructor
  · intro hcompat
    exact KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChordCompatibility
      hcompat
  · intro hphase n inst polygon _hnoncollinear j hj hjupper hclean
    have hj0 : j ≠ 0 := by
      apply Fin.ne_of_val_ne
      simpa using (show j.val ≠ 0 by omega)
    have hneg : 2 ≤ (-j).val := by
      have hval := fin_zero_sub_val j hj0
      have hval' : (-j).val = n - j.val := by
        simpa only [zero_sub] using hval
      rw [hval']
      omega
    have hcleanComplement :
        (polygon.rotate j).ChordIsClean 0 (-j) := by
      have h := polygon.rotate_chordIsClean_zero
        (polygon.chordIsClean_symm hclean)
      simpa only [zero_sub] using h
    have hfirst : kwVectorPhaseCycle
        (polygon.prefixOfCleanChord j hj hclean).edgeList = -1 :=
      hphase (polygon.prefixOfCleanChord j hj hclean)
    have hsecond : kwVectorPhaseCycle
        ((polygon.rotate j).prefixOfCleanChord (-j) hneg
          hcleanComplement).edgeList = -1 :=
      hphase ((polygon.rotate j).prefixOfCleanChord (-j) hneg
        hcleanComplement)
    exact polygon.cleanChordEndpointOrder_of_three_phaseSigns
      j hj hclean hneg hcleanComplement (hphase polygon) hfirst hsecond



theorem kwFiniteSimplePolygonPhaseSign_three_four :
    (∀ polygon : KWFiniteSimplePolygon 3,
        kwVectorPhaseCycle polygon.edgeList = -1) ∧
      (∀ polygon : KWFiniteSimplePolygon 4,
        kwVectorPhaseCycle polygon.edgeList = -1) := by
  constructor
  · intro polygon
    exact polygon.earDecomposition_three.phaseCycle_eq_neg_one
  · exact KWFiniteSimplePolygon.phaseCycle_eq_neg_one_four

end StatMech.FrontierA
