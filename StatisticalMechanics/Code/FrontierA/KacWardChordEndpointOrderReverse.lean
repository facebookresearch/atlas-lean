/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordEndpointOrder









namespace StatMech.FrontierA




theorem kwVectorTurnPhase_chord_boundary_of_zero_turn
    (a b c d chord : ℂ)
    (hturn : kwChordBoundaryTurnDiscrepancy a b c d chord = 0) :
    kwVectorTurnPhase a b * kwVectorTurnPhase c d =
      kwVectorTurnPhase a (-chord) * kwVectorTurnPhase (-chord) d *
        (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b) := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  have hturn' :
      (((Complex.arg b : Real.Angle) -
            (Complex.arg a : Real.Angle)).toReal : ℂ) +
          (((Complex.arg d : Real.Angle) -
            (Complex.arg c : Real.Angle)).toReal : ℂ) =
        ((((Complex.arg (-chord) : Real.Angle) -
              (Complex.arg a : Real.Angle)).toReal : ℂ) +
            (((Complex.arg d : Real.Angle) -
              (Complex.arg (-chord) : Real.Angle)).toReal : ℂ)) +
          ((((Complex.arg chord : Real.Angle) -
              (Complex.arg c : Real.Angle)).toReal : ℂ) +
            (((Complex.arg b : Real.Angle) -
              (Complex.arg chord : Real.Angle)).toReal : ℂ)) := by
    have hturnReal :
        ((Complex.arg b : Real.Angle) -
              (Complex.arg a : Real.Angle)).toReal +
            ((Complex.arg d : Real.Angle) -
              (Complex.arg c : Real.Angle)).toReal =
          (((Complex.arg (-chord) : Real.Angle) -
                (Complex.arg a : Real.Angle)).toReal +
              ((Complex.arg d : Real.Angle) -
                (Complex.arg (-chord) : Real.Angle)).toReal) +
            (((Complex.arg chord : Real.Angle) -
                (Complex.arg c : Real.Angle)).toReal +
              ((Complex.arg b : Real.Angle) -
                (Complex.arg chord : Real.Angle)).toReal) := by
      unfold kwChordBoundaryTurnDiscrepancy at hturn
      linarith
    exact_mod_cast hturnReal
  linear_combination (Complex.I / 2) * hturn'




theorem kwChordBoundaryTurnDiscrepancy_ne_zero_of_phaseCompatible
    (a b c d chord : ℂ)
    (hcompatible :
      kwVectorTurnPhase a b * kwVectorTurnPhase c d =
        -(kwVectorTurnPhase a (-chord) *
            kwVectorTurnPhase (-chord) d *
          (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b))) :
    kwChordBoundaryTurnDiscrepancy a b c d chord ≠ 0 := by
  intro hzero
  have heq := kwVectorTurnPhase_chord_boundary_of_zero_turn
    a b c d chord hzero
  let z := kwVectorTurnPhase a (-chord) *
      kwVectorTurnPhase (-chord) d *
    (kwVectorTurnPhase c chord * kwVectorTurnPhase chord b)
  have hz : z ≠ 0 := by
    dsimp only [z]
    exact mul_ne_zero
      (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
        (kwVectorTurnPhase_ne_zero _ _))
      (mul_ne_zero (kwVectorTurnPhase_ne_zero _ _)
        (kwVectorTurnPhase_ne_zero _ _))
  have : z = -z := by
    calc
      z = kwVectorTurnPhase a b * kwVectorTurnPhase c d := heq.symm
      _ = -z := hcompatible
  apply hz
  linear_combination (1 / 2 : ℂ) * this



theorem KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_iff_endpointOrder
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val) :
    polygon.CleanChordBoundaryPhaseCompatible j hj ↔
      polygon.CleanChordEndpointOrder j hj := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  constructor
  · intro hcompatible
    have hboundary :
        kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
            kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
          -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
              kwVectorTurnPhase (-chord) (p.head hpne) *
            (kwVectorTurnPhase (q.getLast hqne) chord *
              kwVectorTurnPhase chord (q.head hqne))) := by
      simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
        p, q, chord] using hcompatible
    have hne := kwChordBoundaryTurnDiscrepancy_ne_zero_of_phaseCompatible
      (p.getLast hpne) (q.head hqne) (q.getLast hqne)
      (p.head hpne) chord hboundary
    simpa only [KWFiniteSimplePolygon.CleanChordEndpointOrder,
      p, q, chord] using hne
  · intro horder
    exact polygon.cleanChordBoundaryPhaseCompatible_of_oddFullTurn j hj
      (polygon.cleanChordEndpointOddFullTurn_of_endpointOrder j hj horder)



theorem kwVectorPhasePath_ne_zero (edges : List ℂ) :
    kwVectorPhasePath edges ≠ 0 := by
  induction edges with
  | nil => simp [kwVectorPhasePath]
  | cons x edges ih =>
      cases edges with
      | nil => simp [kwVectorPhasePath]
      | cons y tail =>
          rw [kwVectorPhasePath_cons_cons]
          exact mul_ne_zero (kwVectorTurnPhase_ne_zero x y) ih




theorem kwVectorPhaseCycle_chord_boundary_of_three_neg_one
    (p q : List ℂ) (hpne : p ≠ []) (hqne : q ≠ []) (chord : ℂ)
    (hwhole : kwVectorPhaseCycle (p ++ q) = -1)
    (hp : kwVectorPhaseCycle (p.concat (-chord)) = -1)
    (hq : kwVectorPhaseCycle (q.concat chord) = -1) :
    kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
        kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
      -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
          kwVectorTurnPhase (-chord) (p.head hpne) *
        (kwVectorTurnPhase (q.getLast hqne) chord *
          kwVectorTurnPhase chord (q.head hqne))) := by
  obtain ⟨pFirst, pTail, rfl⟩ := List.exists_cons_of_ne_nil hpne
  obtain ⟨qFirst, qTail, rfl⟩ := List.exists_cons_of_ne_nil hqne
  simp only [List.getLast_cons, List.head_cons]
  rw [kwVectorPhaseCycle_append_cons] at hwhole
  rw [kwVectorPhaseCycle_concat_singleton] at hp hq
  have hpPath : kwVectorPhasePath (pFirst :: pTail) ≠ 0 :=
    kwVectorPhasePath_ne_zero _
  have hqPath : kwVectorPhasePath (qFirst :: qTail) ≠ 0 :=
    kwVectorPhasePath_ne_zero _
  apply (mul_left_cancel₀ hpPath)
  apply (mul_left_cancel₀ hqPath)
  calc
    kwVectorPhasePath (qFirst :: qTail) *
        (kwVectorPhasePath (pFirst :: pTail) *
          (kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
            kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst)) =
      kwVectorPhasePath (pFirst :: pTail) *
        kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
        kwVectorPhasePath (qFirst :: qTail) *
        kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst := by ring
    _ = -1 := hwhole
    _ = -(kwVectorPhasePath (pFirst :: pTail) *
          kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) *
          kwVectorTurnPhase (-chord) pFirst) *
        (kwVectorPhasePath (qFirst :: qTail) *
          kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord *
          kwVectorTurnPhase chord qFirst) := by rw [hp, hq]; ring
    _ = kwVectorPhasePath (qFirst :: qTail) *
        (kwVectorPhasePath (pFirst :: pTail) *
          (-(kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) *
              kwVectorTurnPhase (-chord) pFirst *
            (kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord *
              kwVectorTurnPhase chord qFirst)))) := by ring


theorem KWFiniteSimplePolygon.cleanChordEndpointOrder_of_three_phaseSigns
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j)
    (hd : 2 ≤ (-j).val)
    (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j))
    (hwhole : kwVectorPhaseCycle polygon.edgeList = -1)
    (hfirst : kwVectorPhaseCycle
      (polygon.prefixOfCleanChord j hj hclean).edgeList = -1)
    (hsecond : kwVectorPhaseCycle
      ((polygon.rotate j).prefixOfCleanChord (-j) hd
        hcleanRotated).edgeList = -1) :
    polygon.CleanChordEndpointOrder j (by omega) := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hj0 : j ≠ 0 := by
    apply Fin.ne_of_val_ne
    simpa using (show j.val ≠ 0 by omega)
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hwhole' : kwVectorPhaseCycle (p ++ q) = -1 := by
    simpa only [p, q, List.take_append_drop] using hwhole
  have hp : kwVectorPhaseCycle (p.concat (-chord)) = -1 := by
    rw [polygon.prefixOfCleanChord_edgeList_eq_take j hj hclean] at hfirst
    simpa only [p, chord, neg_sub] using hfirst
  have hq : kwVectorPhaseCycle (q.concat chord) = -1 := by
    rw [polygon.complementOfCleanChord_edgeList_eq_drop
      j hj0 hd hcleanRotated] at hsecond
    simpa only [q, chord] using hsecond
  apply (polygon.cleanChordBoundaryPhaseCompatible_iff_endpointOrder
    j (by omega)).mp
  have hboundary := kwVectorPhaseCycle_chord_boundary_of_three_neg_one
    p q hpne hqne chord hwhole' hp hq
  simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
    p, q, chord] using hboundary

end StatMech.FrontierA
