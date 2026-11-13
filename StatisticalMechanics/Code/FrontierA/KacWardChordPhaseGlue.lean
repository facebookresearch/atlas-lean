/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardChordSplit









namespace StatMech.FrontierA



theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeList_eq_take
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j) :
    (polygon.prefixOfCleanChord j hj hclean).edgeList =
      (polygon.edgeList.take j.val).concat
        (polygon.vertex 0 - polygon.vertex j) := by
  rw [polygon.prefixOfCleanChord_edgeList j hj hclean]
  congr 1
  have hjn : j.val ≤ n := Nat.le_of_lt j.isLt
  change (List.ofFn (fun q : Fin j.val ↦
      polygon.edgeVector (kwChordPrefixIndex j q.castSucc))) =
    (List.ofFn polygon.edgeVector).take j.val
  rw [← Fin.ofFn_take_eq_take_ofFn hjn polygon.edgeVector]
  congr 1


theorem fin_zero_sub_val {n : ℕ} [NeZero n] (j : Fin n) (hj : j ≠ 0) :
    ((0 : Fin n) - j).val = n - j.val := by
  have hjval : j.val ≠ 0 := by
    intro hval
    apply hj
    apply Fin.ext
    simpa using hval
  rw [Fin.val_sub]
  simp only [Fin.val_zero, add_zero]
  rw [Nat.mod_eq_of_lt]
  omega



theorem KWFiniteSimplePolygon.complementOfCleanChord_edgeList_eq_drop
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj0 : j ≠ 0) (hd : 2 ≤ (-j).val)
    (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j)) :
    ((polygon.rotate j).prefixOfCleanChord (-j) hd
      hcleanRotated).edgeList =
      (polygon.edgeList.drop j.val).concat
        (polygon.vertex j - polygon.vertex 0) := by
  let rotated := polygon.rotate j
  let d : Fin n := -j
  have hdval : d.val = n - j.val := by
    simpa only [d, zero_sub] using fin_zero_sub_val j hj0
  have hd' : 2 ≤ d.val := by simpa only [d] using hd
  have hcleanRotated' : rotated.ChordIsClean 0 d := by
    simpa only [rotated, d] using hcleanRotated
  change (rotated.prefixOfCleanChord d hd' hcleanRotated').edgeList = _
  rw [rotated.prefixOfCleanChord_edgeList_eq_take d hd' hcleanRotated']
  have hrotate : rotated.edgeList =
      polygon.edgeList.drop j.val ++ polygon.edgeList.take j.val := by
    change (polygon.rotate j).edgeList = _
    rw [polygon.rotate_edgeList, List.rotate_eq_drop_append_take]
    simp only [KWFiniteSimplePolygon.edgeList, List.length_ofFn]
    exact Nat.le_of_lt j.isLt
  rw [hrotate, hdval]
  have hdropLength : (polygon.edgeList.drop j.val).length = n - j.val := by
    simp [KWFiniteSimplePolygon.edgeList]
  rw [← hdropLength, List.take_left]
  congr 1
  unfold rotated d KWFiniteSimplePolygon.rotate
  dsimp only
  simp



theorem kwVectorPhasePath_append_cons (x : ℂ) (left : List ℂ)
    (y : ℂ) (right : List ℂ) :
    kwVectorPhasePath ((x :: left) ++ y :: right) =
      kwVectorPhasePath (x :: left) *
        kwVectorTurnPhase ((x :: left).getLastD x) y *
          kwVectorPhasePath (y :: right) := by
  induction left generalizing x with
  | nil => simp [kwVectorPhasePath]
  | cons z left ih =>
      simp only [List.cons_append, kwVectorPhasePath_cons_cons,
        List.getLastD_cons]
      have hz := ih z
      simp only [List.cons_append, List.getLastD_cons] at hz
      rw [hz]
      ring



theorem kwVectorPhaseCycle_append_cons (x : ℂ) (left : List ℂ)
    (y : ℂ) (right : List ℂ) :
    kwVectorPhaseCycle ((x :: left) ++ y :: right) =
      kwVectorPhasePath (x :: left) *
        kwVectorTurnPhase ((x :: left).getLastD x) y *
          kwVectorPhasePath (y :: right) *
            kwVectorTurnPhase ((y :: right).getLastD y) x := by
  rw [List.cons_append]
  rw [kwVectorPhaseCycle_cons]
  have hp := kwVectorPhasePath_append_cons x left y right
  simp only [List.cons_append] at hp
  rw [hp]
  have hlast : (x :: (left ++ y :: right)).getLastD x =
      (y :: right).getLastD y := by
    rw [List.getLastD_cons, List.getLastD_eq_getLast?,
      List.getLast?_append, List.getLast?_cons]
    change right.getLast?.getD y = (y :: right).getLast?.getD y
    rw [List.getLast?_cons]
    simp
  rw [hlast]



theorem kwVectorPhaseCycle_concat_singleton (x : ℂ) (tail : List ℂ)
    (chord : ℂ) :
    kwVectorPhaseCycle ((x :: tail).concat chord) =
      kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) chord *
          kwVectorTurnPhase chord x := by
  rw [List.concat_eq_append, kwVectorPhaseCycle_append_cons]
  simp




theorem kwVectorPhaseCycle_chord_glue
    (pFirst : ℂ) (pTail : List ℂ)
    (qFirst : ℂ) (qTail : List ℂ) (chord : ℂ)
    (hboundary :
      kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
          kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst =
        -(kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) *
            kwVectorTurnPhase (-chord) pFirst *
          (kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord *
            kwVectorTurnPhase chord qFirst))) :
    kwVectorPhaseCycle ((pFirst :: pTail) ++ qFirst :: qTail) =
      -(kwVectorPhaseCycle ((pFirst :: pTail).concat (-chord)) *
          kwVectorPhaseCycle ((qFirst :: qTail).concat chord)) := by
  rw [kwVectorPhaseCycle_append_cons,
    kwVectorPhaseCycle_concat_singleton,
    kwVectorPhaseCycle_concat_singleton]
  calc
    kwVectorPhasePath (pFirst :: pTail) *
          kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
          kwVectorPhasePath (qFirst :: qTail) *
          kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst =
        kwVectorPhasePath (pFirst :: pTail) *
          kwVectorPhasePath (qFirst :: qTail) *
          (kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
            kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst) := by
      ring
    _ = -(kwVectorPhasePath (pFirst :: pTail) *
          kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) *
          kwVectorTurnPhase (-chord) pFirst *
        (kwVectorPhasePath (qFirst :: qTail) *
          kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord *
          kwVectorTurnPhase chord qFirst)) := by
      rw [hboundary]
      ring



theorem kwVectorPhaseCycle_chord_glue_eq_neg_one
    (pFirst : ℂ) (pTail : List ℂ)
    (qFirst : ℂ) (qTail : List ℂ) (chord : ℂ)
    (hboundary :
      kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) qFirst *
          kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) pFirst =
        -(kwVectorTurnPhase ((pFirst :: pTail).getLastD pFirst) (-chord) *
            kwVectorTurnPhase (-chord) pFirst *
          (kwVectorTurnPhase ((qFirst :: qTail).getLastD qFirst) chord *
            kwVectorTurnPhase chord qFirst)))
    (hp : kwVectorPhaseCycle ((pFirst :: pTail).concat (-chord)) = -1)
    (hq : kwVectorPhaseCycle ((qFirst :: qTail).concat chord) = -1) :
    kwVectorPhaseCycle ((pFirst :: pTail) ++ qFirst :: qTail) = -1 := by
  rw [kwVectorPhaseCycle_chord_glue
    pFirst pTail qFirst qTail chord hboundary, hp, hq]
  ring


theorem kwVectorPhaseCycle_chord_glue_lists
    (p q : List ℂ) (hpne : p ≠ []) (hqne : q ≠ []) (chord : ℂ)
    (hboundary :
      kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
          kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
        -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
            kwVectorTurnPhase (-chord) (p.head hpne) *
          (kwVectorTurnPhase (q.getLast hqne) chord *
            kwVectorTurnPhase chord (q.head hqne)))) :
    kwVectorPhaseCycle (p ++ q) =
      -(kwVectorPhaseCycle (p.concat (-chord)) *
          kwVectorPhaseCycle (q.concat chord)) := by
  obtain ⟨pFirst, pTail, rfl⟩ := List.exists_cons_of_ne_nil hpne
  obtain ⟨qFirst, qTail, rfl⟩ := List.exists_cons_of_ne_nil hqne
  apply kwVectorPhaseCycle_chord_glue
  simpa using hboundary



theorem kwVectorPhaseCycle_chord_glue_lists_eq_neg_one
    (p q : List ℂ) (hpne : p ≠ []) (hqne : q ≠ []) (chord : ℂ)
    (hboundary :
      kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
          kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
        -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
            kwVectorTurnPhase (-chord) (p.head hpne) *
          (kwVectorTurnPhase (q.getLast hqne) chord *
            kwVectorTurnPhase chord (q.head hqne))))
    (hp : kwVectorPhaseCycle (p.concat (-chord)) = -1)
    (hq : kwVectorPhaseCycle (q.concat chord) = -1) :
    kwVectorPhaseCycle (p ++ q) = -1 := by
  rw [kwVectorPhaseCycle_chord_glue_lists p q hpne hqne chord hboundary,
    hp, hq]
  ring




def KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val) : Prop :=
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  let hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  let chord := polygon.vertex j - polygon.vertex 0
  kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
      kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
    -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
        kwVectorTurnPhase (-chord) (p.head hpne) *
      (kwVectorTurnPhase (q.getLast hqne) chord *
        kwVectorTurnPhase chord (q.head hqne)))




theorem KWFiniteSimplePolygon.phaseCycle_eq_neg_one_of_cleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val)
    (hclean : polygon.ChordIsClean 0 j)
    (hd : 2 ≤ (-j).val)
    (hcleanRotated : (polygon.rotate j).ChordIsClean 0 (-j))
    (hcompatible : polygon.CleanChordBoundaryPhaseCompatible j (by omega))
    (hfirst : kwVectorPhaseCycle
      (polygon.prefixOfCleanChord j hj hclean).edgeList = -1)
    (hsecond : kwVectorPhaseCycle
      ((polygon.rotate j).prefixOfCleanChord (-j) hd
        hcleanRotated).edgeList = -1) :
    kwVectorPhaseCycle polygon.edgeList = -1 := by
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
  have hp : kwVectorPhaseCycle (p.concat (-chord)) = -1 := by
    rw [polygon.prefixOfCleanChord_edgeList_eq_take j hj hclean] at hfirst
    simpa only [p, chord, neg_sub] using hfirst
  have hq : kwVectorPhaseCycle (q.concat chord) = -1 := by
    rw [polygon.complementOfCleanChord_edgeList_eq_drop
      j hj0 hd hcleanRotated] at hsecond
    simpa only [q, chord] using hsecond
  have hboundary :
      kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
          kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
        -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
            kwVectorTurnPhase (-chord) (p.head hpne) *
          (kwVectorTurnPhase (q.getLast hqne) chord *
            kwVectorTurnPhase chord (q.head hqne))) := by
    simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
      p, q, chord] using hcompatible
  rw [← List.take_append_drop j.val polygon.edgeList]
  exact kwVectorPhaseCycle_chord_glue_lists_eq_neg_one
    p q hpne hqne chord hboundary hp hq



theorem kwVectorPhaseCycle_contract_front_remaining
    (incoming outgoing : ℂ) (remaining : List ℂ)
    (hne : remaining ≠ []) (htail : remaining.tail ≠ [])
    (hlocal :
      kwVectorTurnPhase (remaining.tail.getLast htail) incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing (remaining.head hne) =
        kwVectorTurnPhase (remaining.tail.getLast htail)
            (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) (remaining.head hne)) :
    kwVectorPhaseCycle (incoming :: outgoing :: remaining) =
      kwVectorPhaseCycle ((incoming + outgoing) :: remaining) := by
  obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hrest : rest ≠ [] := by simpa using htail
  let previous := rest.getLast hrest
  let tail := rest.dropLast
  have hrestEq : rest = tail ++ [previous] := by
    exact (rest.dropLast_append_getLast hrest).symm
  have hcontract := kwVectorPhaseCycle_contract_of_local
    previous incoming outgoing next tail (by simpa [previous] using hlocal)
  have horiginal := kwVectorPhaseCycle_rotate
    (previous :: incoming :: outgoing :: next :: tail) 1
  have hreduced := kwVectorPhaseCycle_rotate
    (previous :: (incoming + outgoing) :: next :: tail) 1
  simp only [List.rotate_cons_succ, List.rotate_zero] at horiginal hreduced
  rw [hrestEq]
  simpa only [List.singleton_append, List.cons_append] using
    horiginal.trans (hcontract.trans hreduced.symm)




theorem KWFiniteSimplePolygon.phaseCycle_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple)
    (hphase : polygon.VertexOnePhaseEar hm) :
    kwVectorPhaseCycle polygon.edgeList =
      kwVectorPhaseCycle (polygon.removeVertexOne hm hsimple).edgeList := by
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    polygon.edgeVector i.succ.succ)
  have hne : remaining ≠ [] := by simp [remaining]
  have htail : remaining.tail ≠ [] := by
    simp [remaining]
    omega
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic,
    kwCyclicEdgeList_eq_first_two]
  rw [polygon.removeVertexOne_edgeList hm hsimple]
  apply kwVectorPhaseCycle_contract_front_remaining
    (polygon.edgeVector 0) (polygon.edgeVector 1) remaining hne htail
  simpa only [remaining, KWFiniteSimplePolygon.VertexOnePhaseEar] using hphase

end StatMech.FrontierA
