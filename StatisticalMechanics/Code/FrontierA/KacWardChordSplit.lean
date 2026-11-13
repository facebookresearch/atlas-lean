/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardVisibleDiagonal





namespace StatMech.FrontierA


def kwChordPrefixIndex {n : ℕ} [NeZero n] (j : Fin n) :
    Fin (j.val + 1) → Fin n :=
  fun k ↦ ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr j.isLt)⟩

theorem kwChordPrefixIndex_injective {n : ℕ} [NeZero n] (j : Fin n) :
    Function.Injective (kwChordPrefixIndex j) := by
  intro k l h
  apply Fin.ext
  simpa [kwChordPrefixIndex] using congrArg Fin.val h

@[simp] theorem kwChordPrefixIndex_zero {n : ℕ} [NeZero n]
    (j : Fin n) : kwChordPrefixIndex j 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem kwChordPrefixIndex_last {n : ℕ} [NeZero n]
    (j : Fin n) : kwChordPrefixIndex j (Fin.last j.val) = j := by
  apply Fin.ext
  simp [kwChordPrefixIndex]

theorem kwChordPrefixIndex_castSucc_add_one {n : ℕ} [NeZero n]
    (j : Fin n) (q : Fin j.val) :
    kwChordPrefixIndex j (q.castSucc + 1) =
      kwChordPrefixIndex j q.castSucc + 1 := by
  apply Fin.ext
  have hprefix : q.val + 1 < j.val + 1 := by omega
  have hold : q.val + 1 < n := lt_of_lt_of_le hprefix
    (Nat.succ_le_iff.mpr j.isLt)
  simp [kwChordPrefixIndex, Fin.val_add, Nat.mod_eq_of_lt hprefix,
    Nat.mod_eq_of_lt hold]

@[simp] theorem kwChordPrefixIndex_last_add_one {n : ℕ} [NeZero n]
    (j : Fin n) :
    kwChordPrefixIndex j (Fin.last j.val + 1) = 0 := by
  apply Fin.ext
  simp [kwChordPrefixIndex, Fin.val_add]


noncomputable def KWFiniteSimplePolygon.prefixOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val)
    (hclean : polygon.ChordIsClean 0 j) :
    KWFiniteSimplePolygon (j.val + 1) where
  vertex := fun k ↦ polygon.vertex (kwChordPrefixIndex j k)
  three_le := by omega
  vertex_injective := polygon.vertex_injective.comp
    (kwChordPrefixIndex_injective j)
  vertex_not_strictly_between := by
    intro q k hkq hkNext
    revert k
    refine Fin.lastCases ?_ (fun p ↦ ?_) q
    · intro k hkq hkNext
      have hk0 : kwChordPrefixIndex j k ≠ 0 := by
        intro h
        apply hkNext
        apply kwChordPrefixIndex_injective j
        simpa only [kwChordPrefixIndex_last_add_one] using h
      have hkj : kwChordPrefixIndex j k ≠ j := by
        intro h
        apply hkq
        apply kwChordPrefixIndex_injective j
        simpa only [kwChordPrefixIndex_last] using h
      simp only [kwChordPrefixIndex_last,
        kwChordPrefixIndex_last_add_one]
      change ¬Sbtw ℝ (polygon.vertex j)
        (polygon.vertex (kwChordPrefixIndex j k)) (polygon.vertex 0)
      rw [sbtw_comm]
      exact hclean.1 (kwChordPrefixIndex j k) hk0 hkj
    · intro k hkq hkNext
      have hkStart : kwChordPrefixIndex j k ≠
          kwChordPrefixIndex j p.castSucc :=
        (kwChordPrefixIndex_injective j).ne hkq
      have hkEnd : kwChordPrefixIndex j k ≠
          kwChordPrefixIndex j p.castSucc + 1 := by
        rw [← kwChordPrefixIndex_castSucc_add_one j p]
        exact (kwChordPrefixIndex_injective j).ne hkNext
      change ¬Sbtw ℝ
        (polygon.vertex (kwChordPrefixIndex j p.castSucc))
        (polygon.vertex (kwChordPrefixIndex j k))
        (polygon.vertex (kwChordPrefixIndex j (p.castSucc + 1)))
      rw [kwChordPrefixIndex_castSucc_add_one]
      exact polygon.vertex_not_strictly_between
        (kwChordPrefixIndex j p.castSucc) (kwChordPrefixIndex j k)
        hkStart hkEnd
  edgeInteriors_disjoint := by
    intro q k hqk
    revert k
    refine Fin.lastCases ?_ (fun p ↦ ?_) q
    · intro k hqk
      refine Fin.lastCases (fun h ↦ (h rfl).elim) (fun s h ↦ ?_) k hqk
      simp only [kwChordPrefixIndex_last,
        kwChordPrefixIndex_last_add_one]
      change Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex j) z (polygon.vertex 0)}
        {z : ℂ | Sbtw ℝ
          (polygon.vertex (kwChordPrefixIndex j s.castSucc)) z
          (polygon.vertex (kwChordPrefixIndex j (s.castSucc + 1)))}
      rw [kwChordPrefixIndex_castSucc_add_one]
      rw [Set.disjoint_left]
      intro z hzChord hzEdge
      exact Set.disjoint_left.mp (hclean.2
        (kwChordPrefixIndex j s.castSucc))
        ((sbtw_comm).mpr hzChord) hzEdge
    · intro k hqk
      refine Fin.lastCases (fun h ↦ ?_) (fun s h ↦ ?_) k hqk
      · simp only [kwChordPrefixIndex_last,
          kwChordPrefixIndex_last_add_one]
        change Disjoint
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j p.castSucc)) z
            (polygon.vertex
              (kwChordPrefixIndex j (p.castSucc + 1)))}
          {z : ℂ | Sbtw ℝ (polygon.vertex j) z (polygon.vertex 0)}
        rw [kwChordPrefixIndex_castSucc_add_one]
        rw [Set.disjoint_left]
        intro z hzEdge hzChord
        exact Set.disjoint_left.mp (hclean.2
          (kwChordPrefixIndex j p.castSucc))
          ((sbtw_comm).mpr hzChord) hzEdge
      · have hpNe : kwChordPrefixIndex j p.castSucc ≠
            kwChordPrefixIndex j s.castSucc :=
          (kwChordPrefixIndex_injective j).ne h
        change Disjoint
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j p.castSucc)) z
            (polygon.vertex (kwChordPrefixIndex j (p.castSucc + 1)))}
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j s.castSucc)) z
            (polygon.vertex (kwChordPrefixIndex j (s.castSucc + 1)))}
        rw [kwChordPrefixIndex_castSucc_add_one,
          kwChordPrefixIndex_castSucc_add_one]
        exact polygon.edgeInteriors_disjoint _ _ hpNe

theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_castSucc
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j)
    (q : Fin j.val) :
    (polygon.prefixOfCleanChord j hj hclean).edgeVector q.castSucc =
      polygon.edgeVector (kwChordPrefixIndex j q.castSucc) := by
  unfold KWFiniteSimplePolygon.edgeVector
  change polygon.vertex (kwChordPrefixIndex j (q.castSucc + 1)) -
      polygon.vertex (kwChordPrefixIndex j q.castSucc) = _
  rw [kwChordPrefixIndex_castSucc_add_one]

theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeVector_last
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j) :
    (polygon.prefixOfCleanChord j hj hclean).edgeVector (Fin.last j.val) =
      polygon.vertex 0 - polygon.vertex j := by
  unfold KWFiniteSimplePolygon.edgeVector
  change polygon.vertex (kwChordPrefixIndex j (Fin.last j.val + 1)) -
      polygon.vertex (kwChordPrefixIndex j (Fin.last j.val)) = _
  rw [kwChordPrefixIndex_last_add_one, kwChordPrefixIndex_last]



theorem KWFiniteSimplePolygon.prefixOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val) (hclean : polygon.ChordIsClean 0 j) :
    (polygon.prefixOfCleanChord j hj hclean).edgeList =
      (List.ofFn (fun q : Fin j.val ↦
        polygon.edgeVector (kwChordPrefixIndex j q.castSucc))).concat
          (polygon.vertex 0 - polygon.vertex j) := by
  unfold KWFiniteSimplePolygon.edgeList
  rw [List.ofFn_succ']
  congr 1
  · congr 1
    funext q
    exact polygon.prefixOfCleanChord_edgeVector_castSucc j hj hclean q
  · exact polygon.prefixOfCleanChord_edgeVector_last j hj hclean


theorem KWFiniteSimplePolygon.rotate_chordIsClean
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) (r : Fin n) :
    (polygon.rotate r).ChordIsClean (i - r) (j - r) := by
  have hi : (i - r) + r = i := by abel
  have hj : (j - r) + r = j := by abel
  constructor
  · intro k hki hkj hbetween
    have hkiOld : k + r ≠ i := by
      intro h
      apply hki
      apply add_right_cancel (b := r)
      exact h.trans hi.symm
    have hkjOld : k + r ≠ j := by
      intro h
      apply hkj
      apply add_right_cancel (b := r)
      exact h.trans hj.symm
    unfold KWFiniteSimplePolygon.rotate at hbetween
    dsimp only at hbetween
    rw [hi, hj] at hbetween
    exact hclean.1 (k + r) hkiOld hkjOld hbetween
  · intro k
    have hsucc : (k + 1) + r = (k + r) + 1 := by abel
    unfold KWFiniteSimplePolygon.rotate
    dsimp only
    rw [hi, hj, hsucc]
    exact hclean.2 (k + r)


theorem KWFiniteSimplePolygon.rotate_chordIsClean_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) :
    (polygon.rotate i).ChordIsClean 0 (j - i) := by
  simpa using polygon.rotate_chordIsClean hclean i



theorem KWFiniteSimplePolygon.cleanChord_distance_bounds
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hij : i ≠ j)
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    let d := j - i
    2 ≤ d.val ∧ d.val + 2 ≤ n := by
  let d := j - i
  have hn : 3 ≤ n := polygon.three_le
  have hd0 : d.val ≠ 0 := by
    intro hval
    have hd : d = 0 := by
      apply Fin.ext
      simpa using hval
    apply hij
    dsimp only [d] at hd
    apply sub_eq_zero.mp hd |>.symm
  have hd1 : d.val ≠ 1 := by
    intro hval
    have hd : d = (1 : Fin n) := by
      apply Fin.ext
      simpa [Nat.mod_eq_of_lt (by omega : 1 < n)] using hval
    apply hforward
    calc
      j = d + i := by dsimp only [d]; abel
      _ = 1 + i := by rw [hd]
      _ = i + 1 := by abel
  have hdLast : d.val ≠ n - 1 := by
    intro hval
    have hdWrap : d + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      have hOne : (1 : Fin n).val = 1 := by
        simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      rw [hOne]
      rw [hval]
      have hnEq : n - 1 + 1 = n := by omega
      rw [hnEq, Nat.mod_self]
    apply hbackward
    calc
      i = 0 + i := by simp
      _ = (d + 1) + i := by rw [hdWrap]
      _ = j + 1 := by dsimp only [d]; abel
  constructor <;> omega



theorem KWFiniteSimplePolygon.cleanChord_two_sided_bounds
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1)
    (hbackward : i ≠ j + 1) :
    (2 ≤ (j - i).val ∧ (j - i).val + 2 ≤ n) ∧
      (2 ≤ (i - j).val ∧ (i - j).val + 2 ≤ n) := by
  exact ⟨polygon.cleanChord_distance_bounds hij hforward hbackward,
    polygon.cleanChord_distance_bounds hij.symm hbackward hforward⟩



noncomputable def KWFiniteSimplePolygon.firstOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    KWFiniteSimplePolygon ((j - i).val + 1) := by
  let rotated := polygon.rotate i
  have hcleanZero : rotated.ChordIsClean 0 (j - i) :=
    polygon.rotate_chordIsClean_zero hclean
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  exact rotated.prefixOfCleanChord (j - i) hbound.1 hcleanZero



noncomputable def KWFiniteSimplePolygon.secondOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    KWFiniteSimplePolygon ((i - j).val + 1) := by
  let rotated := polygon.rotate j
  have hcleanZero : rotated.ChordIsClean 0 (i - j) :=
    polygon.rotate_chordIsClean_zero (polygon.chordIsClean_symm hclean)
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  exact rotated.prefixOfCleanChord (i - j) hbound.1 hcleanZero

theorem KWFiniteSimplePolygon.firstOfCleanChord_card_lt
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (j - i).val + 1 < n := by
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  omega

theorem KWFiniteSimplePolygon.secondOfCleanChord_card_lt
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (i - j).val + 1 < n := by
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  omega

theorem KWFiniteSimplePolygon.firstOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (polygon.firstOfCleanChord i j hclean hij hforward hbackward).edgeList =
      (List.ofFn (fun q : Fin (j - i).val ↦
        (polygon.rotate i).edgeVector
          (kwChordPrefixIndex (j - i) q.castSucc))).concat
        (polygon.vertex i - polygon.vertex j) := by
  let rotated := polygon.rotate i
  have hcleanZero : rotated.ChordIsClean 0 (j - i) :=
    polygon.rotate_chordIsClean_zero hclean
  have hbound := polygon.cleanChord_distance_bounds hij hforward hbackward
  change (rotated.prefixOfCleanChord (j - i) hbound.1 hcleanZero).edgeList = _
  rw [rotated.prefixOfCleanChord_edgeList]
  congr 1
  unfold rotated KWFiniteSimplePolygon.rotate
  dsimp only
  have h0 : (0 : Fin n) + i = i := by simp
  have hd : (j - i) + i = j := by abel
  rw [h0, hd]

theorem KWFiniteSimplePolygon.secondOfCleanChord_edgeList
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hclean : polygon.ChordIsClean i j)
    (hij : i ≠ j) (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1) :
    (polygon.secondOfCleanChord i j hclean hij hforward hbackward).edgeList =
      (List.ofFn (fun q : Fin (i - j).val ↦
        (polygon.rotate j).edgeVector
          (kwChordPrefixIndex (i - j) q.castSucc))).concat
        (polygon.vertex j - polygon.vertex i) := by
  let rotated := polygon.rotate j
  have hcleanZero : rotated.ChordIsClean 0 (i - j) :=
    polygon.rotate_chordIsClean_zero (polygon.chordIsClean_symm hclean)
  have hbound := polygon.cleanChord_distance_bounds
    hij.symm hbackward hforward
  change (rotated.prefixOfCleanChord (i - j) hbound.1 hcleanZero).edgeList = _
  rw [rotated.prefixOfCleanChord_edgeList]
  congr 1
  unfold rotated KWFiniteSimplePolygon.rotate
  dsimp only
  have h0 : (0 : Fin n) + j = j := by simp
  have hd : (i - j) + j = i := by abel
  rw [h0, hd]

end StatMech.FrontierA
