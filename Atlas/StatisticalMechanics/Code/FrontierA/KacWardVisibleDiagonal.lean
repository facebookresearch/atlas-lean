/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardSupportingChord










namespace StatMech.FrontierA


def kwTriangleBaseHeight (A C P : ℂ) : ℝ :=
  kwComplexCross (C - A) (P - A)

theorem kwTriangleBaseHeight_lineMap (A C X Y : ℂ) (t : ℝ) :
    kwTriangleBaseHeight A C (AffineMap.lineMap X Y t) =
      (1 - t) * kwTriangleBaseHeight A C X +
        t * kwTriangleBaseHeight A C Y := by
  rw [AffineMap.lineMap_apply]
  unfold kwTriangleBaseHeight kwComplexCross
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem kwTriangleBaseHeight_sub (A B C P : ℂ) :
    kwTriangleBaseHeight A C B - kwTriangleBaseHeight A C P =
      kwComplexCross (A - B) (P - B) -
        kwComplexCross (C - B) (P - B) := by
  unfold kwTriangleBaseHeight kwComplexCross
  simp only [Complex.sub_re, Complex.sub_im]
  ring



theorem kwTriangleBaseHeight_lt_apex_of_wedge
    {A B C P : ℂ}
    (hAC : 0 < kwComplexCross (A - B) (C - B))
    (hAP : 0 ≤ kwComplexCross (A - B) (P - B))
    (hCP : kwComplexCross (C - B) (P - B) ≤ 0)
    (hPB : P ≠ B) :
    kwTriangleBaseHeight A C P < kwTriangleBaseHeight A C B := by
  have hsub := kwTriangleBaseHeight_sub A B C P
  have haNe : A - B ≠ 0 := by
    intro hzero
    rw [hzero] at hAC
    simp [kwComplexCross] at hAC
  by_contra hnot
  have hAPzero : kwComplexCross (A - B) (P - B) = 0 := by
    nlinarith
  have hCPzero : kwComplexCross (C - B) (P - B) = 0 := by
    nlinarith
  have hpvec := kw_eq_real_mul_of_cross_eq_zero haNe hAPzero
  have hCA : kwComplexCross (C - B) (A - B) ≠ 0 := by
    rw [kwComplexCross_swap]
    exact neg_ne_zero.mpr (ne_of_gt hAC)
  rw [hpvec, kwComplexCross_mul_real_right] at hCPzero
  have hfactor : kwComplexDot (A - B) (P - B) /
      Complex.normSq (A - B) = 0 :=
    (mul_eq_zero.mp hCPzero).resolve_right hCA
  rw [hfactor] at hpvec
  simp at hpvec
  exact hPB (sub_eq_zero.mp hpvec)



theorem kw_openSegments_disjoint_of_common_left_no_between
    {B P Q : ℂ} (hBP : B ≠ P) (hBQ : B ≠ Q) (hPQ : P ≠ Q)
    (hQnot : ¬Sbtw ℝ B Q P) (hPnot : ¬Sbtw ℝ B P Q) :
    Disjoint {z : ℂ | Sbtw ℝ B z P} {z : ℂ | Sbtw ℝ B z Q} := by
  by_cases hcross : kwComplexCross (P - B) (Q - B) = 0
  · rw [Set.disjoint_left]
    intro z hzBP hzBQ
    have hBzero : kwComplexCross (P - B) (B - B) = 0 := by
      simp [kwComplexCross]
    rcases kw_openSegments_overlap_collinear_endpoints hBP hBQ
        hBzero hcross hzBP hzBQ with
      hBinside | hQinside | hBinside' | hPinside | hSame | hReverse
    · exact hBinside.ne_left rfl
    · exact hQnot hQinside
    · exact hBinside'.ne_left rfl
    · exact hPnot hPinside
    · exact hPQ hSame.2.symm
    · exact hBP hReverse.1
  · exact kw_openSegments_disjoint_of_common_left_cross_ne hcross


theorem KWFiniteSimplePolygon.chordIsClean_of_heightBarrier
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hij : i ≠ j)
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (A C : ℂ)
    (hhigh : kwTriangleBaseHeight A C (polygon.vertex j) <
      kwTriangleBaseHeight A C (polygon.vertex i))
    (hmax : ∀ k : Fin n, k ≠ i →
      kwTriangleBaseHeight A C (polygon.vertex k) ≤
        kwTriangleBaseHeight A C (polygon.vertex j)) :
    polygon.ChordIsClean i j := by
  have hvertex : ∀ k : Fin n, k ≠ i → k ≠ j →
      ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
        (polygon.vertex j) := by
    intro k hki hkj hbetween
    obtain ⟨t, ht, htEq⟩ := hbetween.mem_image_Ioo
    have hheight := kwTriangleBaseHeight_lineMap A C
      (polygon.vertex i) (polygon.vertex j) t
    rw [htEq] at hheight
    have hkmax := hmax k hki
    nlinarith [mul_pos (sub_pos.mpr ht.2)
      (sub_pos.mpr hhigh)]
  refine ⟨hvertex, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    have hBQ : polygon.vertex i ≠ polygon.vertex (i + 1) :=
      polygon.vertex_injective.ne (polygon.add_one_ne_self i).symm
    have hPQ : polygon.vertex j ≠ polygon.vertex (i + 1) :=
      polygon.vertex_injective.ne hforward
    have hQnot : ¬Sbtw ℝ (polygon.vertex i)
        (polygon.vertex (i + 1)) (polygon.vertex j) :=
      hvertex (i + 1) (polygon.add_one_ne_self i) hforward.symm
    have hPnot : ¬Sbtw ℝ (polygon.vertex i)
        (polygon.vertex j) (polygon.vertex (i + 1)) :=
      polygon.vertex_not_strictly_between i j hij.symm hforward
    exact kw_openSegments_disjoint_of_common_left_no_between
      (polygon.vertex_injective.ne hij) hBQ hPQ hQnot hPnot
  by_cases hsuccI : k + 1 = i
  · have hBQ : polygon.vertex i ≠ polygon.vertex k :=
      polygon.vertex_injective.ne (Ne.symm hki)
    have hkj : k ≠ j := by
      intro h
      apply hbackward
      rw [← h, hsuccI]
    have hPQ : polygon.vertex j ≠ polygon.vertex k :=
      polygon.vertex_injective.ne hkj.symm
    have hQnot : ¬Sbtw ℝ (polygon.vertex i)
        (polygon.vertex k) (polygon.vertex j) :=
      hvertex k hki hkj
    have hPnot : ¬Sbtw ℝ (polygon.vertex i)
        (polygon.vertex j) (polygon.vertex k) := by
      rw [sbtw_comm]
      simpa only [hsuccI] using
        polygon.vertex_not_strictly_between k j (Ne.symm hkj)
          (by simpa only [hsuccI] using hij.symm)
    have hdisjoint := kw_openSegments_disjoint_of_common_left_no_between
      (polygon.vertex_injective.ne hij) hBQ hPQ hQnot hPnot
    rw [Set.disjoint_left] at hdisjoint ⊢
    intro z hzChord hzEdge
    exact hdisjoint hzChord ((sbtw_comm).mpr
      (by simpa only [hsuccI] using hzEdge))
  rw [Set.disjoint_left]
  intro z hzChord hzEdge
  obtain ⟨t, ht, htEq⟩ := hzChord.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzEdge.mem_image_Ioo
  have hzHigh := kwTriangleBaseHeight_lineMap A C
    (polygon.vertex i) (polygon.vertex j) t
  rw [htEq] at hzHigh
  have hkMax := hmax k hki
  have hsuccMax := hmax (k + 1) hsuccI
  have hzLow := kwTriangleBaseHeight_lineMap A C
    (polygon.vertex k) (polygon.vertex (k + 1)) u
  rw [huEq] at hzLow
  have hweighted :
      (1 - u) * kwTriangleBaseHeight A C (polygon.vertex k) +
          u * kwTriangleBaseHeight A C (polygon.vertex (k + 1)) ≤
        kwTriangleBaseHeight A C (polygon.vertex j) := by
    calc
      _ ≤ (1 - u) * kwTriangleBaseHeight A C (polygon.vertex j) +
          u * kwTriangleBaseHeight A C (polygon.vertex j) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hkMax (by linarith [hu.2]))
          (mul_le_mul_of_nonneg_left hsuccMax hu.1.le)
      _ = kwTriangleBaseHeight A C (polygon.vertex j) := by ring
  nlinarith [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hhigh)]



theorem KWFiniteSimplePolygon.exists_maxHeightVertex_of_wedge
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) (A C : ℂ)
    (hAC : 0 < kwComplexCross (A - polygon.vertex i)
      (C - polygon.vertex i))
    (hwedge : ∀ k : Fin n, k ≠ i →
      0 ≤ kwComplexCross (A - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ∧
        kwComplexCross (C - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ≤ 0) :
    ∃ j : Fin n, j ≠ i ∧
      kwTriangleBaseHeight A C (polygon.vertex j) <
        kwTriangleBaseHeight A C (polygon.vertex i) ∧
      ∀ k : Fin n, k ≠ i →
        kwTriangleBaseHeight A C (polygon.vertex k) ≤
          kwTriangleBaseHeight A C (polygon.vertex j) := by
  let candidates : Finset (Fin n) := Finset.univ.erase i
  have hcandidates : candidates.Nonempty := by
    refine ⟨i + 1, ?_⟩
    simp only [candidates, Finset.mem_erase, Finset.mem_univ, and_true]
    exact polygon.add_one_ne_self i
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image candidates
    (fun k : Fin n ↦ kwTriangleBaseHeight A C (polygon.vertex k))
    hcandidates
  have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
  refine ⟨j, hji, ?_, ?_⟩
  · exact kwTriangleBaseHeight_lt_apex_of_wedge hAC
      (hwedge j hji).1 (hwedge j hji).2
      (polygon.vertex_injective.ne hji)
  · intro k hki
    exact hjmax k (by simp [candidates, hki])



theorem KWFiniteSimplePolygon.exists_heightBarrierChord_or_neighbor
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) (A C : ℂ)
    (hAC : 0 < kwComplexCross (A - polygon.vertex i)
      (C - polygon.vertex i))
    (hwedge : ∀ k : Fin n, k ≠ i →
      0 ≤ kwComplexCross (A - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ∧
        kwComplexCross (C - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ≤ 0) :
    ∃ j : Fin n, j ≠ i ∧
      (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
  obtain ⟨j, hji, hhigh, hmax⟩ :=
    polygon.exists_maxHeightVertex_of_wedge i A C hAC hwedge
  refine ⟨j, hji, ?_⟩
  by_cases hforward : j = i + 1
  · exact Or.inl hforward
  by_cases hbackward : i = j + 1
  · exact Or.inr (Or.inl hbackward)
  exact Or.inr (Or.inr (polygon.chordIsClean_of_heightBarrier
    i j hji.symm hforward hbackward A C hhigh hmax))



theorem KWFiniteSimplePolygon.tangentWedge_cross_pos
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (i lower upper : Fin n) (hlowerI : lower ≠ i)
    (hupperI : upper ≠ i)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0)
    (hlowerSide : ∀ k : Fin n, kwComplexCross
      (polygon.vertex lower - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i) ≤ 0)
    (hupperSide : ∀ k : Fin n, 0 ≤ kwComplexCross
      (polygon.vertex upper - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)) :
    0 < kwComplexCross
      (polygon.vertex upper - polygon.vertex i)
      (polygon.vertex lower - polygon.vertex i) := by
  have hnonneg := hupperSide lower
  by_contra hnot
  have hcross : kwComplexCross
      (polygon.vertex upper - polygon.vertex i)
      (polygon.vertex lower - polygon.vertex i) = 0 := by
    exact le_antisymm (not_lt.mp hnot) hnonneg
  let a := polygon.vertex upper - polygon.vertex i
  let c := polygon.vertex lower - polygon.vertex i
  have haNe : a ≠ 0 :=
    sub_ne_zero.mpr (polygon.vertex_injective.ne hupperI)
  have hcVec := kw_eq_real_mul_of_cross_eq_zero haNe hcross
  let r := kwComplexDot a c / Complex.normSq a
  have hcVec' : c = (r : ℂ) * a := by
    simpa only [a, c, r] using hcVec
  have hdotA := hsupport upper hupperI
  have hdotC := hsupport lower hlowerI
  have hdotEq : kwComplexDot (polygon.vertex i) c =
      r * kwComplexDot (polygon.vertex i) a := by
    rw [hcVec', kwComplexDot_mul_real_right]
  have hr : 0 < r := by nlinarith
  have hallCross (k : Fin n) : kwComplexCross a
      (polygon.vertex k - polygon.vertex i) = 0 := by
    have hlower := hlowerSide k
    have hupper := hupperSide k
    have hlowerEq : kwComplexCross c
        (polygon.vertex k - polygon.vertex i) =
      r * kwComplexCross a
        (polygon.vertex k - polygon.vertex i) := by
      rw [hcVec', kwComplexCross_mul_real_left]
    rw [hlowerEq] at hlower
    nlinarith
  let x := polygon.vertex (i + 1) - polygon.vertex i
  let y := polygon.vertex (i + 2) - polygon.vertex i
  have hcrossX : kwComplexCross a x = 0 := hallCross (i + 1)
  have hcrossY : kwComplexCross a y = 0 := hallCross (i + 2)
  have hnorm : 0 < Complex.normSq a := Complex.normSq_pos.mpr haNe
  have hxy : kwComplexCross x y = 0 := by
    have hid := normSq_mul_kwComplexCross_eq_supportDet a x y
    rw [hcrossX, hcrossY] at hid
    nlinarith
  apply hnoncollinear i
  apply kw_collinear_of_cross_sub_eq_zero
  have hrewrite : polygon.vertex (i + 2) - polygon.vertex (i + 1) =
      y - x := by
    unfold x y
    ring
  rw [hrewrite, kwComplexCross_sub_right, kwComplexCross_self, sub_zero]
  exact hxy




theorem KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i a c : Fin n) (hac : a ≠ c)
    (haNeighbor : a = i + 1 ∨ i = a + 1)
    (hcNeighbor : c = i + 1 ∨ i = c + 1)
    (hAC : 0 < kwComplexCross
      (polygon.vertex a - polygon.vertex i)
      (polygon.vertex c - polygon.vertex i))
    (hwedge : ∀ k : Fin n, k ≠ i →
      0 ≤ kwComplexCross (polygon.vertex a - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ∧
        kwComplexCross (polygon.vertex c - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ≤ 0) :
    (∃ j : Fin n, j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
      polygon.ChordIsClean i j) ∨
    (0 < kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
        (polygon.vertex i) ∧
      ∀ k : Fin n, k ≠ i → k ≠ a → k ≠ c →
        kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
          (polygon.vertex k) < 0) := by
  have hneighbor_eq (k : Fin n)
      (hk : k = i + 1 ∨ i = k + 1) : k = a ∨ k = c := by
    rcases hk with hk | hk
    · rcases haNeighbor with ha | ha
      · exact Or.inl (hk.trans ha.symm)
      · rcases hcNeighbor with hc | hc
        · exact Or.inr (hk.trans hc.symm)
        · exfalso
          apply hac
          apply add_right_cancel (b := (1 : Fin n))
          exact ha.symm.trans hc
    · rcases haNeighbor with ha | ha
      · rcases hcNeighbor with hc | hc
        · exfalso
          apply hac
          exact ha.trans hc.symm
        · exact Or.inr (add_right_cancel (hk.symm.trans hc))
      · exact Or.inl (add_right_cancel (hk.symm.trans ha))
  obtain ⟨j, hji, hhigh, hmax⟩ :=
    polygon.exists_maxHeightVertex_of_wedge i
      (polygon.vertex a) (polygon.vertex c) hAC hwedge
  by_cases hjNeighbor : j = i + 1 ∨ i = j + 1
  · have hjEndpoint := hneighbor_eq j hjNeighbor
    have hjZero : kwTriangleBaseHeight (polygon.vertex a)
        (polygon.vertex c) (polygon.vertex j) = 0 := by
      rcases hjEndpoint with rfl | rfl <;>
        unfold kwTriangleBaseHeight kwComplexCross <;>
        simp only [Complex.sub_re, Complex.sub_im] <;>
        ring
    by_cases htied : ∃ k : Fin n, k ≠ i ∧ k ≠ i + 1 ∧ i ≠ k + 1 ∧
        kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
          (polygon.vertex k) = 0
    · obtain ⟨k, hki, hkForward, hkBackward, hkZero⟩ := htied
      have hkHigh : kwTriangleBaseHeight (polygon.vertex a)
          (polygon.vertex c) (polygon.vertex k) <
          kwTriangleBaseHeight (polygon.vertex a)
            (polygon.vertex c) (polygon.vertex i) := by
        exact kwTriangleBaseHeight_lt_apex_of_wedge hAC
          (hwedge k hki).1 (hwedge k hki).2
          (polygon.vertex_injective.ne hki)
      have hkMax : ∀ q : Fin n, q ≠ i →
          kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
              (polygon.vertex q) ≤
            kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
              (polygon.vertex k) := by
        intro q hqi
        rw [hkZero, ← hjZero]
        exact hmax q hqi
      exact Or.inl ⟨k, hki, hkForward, hkBackward,
        polygon.chordIsClean_of_heightBarrier i k hki.symm
          hkForward hkBackward (polygon.vertex a) (polygon.vertex c)
          hkHigh hkMax⟩
    · apply Or.inr
      constructor
      · have heq : kwTriangleBaseHeight (polygon.vertex a)
            (polygon.vertex c) (polygon.vertex i) =
          kwComplexCross (polygon.vertex a - polygon.vertex i)
            (polygon.vertex c - polygon.vertex i) := by
          unfold kwTriangleBaseHeight kwComplexCross
          simp only [Complex.sub_re, Complex.sub_im]
          ring
        rw [heq]
        exact hAC
      · intro k hki hka hkc
        have hkForward : k ≠ i + 1 := by
          intro hk
          exact (hneighbor_eq k (Or.inl hk)) |>.elim hka hkc
        have hkBackward : i ≠ k + 1 := by
          intro hk
          exact (hneighbor_eq k (Or.inr hk)) |>.elim hka hkc
        have hkle : kwTriangleBaseHeight (polygon.vertex a)
            (polygon.vertex c) (polygon.vertex k) ≤ 0 := by
          rw [← hjZero]
          exact hmax k hki
        have hkne : kwTriangleBaseHeight (polygon.vertex a)
            (polygon.vertex c) (polygon.vertex k) ≠ 0 := by
          intro hkzero
          exact htied ⟨k, hki, hkForward, hkBackward, hkzero⟩
        exact lt_of_le_of_ne hkle hkne
  · push_neg at hjNeighbor
    exact Or.inl ⟨j, hji, hjNeighbor.1, hjNeighbor.2,
      polygon.chordIsClean_of_heightBarrier i j hji.symm
        hjNeighbor.1 hjNeighbor.2 (polygon.vertex a) (polygon.vertex c)
        hhigh hmax⟩




theorem KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation_global
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    (∃ i j : Fin n, i ≠ j ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
      polygon.ChordIsClean i j) ∨
    (∃ i a c : Fin n, a ≠ c ∧
      (a = i + 1 ∨ i = a + 1) ∧
      (c = i + 1 ∨ i = c + 1) ∧
      0 < kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
        (polygon.vertex i) ∧
      ∀ k : Fin n, k ≠ i → k ≠ a → k ≠ c →
        kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
          (polygon.vertex k) < 0) := by
  obtain ⟨i, hsupport⟩ := polygon.exists_strictSupportingVertex
  obtain ⟨lower, upper, hlowerI, hupperI, hlowerUpper,
      hlowerSide, hupperSide, hlowerVertex, hupperVertex⟩ :=
    polygon.exists_distinctNearestTangentVertices
      hnoncollinear i hsupport
  have hAC := polygon.tangentWedge_cross_pos hnoncollinear
    i lower upper hlowerI hupperI hsupport hlowerSide hupperSide
  have hwedge : ∀ k : Fin n, k ≠ i →
      0 ≤ kwComplexCross (polygon.vertex upper - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ∧
        kwComplexCross (polygon.vertex lower - polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ≤ 0 := by
    intro k _
    exact ⟨hupperSide k, hlowerSide k⟩
  by_cases hupperNeighbor : upper = i + 1 ∨ i = upper + 1
  · by_cases hlowerNeighbor : lower = i + 1 ∨ i = lower + 1
    · rcases polygon.exists_visibleChord_or_strictNeighborSeparation
        i upper lower hlowerUpper.symm hupperNeighbor hlowerNeighbor
        hAC hwedge with hvisible | hseparated
      · exact Or.inl ⟨i, hvisible.choose, hvisible.choose_spec.1.symm,
          hvisible.choose_spec.2.1, hvisible.choose_spec.2.2.1,
          hvisible.choose_spec.2.2.2⟩
      · exact Or.inr ⟨i, upper, lower, hlowerUpper.symm,
          hupperNeighbor, hlowerNeighbor, hseparated⟩
    · push_neg at hlowerNeighbor
      have hsideReverse : ∀ k : Fin n, 0 ≤ kwComplexCross
          (polygon.vertex i - polygon.vertex lower)
          (polygon.vertex k - polygon.vertex lower) := by
        intro k
        have hk := hlowerSide k
        have heq : kwComplexCross
            (polygon.vertex i - polygon.vertex lower)
            (polygon.vertex k - polygon.vertex lower) =
          -kwComplexCross
            (polygon.vertex lower - polygon.vertex i)
            (polygon.vertex k - polygon.vertex i) := by
          unfold kwComplexCross
          simp only [Complex.sub_re, Complex.sub_im]
          ring
        rw [heq]
        linarith
      have hvertexReverse : ∀ k : Fin n, k ≠ lower → k ≠ i →
          ¬Sbtw ℝ (polygon.vertex lower) (polygon.vertex k)
            (polygon.vertex i) := by
        intro k hkLower hkI hbetween
        exact hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween)
      have hcleanReverse := polygon.chordIsClean_of_supporting
        lower i hlowerI hlowerNeighbor.2 hlowerNeighbor.1
        hsideReverse hvertexReverse
      exact Or.inl ⟨i, lower, hlowerI.symm, hlowerNeighbor.1,
        hlowerNeighbor.2, polygon.chordIsClean_symm hcleanReverse⟩
  · push_neg at hupperNeighbor
    exact Or.inl ⟨i, upper, hupperI.symm, hupperNeighbor.1,
      hupperNeighbor.2, polygon.chordIsClean_of_supporting
        i upper hupperI.symm hupperNeighbor.1 hupperNeighbor.2
        hupperSide hupperVertex⟩



theorem KWFiniteSimplePolygon.exists_rotated_vertexOneStrictlySeparated_of_neighborSeparation
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (i a c : Fin (m + 3)) (hac : a ≠ c)
    (haNeighbor : a = i + 1 ∨ i = a + 1)
    (hcNeighbor : c = i + 1 ∨ i = c + 1)
    (hApex : 0 < kwTriangleBaseHeight (polygon.vertex a)
      (polygon.vertex c) (polygon.vertex i))
    (hrest : ∀ k : Fin (m + 3), k ≠ i → k ≠ a → k ≠ c →
      kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c)
        (polygon.vertex k) < 0) :
    ∃ r : Fin (m + 3),
      (polygon.rotate r).VertexOneStrictlySeparated := by
  let r : Fin (m + 3) := i - 1
  have h1r : (1 : Fin (m + 3)) + r = i := by
    dsimp only [r]
    abel_nf
  have h0r : (0 : Fin (m + 3)) + r = i - 1 := by
    simp [r]
  have h2r : (2 : Fin (m + 3)) + r = i + 1 := by
    have hTwo : (2 : Fin (m + 3)) = 1 + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
    calc
      (2 : Fin (m + 3)) + r = (1 + 1) + r := by rw [hTwo]
      _ = (1 + r) + 1 := by abel
      _ = i + 1 := by rw [h1r]
  have haPrev (h : i = a + 1) : a = i - 1 := by
    apply add_right_cancel (b := (1 : Fin (m + 3)))
    rw [h]
    abel
  have hcPrev (h : i = c + 1) : c = i - 1 := by
    apply add_right_cancel (b := (1 : Fin (m + 3)))
    rw [h]
    abel
  have hendpoints :
      (a = i - 1 ∧ c = i + 1) ∨ (a = i + 1 ∧ c = i - 1) := by
    rcases haNeighbor with ha | ha
    · rcases hcNeighbor with hc | hc
      · exact (hac (ha.trans hc.symm)).elim
      · exact Or.inr ⟨ha, hcPrev hc⟩
    · rcases hcNeighbor with hc | hc
      · exact Or.inl ⟨haPrev ha, hc⟩
      · exact (hac ((haPrev ha).trans (hcPrev hc).symm)).elim
  refine ⟨r, ?_⟩
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross
      ((polygon.rotate r).vertex 2 - (polygon.rotate r).vertex 0)
      ((polygon.rotate r).vertex k - (polygon.rotate r).vertex 0)
  have hside (k : Fin (m + 3)) : side k =
      kwComplexCross
        (polygon.vertex (i + 1) - polygon.vertex (i - 1))
        (polygon.vertex (k + r) - polygon.vertex (i - 1)) := by
    unfold side KWFiniteSimplePolygon.rotate
    dsimp only
    rw [h0r, h2r]
  have hmapNe (k : Fin (m + 3)) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
      (hk2 : k ≠ 2) :
      k + r ≠ i ∧ k + r ≠ i - 1 ∧ k + r ≠ i + 1 := by
    constructor
    · intro h
      apply hk1
      apply add_right_cancel (b := r)
      exact h.trans h1r.symm
    constructor
    · intro h
      apply hk0
      apply add_right_cancel (b := r)
      exact h.trans h0r.symm
    · intro h
      apply hk2
      apply add_right_cancel (b := r)
      exact h.trans h2r.symm
  dsimp only [KWFiniteSimplePolygon.VertexOneStrictlySeparated]
  change (0 < side 1 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → side k < 0) ∨
    (side 1 < 0 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → 0 < side k)
  rcases hendpoints with horder | horder
  · apply Or.inl
    constructor
    · rw [hside, h1r, ← horder.1, ← horder.2]
      exact hApex
    · intro k hk0 hk1 hk2
      obtain ⟨hki, hka, hkc⟩ := hmapNe k hk0 hk1 hk2
      rw [hside, ← horder.1, ← horder.2]
      exact hrest (k + r) hki
        (by simpa only [horder.1] using hka)
        (by simpa only [horder.2] using hkc)
  · apply Or.inr
    constructor
    · rw [hside, h1r, ← horder.1, ← horder.2]
      have h := hApex
      unfold kwTriangleBaseHeight at h
      unfold kwComplexCross at h ⊢
      simp only [Complex.sub_re, Complex.sub_im] at h ⊢
      linarith
    · intro k hk0 hk1 hk2
      obtain ⟨hki, hka, hkc⟩ := hmapNe k hk0 hk1 hk2
      rw [hside, ← horder.1, ← horder.2]
      have h := hrest (k + r) hki
        (by simpa only [horder.1] using hkc)
        (by simpa only [horder.2] using hka)
      unfold kwTriangleBaseHeight at h
      unfold kwComplexCross at h ⊢
      simp only [Complex.sub_re, Complex.sub_im] at h ⊢
      linarith



theorem KWFiniteSimplePolygon.exists_visibleChord_or_rotated_strictlySeparated
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3))
    (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    (∃ i j : Fin (m + 3), i ≠ j ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
      polygon.ChordIsClean i j) ∨
    (∃ r : Fin (m + 3),
      (polygon.rotate r).VertexOneStrictlySeparated) := by
  rcases polygon.exists_visibleChord_or_strictNeighborSeparation_global
      hnoncollinear with hvisible | hseparated
  · exact Or.inl hvisible
  · obtain ⟨i, a, c, hac, ha, hc, hApex, hrest⟩ := hseparated
    exact Or.inr
      (polygon.exists_rotated_vertexOneStrictlySeparated_of_neighborSeparation
        i a c hac ha hc hApex hrest)

end StatMech.FrontierA
