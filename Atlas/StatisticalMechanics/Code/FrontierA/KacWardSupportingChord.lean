/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardExtremeVertex
import Code.FrontierA.KacWardHalfPlaneSegment









namespace StatMech.FrontierA




theorem kw_eq_real_mul_of_cross_eq_zero {v w : ℂ} (hv : v ≠ 0)
    (hcross : kwComplexCross v w = 0) :
    w = ((kwComplexDot v w / Complex.normSq v : ℝ) : ℂ) * v := by
  have hnorm : Complex.normSq v ≠ 0 :=
    (Complex.normSq_pos.mpr hv).ne'
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hnorm]
    rw [Complex.normSq_apply]
    unfold kwComplexCross at hcross
    unfold kwComplexDot
    linear_combination -v.im * hcross
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [div_mul_eq_mul_div, eq_div_iff hnorm]
    rw [Complex.normSq_apply]
    unfold kwComplexCross at hcross
    unfold kwComplexDot
    linear_combination v.re * hcross




theorem kw_lineMap_openSegments_overlap_endpoints_of_lt
    {A D z : ℂ} (hAD : A ≠ D) {x y : ℝ} (hxy : x < y)
    (hzAD : Sbtw ℝ A z D)
    (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z
      (AffineMap.lineMap A D y)) :
    Sbtw ℝ A (AffineMap.lineMap A D x) D ∨
      Sbtw ℝ A (AffineMap.lineMap A D y) D ∨
      Sbtw ℝ (AffineMap.lineMap A D x) A
        (AffineMap.lineMap A D y) ∨
      Sbtw ℝ (AffineMap.lineMap A D x) D
        (AffineMap.lineMap A D y) ∨
      (AffineMap.lineMap A D x = A ∧
        AffineMap.lineMap A D y = D) := by
  obtain ⟨t, ht, htEq⟩ := hzAD.mem_image_Ioo
  obtain ⟨u, hu, huEq⟩ := hzXY.mem_image_Ioo
  have hcoord : t = (1 - u) * x + u * y := by
    apply AffineMap.lineMap_injective ℝ hAD
    calc
      AffineMap.lineMap A D t = z := htEq
      _ = AffineMap.lineMap (AffineMap.lineMap A D x)
          (AffineMap.lineMap A D y) u := huEq.symm
      _ = AffineMap.lineMap A D ((1 - u) * x + u * y) := by
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          Complex.real_smul]
        push_cast
        ring
  have hxt : x < t := by nlinarith [hu.1, hu.2]
  have hty : t < y := by nlinarith [hu.1, hu.2]
  by_cases hx0 : 0 < x
  · exact Or.inl (sbtw_lineMap_iff.mpr
      ⟨hAD, hx0, by linarith [ht.2, hxt]⟩)
  by_cases hy1 : y < 1
  · exact Or.inr (Or.inl (sbtw_lineMap_iff.mpr
      ⟨hAD, by linarith [ht.1, hty], hy1⟩))
  have hxNonpos : x ≤ 0 := le_of_not_gt hx0
  have hyOne : 1 ≤ y := le_of_not_gt hy1
  by_cases hxNeg : x < 0
  · have hs : Sbtw ℝ x 0 y :=
      Sbtw.of_lt_of_lt hxNeg (by linarith [ht.1, hty])
    have hmapped : Sbtw ℝ (AffineMap.lineMap A D x)
        (AffineMap.lineMap A D (0 : ℝ)) (AffineMap.lineMap A D y) :=
      ((AffineMap.lineMap_injective ℝ hAD).sbtw_map_iff).mpr hs
    exact Or.inr (Or.inr (Or.inl (by simpa using hmapped)))
  have hxEq : x = 0 := le_antisymm hxNonpos (not_lt.mp hxNeg)
  by_cases hyGt : 1 < y
  · have hs : Sbtw ℝ x 1 y :=
      Sbtw.of_lt_of_lt (by linarith) hyGt
    have hmapped : Sbtw ℝ (AffineMap.lineMap A D x)
        (AffineMap.lineMap A D (1 : ℝ)) (AffineMap.lineMap A D y) :=
      ((AffineMap.lineMap_injective ℝ hAD).sbtw_map_iff).mpr hs
    exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hmapped))))
  have hyEq : y = 1 := le_antisymm (not_lt.mp hyGt) hyOne
  exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [hxEq, hyEq]))))



theorem kw_lineMap_openSegments_overlap_endpoints
    {A D z : ℂ} (hAD : A ≠ D) {x y : ℝ} (hxy : x ≠ y)
    (hzAD : Sbtw ℝ A z D)
    (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z
      (AffineMap.lineMap A D y)) :
    Sbtw ℝ A (AffineMap.lineMap A D x) D ∨
      Sbtw ℝ A (AffineMap.lineMap A D y) D ∨
      Sbtw ℝ (AffineMap.lineMap A D x) A
        (AffineMap.lineMap A D y) ∨
      Sbtw ℝ (AffineMap.lineMap A D x) D
        (AffineMap.lineMap A D y) ∨
      (AffineMap.lineMap A D x = A ∧
        AffineMap.lineMap A D y = D) ∨
      (AffineMap.lineMap A D x = D ∧
        AffineMap.lineMap A D y = A) := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · rcases kw_lineMap_openSegments_overlap_endpoints_of_lt hAD hlt
      hzAD hzXY with hX | hY | hA | hD | hEq
    · exact Or.inl hX
    · exact Or.inr (Or.inl hY)
    · exact Or.inr (Or.inr (Or.inl hA))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hEq))))
  · rcases kw_lineMap_openSegments_overlap_endpoints_of_lt hAD hgt
      hzAD ((sbtw_comm).mpr hzXY) with hY | hX | hA | hD | hEq
    · exact Or.inr (Or.inl hY)
    · exact Or.inl hX
    · exact Or.inr (Or.inr (Or.inl ((sbtw_comm).mpr hA)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((sbtw_comm).mpr hD))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hEq.symm))))



theorem kw_openSegments_overlap_collinear_endpoints
    {A D X Y z : ℂ} (hAD : A ≠ D) (hXY : X ≠ Y)
    (hX : kwComplexCross (D - A) (X - A) = 0)
    (hY : kwComplexCross (D - A) (Y - A) = 0)
    (hzAD : Sbtw ℝ A z D) (hzXY : Sbtw ℝ X z Y) :
    Sbtw ℝ A X D ∨ Sbtw ℝ A Y D ∨ Sbtw ℝ X A Y ∨
      Sbtw ℝ X D Y ∨ (X = A ∧ Y = D) ∨ (X = D ∧ Y = A) := by
  let v := D - A
  let x := kwComplexDot v (X - A) / Complex.normSq v
  let y := kwComplexDot v (Y - A) / Complex.normSq v
  have hv : v ≠ 0 := sub_ne_zero.mpr hAD.symm
  have hXvec : X - A = (x : ℂ) * v := by
    exact kw_eq_real_mul_of_cross_eq_zero hv hX
  have hYvec : Y - A = (y : ℂ) * v := by
    exact kw_eq_real_mul_of_cross_eq_zero hv hY
  have hXline : AffineMap.lineMap A D x = X := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    rw [← hXvec]
    ring
  have hYline : AffineMap.lineMap A D y = Y := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    rw [← hYvec]
    ring
  have hxy : x ≠ y := by
    intro h
    apply hXY
    rw [← hXline, ← hYline, h]
  simpa only [hXline, hYline] using
    kw_lineMap_openSegments_overlap_endpoints hAD hxy hzAD
      (by simpa only [hXline, hYline] using hzXY)



theorem kw_cross_endpoints_eq_zero_of_intersect_of_nonneg
    {A D X Y z : ℂ}
    (hzAD : Sbtw ℝ A z D) (hzXY : Sbtw ℝ X z Y)
    (hX : 0 ≤ kwComplexCross (D - A) (X - A))
    (hY : 0 ≤ kwComplexCross (D - A) (Y - A)) :
    kwComplexCross (D - A) (X - A) = 0 ∧
      kwComplexCross (D - A) (Y - A) = 0 := by
  by_cases hXzero : kwComplexCross (D - A) (X - A) = 0
  · exact ⟨hXzero,
      kw_cross_right_eq_zero_of_openSegments_intersect_of_left_eq_zero
        hzAD hzXY hXzero⟩
  by_cases hYzero : kwComplexCross (D - A) (Y - A) = 0
  · exact ⟨kw_cross_left_eq_zero_of_openSegments_intersect_of_right_eq_zero
        hzAD hzXY hYzero, hYzero⟩
  have hprod := kw_cross_product_neg_of_openSegments_intersect
    hzAD hzXY hXzero hYzero
  exfalso
  exact (not_lt_of_ge (mul_nonneg hX hY)) hprod



def KWFiniteSimplePolygon.ChordIsClean {n : ℕ} [NeZero n]
    (polygon : KWFiniteSimplePolygon n) (i j : Fin n) : Prop :=
  (∀ k : Fin n, k ≠ i → k ≠ j →
      ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex j)) ∧
    ∀ k : Fin n,
      Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex i) z (polygon.vertex j)}
        {z : ℂ | Sbtw ℝ (polygon.vertex k) z
          (polygon.vertex (k + 1))}

theorem KWFiniteSimplePolygon.chordIsClean_symm
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) :
    polygon.ChordIsClean j i := by
  constructor
  · intro k hkj hki hbetween
    exact hclean.1 k hki hkj ((sbtw_comm).mpr hbetween)
  · intro k
    rw [Set.disjoint_left]
    intro z hzji hzk
    exact Set.disjoint_left.mp (hclean.2 k) ((sbtw_comm).mpr hzji) hzk





theorem KWFiniteSimplePolygon.chordIsClean_of_supporting
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hij : i ≠ j)
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hside : ∀ k : Fin n, 0 ≤ kwComplexCross
      (polygon.vertex j - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i))
    (hvertex : ∀ k : Fin n, k ≠ i → k ≠ j →
      ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
        (polygon.vertex j)) :
    polygon.ChordIsClean i j := by
  refine ⟨hvertex, ?_⟩
  intro k
  rw [Set.disjoint_left]
  intro z hzChord hzEdge
  have hAD : polygon.vertex i ≠ polygon.vertex j :=
    polygon.vertex_injective.ne hij
  have hXY : polygon.vertex k ≠ polygon.vertex (k + 1) :=
    polygon.vertex_injective.ne (polygon.add_one_ne_self k).symm
  obtain ⟨hXzero, hYzero⟩ :=
    kw_cross_endpoints_eq_zero_of_intersect_of_nonneg hzChord hzEdge
      (hside k) (hside (k + 1))
  rcases kw_openSegments_overlap_collinear_endpoints hAD hXY
      hXzero hYzero hzChord hzEdge with
    hX | hY | hI | hJ | hSame | hReverse
  · by_cases hki : k = i
    · subst k
      exact hX.ne_left rfl
    by_cases hkj : k = j
    · subst k
      exact hX.ne_right rfl
    exact hvertex k hki hkj hX
  · by_cases hki : k + 1 = i
    · rw [hki] at hY
      exact hY.ne_left rfl
    by_cases hkj : k + 1 = j
    · rw [hkj] at hY
      exact hY.ne_right rfl
    exact hvertex (k + 1) hki hkj hY
  · by_cases hik : i = k
    · rw [hik] at hI
      exact hI.ne_left rfl
    by_cases hiSucc : i = k + 1
    · rw [hiSucc] at hI
      exact hI.ne_right rfl
    exact polygon.vertex_not_strictly_between k i hik hiSucc hI
  · by_cases hjk : j = k
    · rw [hjk] at hJ
      exact hJ.ne_left rfl
    by_cases hjSucc : j = k + 1
    · rw [hjSucc] at hJ
      exact hJ.ne_right rfl
    exact polygon.vertex_not_strictly_between k j hjk hjSucc hJ
  · have hki : k = i := polygon.vertex_injective hSame.1
    have hsuccj : k + 1 = j := polygon.vertex_injective hSame.2
    apply hforward
    rw [← hki]
    exact hsuccj.symm
  · have hkj : k = j := polygon.vertex_injective hReverse.1
    have hsucci : k + 1 = i := polygon.vertex_injective hReverse.2
    apply hbackward
    rw [← hkj]
    exact hsucci.symm



theorem KWFiniteSimplePolygon.exists_nearestUpperTangent_chord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧
      (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
  obtain ⟨j, hji, hside, hvertex⟩ :=
    polygon.exists_nearestUpperTangentVertex i hsupport
  refine ⟨j, hji, ?_⟩
  by_cases hforward : j = i + 1
  · exact Or.inl hforward
  by_cases hbackward : i = j + 1
  · exact Or.inr (Or.inl hbackward)
  exact Or.inr (Or.inr (polygon.chordIsClean_of_supporting i j hji.symm
    hforward hbackward hside hvertex))




theorem KWFiniteSimplePolygon.exists_exposed_visibleChord_or_neighbor
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ i j : Fin n, i ≠ j ∧
      (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
  obtain ⟨i, hsupport⟩ := polygon.exists_strictSupportingVertex
  obtain ⟨j, hji, hj⟩ :=
    polygon.exists_nearestUpperTangent_chord i hsupport
  exact ⟨i, j, hji.symm, hj⟩




theorem KWFiniteSimplePolygon.exists_exposed_visibleChord_or_twoNeighbors
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ i : Fin n,
      (∃ j : Fin n, j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
        polygon.ChordIsClean i j) ∨
      (∃ lower upper : Fin n, lower ≠ upper ∧
        (lower = i + 1 ∨ i = lower + 1) ∧
        (upper = i + 1 ∨ i = upper + 1)) := by
  obtain ⟨i, hsupport⟩ := polygon.exists_strictSupportingVertex
  obtain ⟨lower, upper, hlowerI, hupperI, hlowerUpper,
      hlowerSide, hupperSide, hlowerVertex, hupperVertex⟩ :=
    polygon.exists_distinctNearestTangentVertices
      hnoncollinear i hsupport
  refine ⟨i, ?_⟩
  by_cases hupperForward : upper = i + 1
  · by_cases hupperBackward : i = upper + 1
    · by_cases hlowerForward : lower = i + 1
      · exact (hlowerUpper (hlowerForward.trans hupperForward.symm)).elim
      by_cases hlowerBackward : i = lower + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inr hlowerBackward, Or.inl hupperForward⟩
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
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
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
    · by_cases hlowerForward : lower = i + 1
      · exact (hlowerUpper (hlowerForward.trans hupperForward.symm)).elim
      by_cases hlowerBackward : i = lower + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inr hlowerBackward, Or.inl hupperForward⟩
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
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
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
  · by_cases hupperBackward : i = upper + 1
    · by_cases hlowerForward : lower = i + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inl hlowerForward, Or.inr hupperBackward⟩
      by_cases hlowerBackward : i = lower + 1
      · apply False.elim
        apply hlowerUpper
        apply add_right_cancel (b := (1 : Fin n))
        exact hlowerBackward.symm.trans hupperBackward
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
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
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
    · exact Or.inl ⟨upper, hupperI, hupperForward,
        hupperBackward, polygon.chordIsClean_of_supporting i upper
          hupperI.symm hupperForward hupperBackward hupperSide hupperVertex⟩



def KWFiniteSimplePolygon.VertexZeroTwoStrictlyOneSided
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 2 →
      0 < kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
        (polygon.vertex k - polygon.vertex 0)) ∨
    (∀ k : Fin (m + 3), k ≠ 0 → k ≠ 2 →
      kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
        (polygon.vertex k - polygon.vertex 0) < 0)




theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlyOneSided
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hside : polygon.VertexZeroTwoStrictlyOneSided) :
    polygon.VertexOneDiagonalIsClean := by
  let A := polygon.vertex 0
  let C := polygon.vertex 2
  have h02 : (0 : Fin (m + 3)) ≠ 2 := by
    simpa only [zero_add] using (polygon.add_two_ne_self 0).symm
  have hcross_ne (k : Fin (m + 3)) (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
      kwComplexCross (C - A) (polygon.vertex k - A) ≠ 0 := by
    rcases hside with hpos | hneg
    · exact ne_of_gt (hpos k hk0 hk2)
    · exact ne_of_lt (hneg k hk0 hk2)
  constructor
  · intro k hk0 _hk1 hk2 hbetween
    exact hcross_ne k hk0 hk2
      (kwComplexCross_eq_zero_of_sbtw hbetween)
  · intro k hk0 hk1
    by_cases hk2 : k = 2
    · subst k
      rw [Set.disjoint_left]
      intro z hzAC hzCD
      have h30 : (2 : Fin (m + 3)) + 1 ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
      have h32 : (2 : Fin (m + 3)) + 1 ≠ 2 :=
        polygon.add_one_ne_self 2
      have hcross : kwComplexCross (A - C)
          (polygon.vertex (2 + 1) - C) ≠ 0 := by
        have h := hcross_ne (2 + 1) h30 h32
        unfold A C at h ⊢
        convert neg_ne_zero.mpr h using 1 <;>
          unfold kwComplexCross <;>
          simp only [Complex.sub_re, Complex.sub_im] <;>
          ring
      exact Set.disjoint_left.mp
        (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
        ((sbtw_comm).mpr hzAC) hzCD
    · by_cases hsucc0 : k + 1 = 0
      · rw [Set.disjoint_left]
        intro z hzAC hzKA
        have hcross : kwComplexCross (C - A)
            (polygon.vertex k - A) ≠ 0 := hcross_ne k hk0 hk2
        exact Set.disjoint_left.mp
          (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
          hzAC ((sbtw_comm).mpr (by simpa only [hsucc0] using hzKA))
      · have hsucc2 : k + 1 ≠ 2 := by
          intro h
          apply hk1
          have hone : (1 : Fin (m + 3)) + 1 = 2 := by
            apply Fin.ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
          exact add_right_cancel (h.trans hone.symm)
        rcases hside with hpos | hneg
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inl ⟨hpos k hk0 hk2,
              hpos (k + 1) hsucc0 hsucc2⟩)
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inr ⟨hneg k hk0 hk2,
              hneg (k + 1) hsucc0 hsucc2⟩)




def KWFiniteSimplePolygon.VertexOneStrictlySeparated
    {m : ℕ} (polygon : KWFiniteSimplePolygon (m + 3)) : Prop :=
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex k - polygon.vertex 0)
  (0 < side 1 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → side k < 0) ∨
    (side 1 < 0 ∧ ∀ k, k ≠ 0 → k ≠ 1 → k ≠ 2 → 0 < side k)


theorem KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlySeparated
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsep : polygon.VertexOneStrictlySeparated) :
    polygon.VertexOneDiagonalIsClean := by
  let A := polygon.vertex 0
  let C := polygon.vertex 2
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (C - A) (polygon.vertex k - A)
  have hrest_ne (k : Fin (m + 3)) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
      (hk2 : k ≠ 2) : side k ≠ 0 := by
    rcases hsep with hneg | hpos
    · exact ne_of_lt (hneg.2 k hk0 hk1 hk2)
    · exact ne_of_gt (hpos.2 k hk0 hk1 hk2)
  constructor
  · intro k hk0 hk1 hk2 hbetween
    exact hrest_ne k hk0 hk1 hk2
      (kwComplexCross_eq_zero_of_sbtw hbetween)
  · intro k hk0 hk1
    by_cases hk2 : k = 2
    · subst k
      rw [Set.disjoint_left]
      intro z hzAC hzCD
      have h30 : (2 : Fin (m + 3)) + 1 ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
      have h31 : (2 : Fin (m + 3)) + 1 ≠ 1 := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hval
      have h32 : (2 : Fin (m + 3)) + 1 ≠ 2 :=
        polygon.add_one_ne_self 2
      have hcross : kwComplexCross (A - C)
          (polygon.vertex (2 + 1) - C) ≠ 0 := by
        have h := hrest_ne (2 + 1) h30 h31 h32
        unfold side at h
        unfold A C at h ⊢
        convert neg_ne_zero.mpr h using 1 <;>
          unfold kwComplexCross <;>
          simp only [Complex.sub_re, Complex.sub_im] <;>
          ring
      exact Set.disjoint_left.mp
        (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
        ((sbtw_comm).mpr hzAC) hzCD
    · by_cases hsucc0 : k + 1 = 0
      · rw [Set.disjoint_left]
        intro z hzAC hzKA
        have hcross : kwComplexCross (C - A)
            (polygon.vertex k - A) ≠ 0 := hrest_ne k hk0 hk1 hk2
        exact Set.disjoint_left.mp
          (kw_openSegments_disjoint_of_common_left_cross_ne hcross)
          hzAC ((sbtw_comm).mpr (by simpa only [hsucc0] using hzKA))
      · have hsucc1 : k + 1 ≠ 1 := by
          intro h
          apply hk0
          apply add_right_cancel (b := (1 : Fin (m + 3)))
          simpa only [zero_add] using h
        have hsucc2 : k + 1 ≠ 2 := by
          intro h
          apply hk1
          have hone : (1 : Fin (m + 3)) + 1 = 2 := by
            apply Fin.ext
            simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
          exact add_right_cancel (h.trans hone.symm)
        rcases hsep with hneg | hpos
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inr ⟨hneg.2 k hk0 hk1 hk2,
              hneg.2 (k + 1) hsucc0 hsucc1 hsucc2⟩)
        · exact kw_openSegments_disjoint_of_cross_same_sign
            (Or.inl ⟨hpos.2 k hk0 hk1 hk2,
              hpos.2 (k + 1) hsucc0 hsucc1 hsucc2⟩)



theorem KWFiniteSimplePolygon.vertexOneAlignedSideEar_of_strictlySeparated
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsep : polygon.VertexOneStrictlySeparated) :
    polygon.VertexOneAlignedSideEar := by
  let side := fun k : Fin (m + 3) ↦
    kwComplexCross (polygon.vertex 2 - polygon.vertex 0)
      (polygon.vertex k - polygon.vertex 0)
  have hzeroOne : (0 : Fin (m + 3)) + 1 = 1 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
  have honeTwo : (1 : Fin (m + 3)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have htwoThree : (2 : Fin (m + 3)) + 1 = 3 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  let previousIndex : Fin (m + 3) := ⟨m + 2, by omega⟩
  have hpreviousIndex : previousIndex = (-1 : Fin (m + 3)) := by
    apply Fin.ext
    simp [previousIndex, Fin.val_neg]
  have hpreviousNext : previousIndex + 1 = 0 := by
    rw [hpreviousIndex]
    abel
  have hp0 : previousIndex ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex] at this
  have hp1 : previousIndex ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex] at this
  have hp2 : previousIndex ≠ 2 := by
    intro h
    have := congrArg Fin.val h
    simp [previousIndex, Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at this
    omega
  have h30 : (3 : Fin (m + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at this
  have h31 : (3 : Fin (m + 3)) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at this
  have h32 : (3 : Fin (m + 3)) ≠ 2 := by
    intro h
    exact polygon.add_one_ne_self 2 (htwoThree.trans h)
  have hmiddle : kwComplexCross (polygon.edgeVector 0)
      (polygon.edgeVector 1) = -side 1 := by
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [hzeroOne, honeTwo]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hdiagonal : polygon.edgeVector 0 + polygon.edgeVector 1 =
      polygon.vertex 2 - polygon.vertex 0 := by
    unfold KWFiniteSimplePolygon.edgeVector
    rw [hzeroOne, honeTwo]
    ring
  have hleft : kwComplexCross (polygon.edgeVector (-1))
      (polygon.edgeVector 0 + polygon.edgeVector 1) = side previousIndex := by
    rw [← hpreviousIndex, hdiagonal]
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [hpreviousNext]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  have hright : kwComplexCross
      (polygon.edgeVector 0 + polygon.edgeVector 1)
      (polygon.edgeVector 2) = side 3 := by
    rw [hdiagonal]
    unfold KWFiniteSimplePolygon.edgeVector side
    rw [htwoThree]
    unfold kwComplexCross
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  refine ⟨polygon.vertexOneDiagonalIsClean_of_strictlySeparated hm hsep,
    ?_, ?_, ?_⟩
  · rw [hmiddle]
    rcases hsep with hpos | hneg
    · exact neg_ne_zero.mpr (ne_of_gt hpos.1)
    · exact neg_ne_zero.mpr (ne_of_lt hneg.1)
  · rw [hmiddle, hleft]
    rcases hsep with hpos | hneg
    · exact Or.inr ⟨neg_neg_of_pos hpos.1,
        hpos.2 previousIndex hp0 hp1 hp2⟩
    · exact Or.inl ⟨neg_pos_of_neg hneg.1,
        hneg.2 previousIndex hp0 hp1 hp2⟩
  · rw [hmiddle, hright]
    rcases hsep with hpos | hneg
    · exact Or.inr ⟨neg_neg_of_pos hpos.1, hpos.2 3 h30 h31 h32⟩
    · exact Or.inl ⟨neg_pos_of_neg hneg.1, hneg.2 3 h30 h31 h32⟩

end StatMech.FrontierA
