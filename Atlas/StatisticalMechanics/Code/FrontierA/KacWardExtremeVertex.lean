/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardFinitePolygonEar









namespace StatMech.FrontierA


def kwComplexDot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im



noncomputable def kwSupportSlope (u v : ℂ) : ℝ :=
  kwComplexCross u v / (-kwComplexDot u v)

theorem two_mul_kwComplexDot_sub (x y : ℂ) :
    2 * kwComplexDot x (y - x) =
      Complex.normSq y - Complex.normSq x - Complex.normSq (y - x) := by
  unfold kwComplexDot
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring



theorem normSq_mul_kwComplexCross_eq_supportDet (u v w : ℂ) :
    Complex.normSq u * kwComplexCross v w =
      kwComplexCross u v * (-kwComplexDot u w) -
        kwComplexCross u w * (-kwComplexDot u v) := by
  rw [Complex.normSq_apply]
  unfold kwComplexCross kwComplexDot
  ring

theorem kwComplexDot_mul_real_right (r : ℝ) (u v : ℂ) :
    kwComplexDot u ((r : ℂ) * v) = r * kwComplexDot u v := by
  unfold kwComplexDot
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem normSq_mul_real (r : ℝ) (v : ℂ) :
    Complex.normSq ((r : ℂ) * v) = r ^ 2 * Complex.normSq v := by
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring



theorem KWFiniteSimplePolygon.exists_strictSupportingVertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ i : Fin n, ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin n ↦ Complex.normSq (polygon.vertex k))
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  intro j hji
  have hnormLe : Complex.normSq (polygon.vertex j) ≤
      Complex.normSq (polygon.vertex i) := hi j (Finset.mem_univ j)
  have hsub : polygon.vertex j - polygon.vertex i ≠ 0 :=
    sub_ne_zero.mpr (polygon.vertex_injective.ne hji)
  have hnormPos : 0 < Complex.normSq
      (polygon.vertex j - polygon.vertex i) := Complex.normSq_pos.mpr hsub
  have hid := two_mul_kwComplexDot_sub
    (polygon.vertex i) (polygon.vertex j)
  nlinarith




theorem KWFiniteSimplePolygon.exists_upperTangentVertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧ ∀ k : Fin n,
      0 ≤ kwComplexCross
        (polygon.vertex j - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) := by
  let candidates : Finset (Fin n) := Finset.univ.erase i
  have hcandidates : candidates.Nonempty := by
    refine ⟨i + 1, ?_⟩
    simp only [candidates, Finset.mem_erase, Finset.mem_univ, and_true]
    exact polygon.add_one_ne_self i
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image candidates
    (fun k : Fin n ↦ kwSupportSlope (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)) hcandidates
  have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
  refine ⟨j, hji, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    simp [kwComplexCross]
  have hkmem : k ∈ candidates := by
    simp [candidates, hki]
  have hslope := hjmax k hkmem
  have hdenJ : 0 < -kwComplexDot (polygon.vertex i)
      (polygon.vertex j - polygon.vertex i) := by
    exact neg_pos.mpr (hsupport j hji)
  have hdenK : 0 < -kwComplexDot (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i) := by
    exact neg_pos.mpr (hsupport k hki)
  have hdet : kwComplexCross (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) *
        (-kwComplexDot (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i)) ≤
      kwComplexCross (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) *
        (-kwComplexDot (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i)) := by
    exact (div_le_div_iff₀ hdenK hdenJ).mp hslope
  have hiNe : polygon.vertex i ≠ 0 := by
    intro hiZero
    have hs := hsupport (i + 1) (polygon.add_one_ne_self i)
    rw [hiZero] at hs
    simp [kwComplexDot] at hs
  have hnorm : 0 < Complex.normSq (polygon.vertex i) :=
    Complex.normSq_pos.mpr hiNe
  have hid := normSq_mul_kwComplexCross_eq_supportDet
    (polygon.vertex i)
    (polygon.vertex j - polygon.vertex i)
    (polygon.vertex k - polygon.vertex i)
  nlinarith



theorem KWFiniteSimplePolygon.exists_nearestUpperTangentVertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧
      (∀ k : Fin n, 0 ≤ kwComplexCross
        (polygon.vertex j - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i)) ∧
      ∀ k : Fin n, k ≠ i → k ≠ j →
        ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
          (polygon.vertex j) := by
  let candidates : Finset (Fin n) := Finset.univ.erase i
  have hcandidates : candidates.Nonempty := by
    refine ⟨i + 1, ?_⟩
    simp only [candidates, Finset.mem_erase, Finset.mem_univ, and_true]
    exact polygon.add_one_ne_self i
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image candidates
    (fun k : Fin n ↦ kwSupportSlope (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)) hcandidates
  let tangents := candidates.filter (fun k : Fin n ↦
    kwSupportSlope (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) =
      kwSupportSlope (polygon.vertex i)
        (polygon.vertex j₀ - polygon.vertex i))
  have htangents : tangents.Nonempty := by
    refine ⟨j₀, ?_⟩
    simp [tangents, hj₀mem]
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image tangents
    (fun k : Fin n ↦ Complex.normSq
      (polygon.vertex k - polygon.vertex i)) htangents
  have hjCandidates : j ∈ candidates :=
    (Finset.mem_filter.mp hjmem).1
  have hji : j ≠ i := (Finset.mem_erase.mp hjCandidates).1
  have hjSlope : kwSupportSlope (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) =
      kwSupportSlope (polygon.vertex i)
        (polygon.vertex j₀ - polygon.vertex i) :=
    (Finset.mem_filter.mp hjmem).2
  have hiNe : polygon.vertex i ≠ 0 := by
    intro hiZero
    have hs := hsupport (i + 1) (polygon.add_one_ne_self i)
    rw [hiZero] at hs
    simp [kwComplexDot] at hs
  have hnormI : 0 < Complex.normSq (polygon.vertex i) :=
    Complex.normSq_pos.mpr hiNe
  refine ⟨j, hji, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      simp [kwComplexCross]
    have hkmem : k ∈ candidates := by
      simp [candidates, hki]
    have hslope₀ := hj₀max k hkmem
    have hslope : kwSupportSlope (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) ≤
        kwSupportSlope (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) := by
      rw [hjSlope]
      exact hslope₀
    have hdenJ : 0 < -kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) :=
      neg_pos.mpr (hsupport j hji)
    have hdenK : 0 < -kwComplexDot (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) :=
      neg_pos.mpr (hsupport k hki)
    have hdet : kwComplexCross (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) *
          (-kwComplexDot (polygon.vertex i)
            (polygon.vertex j - polygon.vertex i)) ≤
        kwComplexCross (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) *
          (-kwComplexDot (polygon.vertex i)
            (polygon.vertex k - polygon.vertex i)) := by
      exact (div_le_div_iff₀ hdenK hdenJ).mp hslope
    have hid := normSq_mul_kwComplexCross_eq_supportDet
      (polygon.vertex i)
      (polygon.vertex j - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)
    nlinarith
  · intro k hki hkj hbetween
    obtain ⟨t, ht, htEq⟩ := hbetween.mem_image_Ioo
    have hvec : polygon.vertex k - polygon.vertex i =
        (t : ℂ) * (polygon.vertex j - polygon.vertex i) := by
      rw [← htEq, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
      ring
    have hdotJ : kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) ≠ 0 :=
      ne_of_lt (hsupport j hji)
    have hslopeEq : kwSupportSlope (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) =
        kwSupportSlope (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) := by
      rw [hvec]
      unfold kwSupportSlope
      rw [kwComplexCross_mul_real_right, kwComplexDot_mul_real_right]
      field_simp [ht.1.ne', hdotJ]
    have hkTangent : k ∈ tangents := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simp [candidates, hki]
      · exact hslopeEq.trans hjSlope
    have hmin := hjmin k hkTangent
    have hjNePoint : polygon.vertex j - polygon.vertex i ≠ 0 :=
      sub_ne_zero.mpr (polygon.vertex_injective.ne hji)
    have hnormJ : 0 < Complex.normSq
        (polygon.vertex j - polygon.vertex i) :=
      Complex.normSq_pos.mpr hjNePoint
    have hnormEq : Complex.normSq
          (polygon.vertex k - polygon.vertex i) =
        t ^ 2 * Complex.normSq
          (polygon.vertex j - polygon.vertex i) := by
      rw [hvec, normSq_mul_real]
    rw [hnormEq] at hmin
    have htSq : t ^ 2 < 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    have hstrict : 0 < (1 - t ^ 2) * Complex.normSq
        (polygon.vertex j - polygon.vertex i) :=
      mul_pos (sub_pos.mpr htSq) hnormJ
    nlinarith



theorem KWFiniteSimplePolygon.exists_lowerTangentVertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧ ∀ k : Fin n,
      kwComplexCross
        (polygon.vertex j - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) ≤ 0 := by
  let candidates : Finset (Fin n) := Finset.univ.erase i
  have hcandidates : candidates.Nonempty := by
    refine ⟨i + 1, ?_⟩
    simp only [candidates, Finset.mem_erase, Finset.mem_univ, and_true]
    exact polygon.add_one_ne_self i
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image candidates
    (fun k : Fin n ↦ kwSupportSlope (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)) hcandidates
  have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
  refine ⟨j, hji, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    simp [kwComplexCross]
  have hkmem : k ∈ candidates := by
    simp [candidates, hki]
  have hslope := hjmin k hkmem
  have hdenJ : 0 < -kwComplexDot (polygon.vertex i)
      (polygon.vertex j - polygon.vertex i) := by
    exact neg_pos.mpr (hsupport j hji)
  have hdenK : 0 < -kwComplexDot (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i) := by
    exact neg_pos.mpr (hsupport k hki)
  have hdet : kwComplexCross (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) *
        (-kwComplexDot (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i)) ≤
      kwComplexCross (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) *
        (-kwComplexDot (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i)) := by
    exact (div_le_div_iff₀ hdenJ hdenK).mp hslope
  have hiNe : polygon.vertex i ≠ 0 := by
    intro hiZero
    have hs := hsupport (i + 1) (polygon.add_one_ne_self i)
    rw [hiZero] at hs
    simp [kwComplexDot] at hs
  have hnorm : 0 < Complex.normSq (polygon.vertex i) :=
    Complex.normSq_pos.mpr hiNe
  have hid := normSq_mul_kwComplexCross_eq_supportDet
    (polygon.vertex i)
    (polygon.vertex j - polygon.vertex i)
    (polygon.vertex k - polygon.vertex i)
  nlinarith


theorem KWFiniteSimplePolygon.exists_nearestLowerTangentVertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧
      (∀ k : Fin n, kwComplexCross
        (polygon.vertex j - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) ≤ 0) ∧
      ∀ k : Fin n, k ≠ i → k ≠ j →
        ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
          (polygon.vertex j) := by
  let candidates : Finset (Fin n) := Finset.univ.erase i
  have hcandidates : candidates.Nonempty := by
    refine ⟨i + 1, ?_⟩
    simp only [candidates, Finset.mem_erase, Finset.mem_univ, and_true]
    exact polygon.add_one_ne_self i
  obtain ⟨j₀, hj₀mem, hj₀min⟩ := Finset.exists_min_image candidates
    (fun k : Fin n ↦ kwSupportSlope (polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)) hcandidates
  let tangents := candidates.filter (fun k : Fin n ↦
    kwSupportSlope (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) =
      kwSupportSlope (polygon.vertex i)
        (polygon.vertex j₀ - polygon.vertex i))
  have htangents : tangents.Nonempty := by
    refine ⟨j₀, ?_⟩
    simp [tangents, hj₀mem]
  obtain ⟨j, hjmem, hjnormMin⟩ := Finset.exists_min_image tangents
    (fun k : Fin n ↦ Complex.normSq
      (polygon.vertex k - polygon.vertex i)) htangents
  have hjCandidates : j ∈ candidates :=
    (Finset.mem_filter.mp hjmem).1
  have hji : j ≠ i := (Finset.mem_erase.mp hjCandidates).1
  have hjSlope : kwSupportSlope (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) =
      kwSupportSlope (polygon.vertex i)
        (polygon.vertex j₀ - polygon.vertex i) :=
    (Finset.mem_filter.mp hjmem).2
  have hiNe : polygon.vertex i ≠ 0 := by
    intro hiZero
    have hs := hsupport (i + 1) (polygon.add_one_ne_self i)
    rw [hiZero] at hs
    simp [kwComplexDot] at hs
  have hnormI : 0 < Complex.normSq (polygon.vertex i) :=
    Complex.normSq_pos.mpr hiNe
  refine ⟨j, hji, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      simp [kwComplexCross]
    have hkmem : k ∈ candidates := by
      simp [candidates, hki]
    have hslope₀ := hj₀min k hkmem
    have hslope : kwSupportSlope (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) ≤
        kwSupportSlope (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) := by
      rw [hjSlope]
      exact hslope₀
    have hdenJ : 0 < -kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) :=
      neg_pos.mpr (hsupport j hji)
    have hdenK : 0 < -kwComplexDot (polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) :=
      neg_pos.mpr (hsupport k hki)
    have hdet : kwComplexCross (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) *
          (-kwComplexDot (polygon.vertex i)
            (polygon.vertex k - polygon.vertex i)) ≤
        kwComplexCross (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) *
          (-kwComplexDot (polygon.vertex i)
            (polygon.vertex j - polygon.vertex i)) := by
      exact (div_le_div_iff₀ hdenJ hdenK).mp hslope
    have hid := normSq_mul_kwComplexCross_eq_supportDet
      (polygon.vertex i)
      (polygon.vertex j - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i)
    nlinarith
  · intro k hki hkj hbetween
    obtain ⟨t, ht, htEq⟩ := hbetween.mem_image_Ioo
    have hvec : polygon.vertex k - polygon.vertex i =
        (t : ℂ) * (polygon.vertex j - polygon.vertex i) := by
      rw [← htEq, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
      ring
    have hdotJ : kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) ≠ 0 :=
      ne_of_lt (hsupport j hji)
    have hslopeEq : kwSupportSlope (polygon.vertex i)
          (polygon.vertex k - polygon.vertex i) =
        kwSupportSlope (polygon.vertex i)
          (polygon.vertex j - polygon.vertex i) := by
      rw [hvec]
      unfold kwSupportSlope
      rw [kwComplexCross_mul_real_right, kwComplexDot_mul_real_right]
      field_simp [ht.1.ne', hdotJ]
    have hkTangent : k ∈ tangents := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simp [candidates, hki]
      · exact hslopeEq.trans hjSlope
    have hmin := hjnormMin k hkTangent
    have hjNePoint : polygon.vertex j - polygon.vertex i ≠ 0 :=
      sub_ne_zero.mpr (polygon.vertex_injective.ne hji)
    have hnormJ : 0 < Complex.normSq
        (polygon.vertex j - polygon.vertex i) :=
      Complex.normSq_pos.mpr hjNePoint
    have hnormEq : Complex.normSq
          (polygon.vertex k - polygon.vertex i) =
        t ^ 2 * Complex.normSq
          (polygon.vertex j - polygon.vertex i) := by
      rw [hvec, normSq_mul_real]
    rw [hnormEq] at hmin
    have htSq : t ^ 2 < 1 := by
      nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
    have hstrict : 0 < (1 - t ^ 2) * Complex.normSq
        (polygon.vertex j - polygon.vertex i) :=
      mul_pos (sub_pos.mpr htSq) hnormJ
    nlinarith



theorem KWFiniteSimplePolygon.exists_distinctNearestTangentVertices
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ lower upper : Fin n,
      lower ≠ i ∧ upper ≠ i ∧ lower ≠ upper ∧
      (∀ k : Fin n, kwComplexCross
        (polygon.vertex lower - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) ≤ 0) ∧
      (∀ k : Fin n, 0 ≤ kwComplexCross
        (polygon.vertex upper - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i)) ∧
      (∀ k : Fin n, k ≠ i → k ≠ lower →
        ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
          (polygon.vertex lower)) ∧
      (∀ k : Fin n, k ≠ i → k ≠ upper →
        ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
          (polygon.vertex upper)) := by
  obtain ⟨upper, hupperI, hupper, hupperVertex⟩ :=
    polygon.exists_nearestUpperTangentVertex i hsupport
  obtain ⟨lower, hlowerI, hlower, hlowerVertex⟩ :=
    polygon.exists_nearestLowerTangentVertex i hsupport
  refine ⟨lower, upper, hlowerI, hupperI, ?_, hlower, hupper,
    hlowerVertex, hupperVertex⟩
  intro heq
  subst lower
  let u := polygon.vertex upper - polygon.vertex i
  let x := polygon.vertex (i + 1) - polygon.vertex i
  let y := polygon.vertex (i + 2) - polygon.vertex i
  have hcrossX : kwComplexCross u x = 0 := by
    apply le_antisymm
    · exact hlower (i + 1)
    · exact hupper (i + 1)
  have hcrossY : kwComplexCross u y = 0 := by
    apply le_antisymm
    · exact hlower (i + 2)
    · exact hupper (i + 2)
  have huNe : u ≠ 0 := by
    unfold u
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne hupperI)
  have hnorm : 0 < Complex.normSq u := Complex.normSq_pos.mpr huNe
  have hxy : kwComplexCross x y = 0 := by
    have hid := normSq_mul_kwComplexCross_eq_supportDet u x y
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



theorem KWFiniteSimplePolygon.exists_distinctTangentVertices
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ))
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ lower upper : Fin n,
      lower ≠ i ∧ upper ≠ i ∧ lower ≠ upper ∧
      (∀ k : Fin n, kwComplexCross
        (polygon.vertex lower - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i) ≤ 0) ∧
      (∀ k : Fin n, 0 ≤ kwComplexCross
        (polygon.vertex upper - polygon.vertex i)
        (polygon.vertex k - polygon.vertex i)) := by
  obtain ⟨upper, hupperI, hupper⟩ :=
    polygon.exists_upperTangentVertex i hsupport
  obtain ⟨lower, hlowerI, hlower⟩ :=
    polygon.exists_lowerTangentVertex i hsupport
  refine ⟨lower, upper, hlowerI, hupperI, ?_, hlower, hupper⟩
  intro heq
  subst lower
  let u := polygon.vertex upper - polygon.vertex i
  let x := polygon.vertex (i + 1) - polygon.vertex i
  let y := polygon.vertex (i + 2) - polygon.vertex i
  have hcrossX : kwComplexCross u x = 0 := by
    apply le_antisymm
    · exact hlower (i + 1)
    · exact hupper (i + 1)
  have hcrossY : kwComplexCross u y = 0 := by
    apply le_antisymm
    · exact hlower (i + 2)
    · exact hupper (i + 2)
  have huNe : u ≠ 0 := by
    unfold u
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne hupperI)
  have hnorm : 0 < Complex.normSq u := Complex.normSq_pos.mpr huNe
  have hxy : kwComplexCross x y = 0 := by
    have hid := normSq_mul_kwComplexCross_eq_supportDet u x y
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

end StatMech.FrontierA
