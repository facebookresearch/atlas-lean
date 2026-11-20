/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardVertexCoreSeparation









namespace StatMech.FrontierA

open scoped Convex
open Set

private theorem parameter_eq_of_scaled_coordinate
    {a x s t : ℝ} (hx : x ≠ 0) (h : a + s * x = a + t * x) :
    s = t := by
  apply mul_right_cancel₀ hx
  linarith

private theorem exists_re_parameter_of_segment
    {A x lo hi p q : ℝ} {P Q z : ℂ}
    (hp : p ∈ Icc lo hi) (hq : q ∈ Icc lo hi)
    (hP : P.re = A + p * x) (hQ : Q.re = A + q * x)
    (hz : z ∈ segment ℝ P Q) :
    ∃ u ∈ Icc lo hi, z.re = A + u * x := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u := (1 - t) * p + t * q
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u] <;> nlinarith [hp.1, hp.2, hq.1, hq.2,
      ht.1, ht.2]
  · rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_re, Complex.mul_re, Complex.real_smul, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, hP, hQ]
    dsimp only [u]
    ring_nf

private theorem exists_im_parameter_of_segment
    {A x lo hi p q : ℝ} {P Q z : ℂ}
    (hp : p ∈ Icc lo hi) (hq : q ∈ Icc lo hi)
    (hP : P.im = A + p * x) (hQ : Q.im = A + q * x)
    (hz : z ∈ segment ℝ P Q) :
    ∃ u ∈ Icc lo hi, z.im = A + u * x := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u := (1 - t) * p + t * q
  refine ⟨u, ?_, ?_⟩
  · constructor <;> dsimp only [u] <;> nlinarith [hp.1, hp.2, hq.1, hq.2,
      ht.1, ht.2]
  · rw [AffineMap.lineMap_apply_module]
    simp only [Complex.add_im, Complex.mul_im, Complex.real_smul, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hP, hQ]
    dsimp only [u]
    ring_nf

theorem KWAdaptivePatchedData.middleCorner_re
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.middleCorner i q).re = (polygon.vertex i).re +
      (if patch.sliceUsesVerticalFirst i q then
        patch.data.parameter i q.succ.castSucc.castSucc
      else patch.data.parameter i q.succ.castSucc.succ) *
        (polygon.edgeVector i).re := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp [KWAdaptivePatchedData.middleCorner, hv, kwVerticalPart,
      patch.data.base_re]
  · simpa only [KWAdaptivePatchedData.middleCorner, hv, if_false,
      patch.data.corner_re]

theorem KWAdaptivePatchedData.middleCorner_im
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.middleCorner i q).im = (polygon.vertex i).im +
      (if patch.sliceUsesVerticalFirst i q then
        patch.data.parameter i q.succ.castSucc.succ
      else patch.data.parameter i q.succ.castSucc.castSucc) *
        (polygon.edgeVector i).im := by
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · simp [KWAdaptivePatchedData.middleCorner, hv, kwVerticalPart,
      patch.data.base_im]
    ring
  · simpa only [KWAdaptivePatchedData.middleCorner, hv, if_false,
      patch.data.corner_im]

theorem KWAdaptivePatchedData.pathBase_castSucc_re
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.pathBase i q.castSucc).re = (polygon.vertex i).re +
      patch.data.parameter i q.succ.castSucc.castSucc *
        (polygon.edgeVector i).re := by
  rw [patch.pathBase_castSucc, patch.data.base_re]

theorem KWAdaptivePatchedData.pathBase_castSucc_im
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.pathBase i q.castSucc).im = (polygon.vertex i).im +
      patch.data.parameter i q.succ.castSucc.castSucc *
        (polygon.edgeVector i).im := by
  rw [patch.pathBase_castSucc, patch.data.base_im]

theorem KWAdaptivePatchedData.pathBase_succ_re
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.pathBase i q.succ).re = (polygon.vertex i).re +
      patch.data.parameter i q.succ.castSucc.succ *
        (polygon.edgeVector i).re := by
  rw [patch.pathBase_succ_eq_base, patch.data.base_re]
  congr 2

theorem KWAdaptivePatchedData.pathBase_succ_im
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) :
    (patch.pathBase i q.succ).im = (polygon.vertex i).im +
      patch.data.parameter i q.succ.castSucc.succ *
        (polygon.edgeVector i).im := by
  rw [patch.pathBase_succ_eq_base, patch.data.base_im]
  congr 2



theorem KWAdaptivePatchedData.middle_rawClosedEdge_point_parameters
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) {z : ℂ}
    (hz : z ∈ if even then
        kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc)
      else kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc)) :
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re) ∧
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im) := by
  have hle : patch.data.parameter i q.succ.castSucc.castSucc ≤
      patch.data.parameter i q.succ.castSucc.succ :=
    (patch.data.parameter_strict i q.succ.castSucc).le
  have hcornerRe : (if patch.sliceUsesVerticalFirst i q then
        patch.data.parameter i q.succ.castSucc.castSucc
      else patch.data.parameter i q.succ.castSucc.succ) ∈
      Icc (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ) := by
    split <;> simp_all
  have hcornerIm : (if patch.sliceUsesVerticalFirst i q then
        patch.data.parameter i q.succ.castSucc.succ
      else patch.data.parameter i q.succ.castSucc.castSucc) ∈
      Icc (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ) := by
    split <;> simp_all
  cases even with
  | false =>
      simp only [Bool.false_eq_true, if_false,
        patch.rawClosedEdge_odd_castSucc] at hz
      constructor
      · exact exists_re_parameter_of_segment hcornerRe ⟨hle, le_rfl⟩
          (patch.middleCorner_re i q) (patch.pathBase_succ_re i q) hz
      · exact exists_im_parameter_of_segment hcornerIm ⟨hle, le_rfl⟩
          (patch.middleCorner_im i q) (patch.pathBase_succ_im i q) hz
  | true =>
      simp only [if_pos rfl,
        patch.rawClosedEdge_even_castSucc] at hz
      constructor
      · exact exists_re_parameter_of_segment ⟨le_rfl, hle⟩ hcornerRe
          (patch.pathBase_castSucc_re i q) (patch.middleCorner_re i q) hz
      · exact exists_im_parameter_of_segment ⟨le_rfl, hle⟩ hcornerIm
          (patch.pathBase_castSucc_im i q) (patch.middleCorner_im i q) hz


theorem KWAdaptivePatchedData.pathBase_succ_not_mem_even_middle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.succ ∉
      kwRawClosedEdge patch.vertex (kwStairEvenIndex i q.castSucc) := by
  rw [patch.rawClosedEdge_even_castSucc]
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hline⟩ := hz
  have hstrict := patch.data.parameter_strict i q.succ.castSucc
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, patch.pathBase_castSucc_re,
      patch.middleCorner_re, patch.pathBase_succ_re, if_pos hv] at hre
    ring_nf at hre
    have heq := parameter_eq_of_scaled_coordinate
      (a := (polygon.vertex i).re) (x := (polygon.edgeVector i).re)
      (s := patch.data.parameter i q.succ.castSucc.castSucc)
      (t := patch.data.parameter i q.succ.castSucc.succ)
      (hcoords i).1 (by nlinarith [hre])
    exact hstrict.ne heq
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, patch.pathBase_castSucc_im,
      patch.middleCorner_im, patch.pathBase_succ_im, if_neg hv] at him
    ring_nf at him
    have heq := parameter_eq_of_scaled_coordinate
      (a := (polygon.vertex i).im) (x := (polygon.edgeVector i).im)
      (s := patch.data.parameter i q.succ.castSucc.castSucc)
      (t := patch.data.parameter i q.succ.castSucc.succ)
      (hcoords i).2 (by nlinarith [him])
    exact hstrict.ne heq


theorem KWAdaptivePatchedData.pathBase_castSucc_not_mem_odd_middle
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q : Fin M) :
    patch.pathBase i q.castSucc ∉
      kwRawClosedEdge patch.vertex (kwStairOddIndex i q.castSucc) := by
  rw [patch.rawClosedEdge_odd_castSucc]
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, hline⟩ := hz
  have hstrict := patch.data.parameter_strict i q.succ.castSucc
  by_cases hv : patch.sliceUsesVerticalFirst i q
  · have him := congrArg Complex.im hline
    rw [AffineMap.lineMap_apply_module] at him
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, patch.middleCorner_im,
      patch.pathBase_succ_im, patch.pathBase_castSucc_im, if_pos hv] at him
    ring_nf at him
    have heq := parameter_eq_of_scaled_coordinate
      (a := (polygon.vertex i).im) (x := (polygon.edgeVector i).im)
      (s := patch.data.parameter i q.succ.castSucc.castSucc)
      (t := patch.data.parameter i q.succ.castSucc.succ)
      (hcoords i).2 (by nlinarith [him])
    exact hstrict.ne heq
  · have hre := congrArg Complex.re hline
    rw [AffineMap.lineMap_apply_module] at hre
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, patch.middleCorner_re,
      patch.pathBase_succ_re, patch.pathBase_castSucc_re, if_neg hv] at hre
    ring_nf at hre
    have heq := parameter_eq_of_scaled_coordinate
      (a := (polygon.vertex i).re) (x := (polygon.edgeVector i).re)
      (s := patch.data.parameter i q.succ.castSucc.castSucc)
      (t := patch.data.parameter i q.succ.castSucc.succ)
      (hcoords i).1 (by nlinarith [hre])
    exact hstrict.ne heq

def kwAdaptiveMiddleIndex
    {n M : ℕ} [NeZero n] [NeZero M]
    (i : Fin n) (q : Fin M) (even : Bool) :
    Fin (n * (2 * (M + 1))) :=
  if even then kwStairEvenIndex i q.castSucc
  else kwStairOddIndex i q.castSucc

def KWAdaptivePatchedData.middleClosedEdge
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) : Set ℂ :=
  kwRawClosedEdge patch.vertex (kwAdaptiveMiddleIndex i q even)

theorem KWAdaptivePatchedData.middleClosedEdge_point_parameters
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) {z : ℂ}
    (hz : z ∈ patch.middleClosedEdge i q even) :
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re) ∧
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im) := by
  cases even with
  | false =>
      exact patch.middle_rawClosedEdge_point_parameters i q false (by
        simpa [KWAdaptivePatchedData.middleClosedEdge,
          kwAdaptiveMiddleIndex] using hz)
  | true =>
      exact patch.middle_rawClosedEdge_point_parameters i q true (by
        simpa [KWAdaptivePatchedData.middleClosedEdge,
          kwAdaptiveMiddleIndex] using hz)

private theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_gap
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hgap : q.val + 1 < l.val) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rw [Set.disjoint_left]
  intro z hzq hzl
  obtain ⟨⟨uq, huq, hreq⟩, _⟩ :=
    patch.middleClosedEdge_point_parameters i q eq hzq
  obtain ⟨⟨ul, hul, hrel⟩, _⟩ :=
    patch.middleClosedEdge_point_parameters i l el hzl
  have hulEq : uq = ul :=
    parameter_eq_of_scaled_coordinate (hcoords i).1 (hreq.symm.trans hrel)
  have hindex : q.succ.castSucc.succ < l.succ.castSucc.castSucc := by
    apply Fin.mk_lt_mk.mpr
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hparam := patch.data.parameter_strictMono i hindex
  linarith [huq.2, hul.1]

private theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_next
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hnext : q.val + 1 = l.val)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rw [Set.disjoint_left]
  intro z hzq hzl
  obtain ⟨⟨urq, hurq, hreq⟩, ⟨uiq, huiq, himeq⟩⟩ :=
    patch.middleClosedEdge_point_parameters i q eq hzq
  obtain ⟨⟨url, hurl, hrel⟩, ⟨uil, huil, himel⟩⟩ :=
    patch.middleClosedEdge_point_parameters i l el hzl
  have hparameterIndex : q.succ.castSucc.succ =
      l.succ.castSucc.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hparameter : patch.data.parameter i q.succ.castSucc.succ =
      patch.data.parameter i l.succ.castSucc.castSucc := by rw [hparameterIndex]
  have hreParameter : urq = url :=
    parameter_eq_of_scaled_coordinate (hcoords i).1 (hreq.symm.trans hrel)
  have himParameter : uiq = uil :=
    parameter_eq_of_scaled_coordinate (hcoords i).2 (himeq.symm.trans himel)
  have hurqEnd : urq = patch.data.parameter i q.succ.castSucc.succ := by
    linarith [hurq.2, hurl.1]
  have huiqEnd : uiq = patch.data.parameter i q.succ.castSucc.succ := by
    linarith [huiq.2, huil.1]
  have hzbase : z = patch.pathBase i q.succ := by
    apply Complex.ext
    · rw [patch.pathBase_succ_re, hreq, hurqEnd]
    · rw [patch.pathBase_succ_im, himeq, huiqEnd]
  subst z
  cases eq with
  | true =>
      exact patch.pathBase_succ_not_mem_even_middle hcoords i q hzq
  | false =>
      cases el with
      | false =>
          have hbase : patch.pathBase i q.succ =
              patch.pathBase i l.castSucc := by
            rw [patch.pathBase_succ_eq_base, patch.pathBase_castSucc]
            congr 2
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
          rw [hbase] at hzl
          exact patch.pathBase_castSucc_not_mem_odd_middle hcoords i l hzl
      | true =>
          apply hnon.2.2
          simp only [kwAdaptiveMiddleIndex, Bool.false_eq_true, if_false,
            if_pos rfl]
          rw [kwStairOddIndex_castSucc_add_one]
          congr 2
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega

private theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_lt
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hlt : q.val < l.val)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  by_cases hgap : q.val + 1 < l.val
  · exact patch.middleClosedEdges_disjoint_of_gap hcoords i q l eq el hgap
  · apply patch.middleClosedEdges_disjoint_of_next hcoords i q l eq el
    · omega
    · exact hnon



theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_sameOwner
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rcases lt_trichotomy q.val l.val with hlt | heq | hgt
  · exact patch.middleClosedEdges_disjoint_of_lt hcoords i q l eq el hlt hnon
  · have hql : q = l := Fin.ext heq
    subst l
    cases eq <;> cases el
    · exact (hnon.1 (by simp [kwAdaptiveMiddleIndex])).elim
    · apply (hnon.2.1 ?_).elim
      simpa [kwAdaptiveMiddleIndex] using
        (kwStairEvenIndex_add_one i q.castSucc).symm
    · apply (hnon.2.2 ?_).elim
      simpa [kwAdaptiveMiddleIndex] using
        kwStairEvenIndex_add_one i q.castSucc
    · exact (hnon.1 (by simp [kwAdaptiveMiddleIndex])).elim
  · exact (patch.middleClosedEdges_disjoint_of_lt hcoords i l q el eq hgt
      hnon.symm).symm

end StatMech.FrontierA
