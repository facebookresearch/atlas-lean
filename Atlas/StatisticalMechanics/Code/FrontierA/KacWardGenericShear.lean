/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAxisStaircase










namespace StatMech.FrontierA


def kwShearX (t : ℝ) (z : ℂ) : ℂ :=
  (z.re + t * z.im) + z.im * Complex.I

def kwShearY (t : ℝ) (z : ℂ) : ℂ :=
  z.re + (z.im + t * z.re) * Complex.I

@[simp] theorem kwShearX_re (t : ℝ) (z : ℂ) :
    (kwShearX t z).re = z.re + t * z.im := by
  simp [kwShearX]

@[simp] theorem kwShearX_im (t : ℝ) (z : ℂ) :
    (kwShearX t z).im = z.im := by
  simp [kwShearX]

@[simp] theorem kwShearY_re (t : ℝ) (z : ℂ) :
    (kwShearY t z).re = z.re := by
  simp [kwShearY]

@[simp] theorem kwShearY_im (t : ℝ) (z : ℂ) :
    (kwShearY t z).im = z.im + t * z.re := by
  simp [kwShearY]

theorem kwComplexCross_shearX (t : ℝ) (z w : ℂ) :
    kwComplexCross (kwShearX t z) (kwShearX t w) =
      kwComplexCross z w := by
  unfold kwComplexCross
  simp only [kwShearX_re, kwShearX_im]
  ring

theorem kwComplexCross_shearY (t : ℝ) (z w : ℂ) :
    kwComplexCross (kwShearY t z) (kwShearY t w) =
      kwComplexCross z w := by
  unfold kwComplexCross
  simp only [kwShearY_re, kwShearY_im]
  ring

def kwShearXLinearEquiv (t : ℝ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun := kwShearX t
  invFun := kwShearX (-t)
  left_inv z := by
    apply Complex.ext
    · simp [kwShearX]
    · simp [kwShearX]
  right_inv z := by
    apply Complex.ext
    · simp [kwShearX]
    · simp [kwShearX]
  map_add' z w := by
    apply Complex.ext
    · simp [kwShearX]; ring
    · simp [kwShearX]
  map_smul' r z := by
    apply Complex.ext
    · simp [kwShearX]; ring
    · simp [kwShearX]

def kwShearYLinearEquiv (t : ℝ) : ℂ ≃ₗ[ℝ] ℂ where
  toFun := kwShearY t
  invFun := kwShearY (-t)
  left_inv z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]
  right_inv z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]
  map_add' z w := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]; ring
  map_smul' r z := by
    apply Complex.ext
    · simp [kwShearY]
    · simp [kwShearY]; ring


noncomputable def KWFiniteSimplePolygon.mapLinearEquiv
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) : KWFiniteSimplePolygon n where
  vertex := fun i ↦ e (polygon.vertex i)
  three_le := polygon.three_le
  vertex_injective := e.injective.comp polygon.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    apply polygon.vertex_not_strictly_between i j hji hjs
    exact e.toAffineEquiv.sbtw_map_iff.mp hs
  edgeInteriors_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi' : Sbtw ℝ (polygon.vertex i) (e.symm z)
        (polygon.vertex (i + 1)) := by
      apply e.toAffineEquiv.sbtw_map_iff.mp
      simpa using hzi
    have hzj' : Sbtw ℝ (polygon.vertex j) (e.symm z)
        (polygon.vertex (j + 1)) := by
      apply e.toAffineEquiv.sbtw_map_iff.mp
      simpa using hzj
    exact Set.disjoint_left.mp (polygon.edgeInteriors_disjoint i j hij)
      hzi' hzj'

@[simp] theorem KWFiniteSimplePolygon.mapLinearEquiv_vertex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) (i : Fin n) :
    (polygon.mapLinearEquiv e).vertex i = e (polygon.vertex i) := rfl

@[simp] theorem KWFiniteSimplePolygon.mapLinearEquiv_edgeVector
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (e : ℂ ≃ₗ[ℝ] ℂ) (i : Fin n) :
    (polygon.mapLinearEquiv e).edgeVector i = e (polygon.edgeVector i) := by
  simp only [KWFiniteSimplePolygon.edgeVector, mapLinearEquiv_vertex,
    map_sub]


private theorem exists_real_not_mem_finset (s : Finset ℝ) :
    ∃ t : ℝ, t ∉ s := by
  have hinfinite : (Set.univ \ (↑s : Set ℝ)).Infinite :=
    Set.infinite_univ.diff s.finite_toSet
  obtain ⟨t, _, ht⟩ := hinfinite.nonempty
  exact ⟨t, ht⟩


theorem KWFiniteSimplePolygon.exists_shearX_re_ne_zero
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ t : ℝ, ∀ i : Fin n, (kwShearX t (polygon.edgeVector i)).re ≠ 0 := by
  classical
  let forbidden : Finset ℝ := Finset.univ.image fun i : Fin n ↦
    -(polygon.edgeVector i).re / (polygon.edgeVector i).im
  obtain ⟨t, ht⟩ := exists_real_not_mem_finset forbidden
  refine ⟨t, ?_⟩
  intro i hzero
  by_cases him : (polygon.edgeVector i).im = 0
  · have hre : (polygon.edgeVector i).re = 0 := by
      rw [kwShearX_re, him, mul_zero, add_zero] at hzero
      exact hzero
    have hedge : polygon.edgeVector i = 0 := by
      apply Complex.ext
      · exact hre
      · exact him
    unfold KWFiniteSimplePolygon.edgeVector at hedge
    exact polygon.vertex_injective.ne (polygon.add_one_ne_self i) (sub_eq_zero.mp hedge)
  · apply ht
    simp only [forbidden, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [kwShearX_re] at hzero
    symm
    apply (eq_div_iff him).mpr
    linarith



theorem KWFiniteSimplePolygon.exists_generic_shear
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ tx ty : ℝ, ∀ i : Fin n,
      (kwShearY ty (kwShearX tx (polygon.edgeVector i))).re ≠ 0 ∧
      (kwShearY ty (kwShearX tx (polygon.edgeVector i))).im ≠ 0 := by
  classical
  obtain ⟨tx, hx⟩ := polygon.exists_shearX_re_ne_zero
  let forbidden : Finset ℝ := Finset.univ.image fun i : Fin n ↦
    -(kwShearX tx (polygon.edgeVector i)).im /
      (kwShearX tx (polygon.edgeVector i)).re
  obtain ⟨ty, hty⟩ := exists_real_not_mem_finset forbidden
  refine ⟨tx, ty, ?_⟩
  intro i
  constructor
  · simpa using hx i
  · intro hzero
    apply hty
    simp only [forbidden, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [kwShearY_im] at hzero
    symm
    apply (eq_div_iff (hx i)).mpr
    linarith


theorem KWFiniteSimplePolygon.exists_generic_coordinate_polygon
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ tx ty : ℝ,
      let e := (kwShearXLinearEquiv tx).trans (kwShearYLinearEquiv ty)
      ∀ i : Fin n,
        ((polygon.mapLinearEquiv e).edgeVector i).re ≠ 0 ∧
        ((polygon.mapLinearEquiv e).edgeVector i).im ≠ 0 := by
  obtain ⟨tx, ty, hgeneric⟩ := polygon.exists_generic_shear
  refine ⟨tx, ty, ?_⟩
  dsimp only
  intro i
  rw [polygon.mapLinearEquiv_edgeVector]
  simpa only [LinearEquiv.trans_apply, kwShearXLinearEquiv,
    kwShearYLinearEquiv] using hgeneric i

end StatMech.FrontierA
