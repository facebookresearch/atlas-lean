/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.PeriodicDualShift

/-!
# Plane positions of the triangular and hexagonal lattices

Vertex positions in `ℂ`, straight-segment edges, and their basic geometric properties for the
triangular and hexagonal lattices.

## i. Overview

The site `z : Site 2` sits at `z 0 + z 1 * I`, so the period lattice is `ℤ[I]` acting by
translation. In these (sheared) coordinates the triangular lattice has edge steps `(1, 0)`,
`(0, 1)`, `(-1, 1)`. The hexagonal vertex `(z, b)` sits at the centre of the corresponding
triangular face, `z ± (1 + I) / 3`. Edges are drawn as straight segments. This file proves that
the vertex maps are injective, translation covariant and proper (finitely many vertices in a
ball), that edges have length at most `2`, and that the segment drawing is locally finite. All
results are proved unconditionally; that two distinct segments meet only at shared endpoints is
proved in `TriHex.PeriodicStraightIntersection`.

## ii. Key results

- `triangularPlaneVertex`, `hexagonalPlaneVertex` : vertex embeddings into `ℂ`.
- `triangularStraightEdgeArc`, `hexagonalStraightEdgeArc` : straight edge arcs.
- `triangularStraightEdgeArc_locallyFinite`, `hexagonalStraightEdgeArc_locallyFinite` : a
  compact set meets finitely many edges.

## iii. Table of contents

- A. Periods and plane coordinates
- B. Triangular vertices and edges
- C. Hexagonal vertices and edges
- D. Local finiteness of the edge drawings

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6.
- V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
  model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), 511–542.
-/

@[expose] public section

open Set

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

/-! ## A. Periods and plane coordinates -/

/-- The period map `z ↦ z 0 + z 1 * I` from `Site 2` to `ℂ`. -/
def triHexPlanePeriod : AddMonoidHom (Site 2) Complex where
  toFun z := (z 0 : Real) + (z 1 : Real) * Complex.I
  map_zero' := by simp
  map_add' z w := by
    apply Complex.ext <;> simp

@[simp] lemma triHexPlanePeriod_re (z : Site 2) :
    (triHexPlanePeriod z).re = z 0 := by
  simp [triHexPlanePeriod]

@[simp] lemma triHexPlanePeriod_im (z : Site 2) :
    (triHexPlanePeriod z).im = z 1 := by
  simp [triHexPlanePeriod]

lemma triHexPlanePeriod_injective :
    Function.Injective triHexPlanePeriod := by
  intro z w h
  funext i
  fin_cases i
  · have hreal : (z 0 : Real) = (w 0 : Real) := by
      simpa using congrArg Complex.re h
    exact_mod_cast hreal
  · have himag : (z 1 : Real) = (w 1 : Real) := by
      simpa using congrArg Complex.im h
    exact_mod_cast himag

/-- The real-linear identification of `ℂ` with `Fin 2 → ℝ` (real and imaginary parts). -/
noncomputable def triHexPlaneCoordinates :
    Complex ≃L[Real] (Fin 2 -> Real) :=
  Complex.equivRealProdCLM.trans
    (ContinuousLinearEquiv.finTwoArrow Real Real).symm

@[simp] lemma triHexPlaneCoordinates_apply_zero (z : Complex) :
    triHexPlaneCoordinates z 0 = z.re := by
  rfl

@[simp] lemma triHexPlaneCoordinates_apply_one (z : Complex) :
    triHexPlaneCoordinates z 1 = z.im := by
  rfl

@[simp] lemma triHexPlaneCoordinates_period
    (z : Site 2) (i : Fin 2) :
    triHexPlaneCoordinates (triHexPlanePeriod z) i = z i := by
  fin_cases i <;> simp

/-! ## B. Triangular vertices and edges -/

/-- Plane position of the triangular site `z`: the period point `z 0 + z 1 * I`. -/
def triangularPlaneVertex : Site 2 ↪ Complex where
  toFun := triHexPlanePeriod
  inj' := triHexPlanePeriod_injective

@[simp] lemma triangularPlaneVertex_apply (z : Site 2) :
    triangularPlaneVertex z = triHexPlanePeriod z := rfl

@[simp] lemma triangularPlaneVertex_shift (z x : Site 2) :
    triangularPlaneVertex (triangular.shift z x) =
      triangularPlaneVertex x + triHexPlanePeriod z := by
  change triHexPlanePeriod (x + z) =
    triHexPlanePeriod x + triHexPlanePeriod z
  exact map_add triHexPlanePeriod x z

lemma triHexPlanePeriod_bounded_finite (R : Real) :
    {z : Site 2 | ‖triHexPlanePeriod z‖ <= R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply (Set.Finite.pi (fun _ : Fin 2 =>
    Set.finite_Icc (-(N : Int)) (N : Int))).subset
  intro z hz
  rw [Set.mem_pi]
  intro i _hi
  have habs : |(z i : Real)| <= ‖triHexPlanePeriod z‖ := by
    fin_cases i
    · simpa using Complex.abs_re_le_norm (triHexPlanePeriod z)
    · simpa using Complex.abs_im_le_norm (triHexPlanePeriod z)
  have hlt : |(z i : Real)| < N := habs.trans_lt (hz.trans_lt hN)
  rw [abs_lt] at hlt
  constructor
  · exact_mod_cast hlt.1.le
  · exact_mod_cast hlt.2.le

lemma triangularPlaneVertex_bounded_finite (R : Real) :
    {z : Site 2 | ‖(triangularPlaneVertex z : Complex)‖ <= R}.Finite := by
  simpa using triHexPlanePeriod_bounded_finite R

/-- The triangular edge `xy` drawn as the straight segment between its endpoints. -/
noncomputable def triangularStraightEdgeArc {x y : Site 2}
    (_hxy : triangularGraph.Adj x y) :
    Path (triangularPlaneVertex x) (triangularPlaneVertex y) :=
  Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y)

lemma triangularStraightEdgeArc_injective {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    Function.Injective (triangularStraightEdgeArc hxy) := by
  apply Path.segment_injective_of_ne
  exact triangularPlaneVertex.injective.ne hxy.ne

lemma triangularStraightEdgeArc_symm {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    Set.range (triangularStraightEdgeArc hxy.symm) =
      Set.range (triangularStraightEdgeArc hxy) := by
  simp only [triangularStraightEdgeArc, Path.range_segment]
  exact segment_symm Real _ _

lemma triangularStraightEdgeArc_shift
    (z : Site 2) {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    Set.range (triangularStraightEdgeArc
        ((triangular.shift_adj z x y).2 hxy)) =
      (fun p => p + triHexPlanePeriod z) ''
        Set.range (triangularStraightEdgeArc hxy) := by
  simp only [triangularStraightEdgeArc, Path.range_segment,
    triangularPlaneVertex_shift]
  simpa [add_comm] using
    (segment_translate_image Real (triHexPlanePeriod z)
      (triangularPlaneVertex x) (triangularPlaneVertex y)).symm

lemma triangularStraightEdge_length_le_two {x y : Site 2}
    (hxy : triangularGraph.Adj x y) :
    dist (triangularPlaneVertex x) (triangularPlaneVertex y) <= 2 := by
  rw [triangularGraph_adj, triangularAdj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · have hy : y = x + triangularStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst y
    change dist (triHexPlanePeriod x)
      (triHexPlanePeriod (x + triangularStep i)) <= 2
    calc
      dist (triHexPlanePeriod x)
          (triHexPlanePeriod (x + triangularStep i)) =
          ‖triHexPlanePeriod (triangularStep i)‖ := by
        rw [map_add, dist_eq_norm]
        have heq : triHexPlanePeriod x -
            (triHexPlanePeriod x + triHexPlanePeriod (triangularStep i)) =
              -triHexPlanePeriod (triangularStep i) := by abel
        rw [heq, norm_neg]
      _ <= 2 := by
        calc
          ‖triHexPlanePeriod (triangularStep i)‖ <=
              |(triHexPlanePeriod (triangularStep i)).re| +
                |(triHexPlanePeriod (triangularStep i)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ <= 2 := by
            fin_cases i <;> norm_num [triHexPlanePeriod, triangularStep]
  · have hx : x = y + triangularStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst x
    change dist (triHexPlanePeriod (y + triangularStep i))
      (triHexPlanePeriod y) <= 2
    calc
      dist (triHexPlanePeriod (y + triangularStep i))
          (triHexPlanePeriod y) =
          ‖triHexPlanePeriod (triangularStep i)‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        calc
          ‖triHexPlanePeriod (triangularStep i)‖ <=
              |(triHexPlanePeriod (triangularStep i)).re| +
                |(triHexPlanePeriod (triangularStep i)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
          _ <= 2 := by
            fin_cases i <;> norm_num [triHexPlanePeriod, triangularStep]

/-! ## C. Hexagonal vertices and edges -/

/-- Offset of a hexagonal vertex from its base site: `(1 + I) / 3` for black and `-(1 + I) / 3` for
white vertices, the centres of the two triangular faces. -/
noncomputable def hexagonalFaceCenterOffset (white : Bool) : Complex :=
  if white then -(1 / 3 : Real) - (1 / 3 : Real) * Complex.I
  else (1 / 3 : Real) + (1 / 3 : Real) * Complex.I

@[simp] lemma hexagonalFaceCenterOffset_false :
    hexagonalFaceCenterOffset false =
      (1 / 3 : Real) + (1 / 3 : Real) * Complex.I := rfl

@[simp] lemma hexagonalFaceCenterOffset_true :
    hexagonalFaceCenterOffset true =
      -(1 / 3 : Real) - (1 / 3 : Real) * Complex.I := rfl

lemma hexagonalFaceCenterOffset_norm_le_one (white : Bool) :
    ‖hexagonalFaceCenterOffset white‖ <= 1 := by
  cases white
  · calc
      ‖hexagonalFaceCenterOffset false‖ <=
          ‖((1 / 3 : Real) : Complex)‖ +
            ‖((1 / 3 : Real) : Complex) * Complex.I‖ := by
        simpa [hexagonalFaceCenterOffset] using
          norm_add_le ((1 / 3 : Real) : Complex)
            (((1 / 3 : Real) : Complex) * Complex.I)
      _ <= 1 := by norm_num [norm_mul]
  · calc
      ‖hexagonalFaceCenterOffset true‖ <=
          ‖(-((1 / 3 : Real) : Complex))‖ +
            ‖((1 / 3 : Real) : Complex) * Complex.I‖ := by
        simpa [hexagonalFaceCenterOffset] using
          norm_sub_le (-((1 / 3 : Real) : Complex))
            (((1 / 3 : Real) : Complex) * Complex.I)
      _ <= 1 := by norm_num [norm_mul]

/-- Plane position of the hexagonal vertex `u`: base site plus face-centre offset. -/
noncomputable def hexagonalPlaneVertexValue (u : HexVertex) : Complex :=
  triHexPlanePeriod u.1 + hexagonalFaceCenterOffset u.2

lemma hexagonalPlaneVertexValue_injective :
    Function.Injective hexagonalPlaneVertexValue := by
  rintro ⟨x, xb⟩ ⟨y, yb⟩ h
  cases xb <;> cases yb
  · apply Prod.ext
    · apply triHexPlanePeriod_injective
      exact add_right_cancel h
    · rfl
  · have hre : (x 0 : Real) + 1 / 3 = (y 0 : Real) - 1 / 3 := by
      have h' := congrArg Complex.re h
      simp [hexagonalPlaneVertexValue, hexagonalFaceCenterOffset] at h'
      linarith
    have hre' : (3 : Real) * (x 0 : Real) + 1 =
        (3 : Real) * (y 0 : Real) - 1 := by
      linarith
    have hreInt : (3 : Int) * x 0 + 1 = (3 : Int) * y 0 - 1 := by
      exact_mod_cast hre'
    omega
  · have hre : (x 0 : Real) - 1 / 3 = (y 0 : Real) + 1 / 3 := by
      have h' := congrArg Complex.re h
      simp [hexagonalPlaneVertexValue, hexagonalFaceCenterOffset] at h'
      linarith
    have hre' : (3 : Real) * (x 0 : Real) - 1 =
        (3 : Real) * (y 0 : Real) + 1 := by
      linarith
    have hreInt : (3 : Int) * x 0 - 1 = (3 : Int) * y 0 + 1 := by
      exact_mod_cast hre'
    omega
  · apply Prod.ext
    · apply triHexPlanePeriod_injective
      exact add_right_cancel h
    · rfl

/-- Plane position of a hexagonal vertex, as an embedding `HexVertex ↪ ℂ`. -/
noncomputable def hexagonalPlaneVertex : HexVertex ↪ Complex where
  toFun := hexagonalPlaneVertexValue
  inj' := hexagonalPlaneVertexValue_injective

@[simp] lemma hexagonalPlaneVertex_apply (u : HexVertex) :
    hexagonalPlaneVertex u = hexagonalPlaneVertexValue u := rfl

@[simp] lemma hexagonalPlaneVertex_shift (z : Site 2) (u : HexVertex) :
    hexagonalPlaneVertex (hexagonal.shift z u) =
      hexagonalPlaneVertex u + triHexPlanePeriod z := by
  rcases u with ⟨x, b⟩
  change triHexPlanePeriod (x + z) + hexagonalFaceCenterOffset b =
    (triHexPlanePeriod x + hexagonalFaceCenterOffset b) +
      triHexPlanePeriod z
  rw [map_add]
  abel

lemma hexagonalPlaneVertex_bounded_finite (R : Real) :
    {u : HexVertex | ‖(hexagonalPlaneVertex u : Complex)‖ <= R}.Finite := by
  let K : Set (Site 2) := {z | ‖triHexPlanePeriod z‖ <= R + 1}
  have hK : K.Finite := triHexPlanePeriod_bounded_finite (R + 1)
  apply (hK.prod Set.finite_univ).subset
  intro u hu
  constructor
  · change ‖triHexPlanePeriod u.1‖ <= R + 1
    have hsplit : triHexPlanePeriod u.1 =
        hexagonalPlaneVertexValue u - hexagonalFaceCenterOffset u.2 := by
      simp [hexagonalPlaneVertexValue]
    rw [hsplit]
    exact (norm_sub_le _ _).trans
      (add_le_add hu (hexagonalFaceCenterOffset_norm_le_one u.2))
  · simp

/-- The hexagonal edge `uv` drawn as the straight segment between its endpoints. -/
noncomputable def hexagonalStraightEdgeArc {u v : HexVertex}
    (_huv : hexagonalGraph.Adj u v) :
    Path (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) :=
  Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v)

lemma hexagonalStraightEdgeArc_injective {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    Function.Injective (hexagonalStraightEdgeArc huv) := by
  apply Path.segment_injective_of_ne
  exact hexagonalPlaneVertex.injective.ne huv.ne

lemma hexagonalStraightEdgeArc_symm {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    Set.range (hexagonalStraightEdgeArc huv.symm) =
      Set.range (hexagonalStraightEdgeArc huv) := by
  simp only [hexagonalStraightEdgeArc, Path.range_segment]
  exact segment_symm Real _ _

lemma hexagonalStraightEdgeArc_shift
    (z : Site 2) {u v : HexVertex} (huv : hexagonalGraph.Adj u v) :
    Set.range (hexagonalStraightEdgeArc
        ((hexagonal.shift_adj z u v).2 huv)) =
      (fun p => p + triHexPlanePeriod z) ''
        Set.range (hexagonalStraightEdgeArc huv) := by
  simp only [hexagonalStraightEdgeArc, Path.range_segment,
    hexagonalPlaneVertex_shift]
  simpa [add_comm] using
    (segment_translate_image Real (triHexPlanePeriod z)
      (hexagonalPlaneVertex u) (hexagonalPlaneVertex v)).symm

lemma hexagonalStraightEdge_length_le_two {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    dist (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) <= 2 := by
  rw [hexagonalGraph_adj, hexagonalAdj] at huv
  rcases huv with ⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩
  · rcases u with ⟨x, xb⟩
    rcases v with ⟨y, yb⟩
    change xb = false at hu
    change yb = true at hv
    subst xb
    subst yb
    have hy : y = x + hexagonalStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst y
    change dist
      (triHexPlanePeriod x + hexagonalFaceCenterOffset false)
      (triHexPlanePeriod (x + hexagonalStep i) +
        hexagonalFaceCenterOffset true) <= 2
    calc
      _ = ‖hexagonalFaceCenterOffset false -
          (triHexPlanePeriod (hexagonalStep i) +
            hexagonalFaceCenterOffset true)‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        let d := hexagonalFaceCenterOffset false -
          (triHexPlanePeriod (hexagonalStep i) +
            hexagonalFaceCenterOffset true)
        calc
          ‖hexagonalFaceCenterOffset false -
              (triHexPlanePeriod (hexagonalStep i) +
                hexagonalFaceCenterOffset true)‖ <= |d.re| + |d.im| :=
            Complex.norm_le_abs_re_add_abs_im d
          _ <= 2 := by
            fin_cases i <;>
              norm_num [d, hexagonalFaceCenterOffset, triHexPlanePeriod,
                hexagonalStep]
  · rcases u with ⟨x, xb⟩
    rcases v with ⟨y, yb⟩
    change yb = false at hv
    change xb = true at hu
    subst xb
    subst yb
    have hx : x = y + hexagonalStep i := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    subst x
    change dist
      (triHexPlanePeriod (y + hexagonalStep i) +
        hexagonalFaceCenterOffset true)
      (triHexPlanePeriod y + hexagonalFaceCenterOffset false) <= 2
    calc
      _ = ‖triHexPlanePeriod (hexagonalStep i) +
          hexagonalFaceCenterOffset true -
            hexagonalFaceCenterOffset false‖ := by
        rw [map_add, dist_eq_norm]
        congr 1
        abel
      _ <= 2 := by
        let d := triHexPlanePeriod (hexagonalStep i) +
          hexagonalFaceCenterOffset true -
            hexagonalFaceCenterOffset false
        calc
          ‖triHexPlanePeriod (hexagonalStep i) +
              hexagonalFaceCenterOffset true -
                hexagonalFaceCenterOffset false‖ <= |d.re| + |d.im| :=
            Complex.norm_le_abs_re_add_abs_im d
          _ <= 2 := by
            fin_cases i <;>
              norm_num [d, hexagonalFaceCenterOffset, triHexPlanePeriod,
                hexagonalStep]

/-! ## D. Local finiteness of the edge drawings -/

private lemma segment_endpoints_norm_le_add_two
    (a b : Complex) (t : unitInterval) (R : Real)
    (hpoint : ‖Path.segment a b t‖ <= R)
    (hlength : dist a b <= 2) :
    ‖a‖ <= R + 2 ∧ ‖b‖ <= R + 2 := by
  have ht : ‖(t : Real)‖ <= 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg t.2.1]
    exact t.2.2
  have hOneSub : ‖(1 : Real) - t‖ <= 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.2.2)]
    linarith [t.2.1]
  have hleft : dist a (Path.segment a b t) <= 2 := by
    rw [Path.segment_apply, dist_left_lineMap]
    calc
      ‖(t : Real)‖ * dist a b <= 1 * 2 :=
        mul_le_mul ht hlength (dist_nonneg) (by norm_num)
      _ = 2 := by norm_num
  have hright : dist b (Path.segment a b t) <= 2 := by
    rw [Path.segment_apply, dist_right_lineMap]
    calc
      ‖(1 : Real) - t‖ * dist a b <= 1 * 2 :=
        mul_le_mul hOneSub hlength (dist_nonneg) (by norm_num)
      _ = 2 := by norm_num
  constructor
  · calc
      ‖a‖ = dist a 0 := by rw [dist_zero_right]
      _ <= dist a (Path.segment a b t) +
          dist (Path.segment a b t) 0 := dist_triangle _ _ _
      _ <= 2 + R := by
        rw [dist_zero_right]
        exact add_le_add hleft hpoint
      _ = R + 2 := by ring
  · calc
      ‖b‖ = dist b 0 := by rw [dist_zero_right]
      _ <= dist b (Path.segment a b t) +
          dist (Path.segment a b t) 0 := dist_triangle _ _ _
      _ <= 2 + R := by
        rw [dist_zero_right]
        exact add_le_add hright hpoint
      _ = R + 2 := by ring

lemma triangularStraightEdgeArc_locallyFinite
    (K : Set Complex) (hK : IsCompact K) :
    {xy : Site 2 × Site 2 | ∃ hxy : triangularGraph.Adj xy.1 xy.2,
      (Set.range (triangularStraightEdgeArc hxy) ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B : Set (Site 2) :=
    {x | ‖(triangularPlaneVertex x : Complex)‖ <= R + 2}
  have hB : B.Finite := triangularPlaneVertex_bounded_finite (R + 2)
  apply (hB.prod hB).subset
  rintro ⟨x, y⟩ ⟨hxy, q, hqArc, hqK⟩
  obtain ⟨t, rfl⟩ := hqArc
  have hpoint :
      ‖triangularStraightEdgeArc hxy t‖ <= R := by
    have hmem := hR hqK
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hend := segment_endpoints_norm_le_add_two
    (triangularPlaneVertex x) (triangularPlaneVertex y) t R
    (by simpa [triangularStraightEdgeArc] using hpoint)
    (triangularStraightEdge_length_le_two hxy)
  exact hend

lemma hexagonalStraightEdgeArc_locallyFinite
    (K : Set Complex) (hK : IsCompact K) :
    {uv : HexVertex × HexVertex | ∃ huv : hexagonalGraph.Adj uv.1 uv.2,
      (Set.range (hexagonalStraightEdgeArc huv) ∩ K).Nonempty}.Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Complex)
  let B : Set HexVertex :=
    {u | ‖(hexagonalPlaneVertex u : Complex)‖ <= R + 2}
  have hB : B.Finite := hexagonalPlaneVertex_bounded_finite (R + 2)
  apply (hB.prod hB).subset
  rintro ⟨u, v⟩ ⟨huv, q, hqArc, hqK⟩
  obtain ⟨t, rfl⟩ := hqArc
  have hpoint :
      ‖hexagonalStraightEdgeArc huv t‖ <= R := by
    have hmem := hR hqK
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem
  have hend := segment_endpoints_norm_le_add_two
    (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) t R
    (by simpa [hexagonalStraightEdgeArc] using hpoint)
    (hexagonalStraightEdge_length_le_two huv)
  exact hend

end StatMech.FK.PeriodicPlanar
