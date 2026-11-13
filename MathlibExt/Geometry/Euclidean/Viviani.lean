/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.SignedDist
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.LinearAlgebra.AffineSpace.MidpointZero
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Viviani's theorem

This file proves that the sum of the distances from an interior point of an equilateral triangle
to its three side lines equals the triangle's altitude.
-/

namespace MetaMathlibExt

@[expose]
public section

private lemma viviani_range_points {X : Type*} (A B C : X) :
    Set.range (![A, B, C] : Fin 3 → X) = {A, B, C} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

private lemma viviani_affineIndependent
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (hP : P ∈ interior (convexHull ℝ {A, B, C})) :
    AffineIndependent ℝ (![A, B, C] : Fin 3 → EuclideanSpace ℝ (Fin 2)) := by
  have hspan : affineSpan ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior ⟨P, hP⟩
  rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (n := 2) (by norm_num)]
  have hvspan :
      vectorSpan ℝ (Set.range (![A, B, C] : Fin 3 → EuclideanSpace ℝ (Fin 2))) = ⊤ := by
    rw [← direction_affineSpan, viviani_range_points, hspan, AffineSubspace.direction_top]
  rw [hvspan, finrank_top]
  norm_num

private lemma viviani_infDist_eq_dist_midpoint
    (A B C : EuclideanSpace ℝ (Fin 2)) (h : dist A B = dist A C) :
    Metric.infDist A ↑(affineSpan ℝ {B, C}) = dist A (midpoint ℝ B C) := by
  let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := affineSpan ℝ {B, C}
  have hmid : midpoint ℝ B C ∈ L := by
    rw [← lineMap_inv_two]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hperp : A ∈ AffineSubspace.perpBisector B C :=
    AffineSubspace.mem_perpBisector_iff_dist_eq.mpr h
  have horth : A -ᵥ midpoint ℝ B C ∈ L.directionᗮ := by
    change A -ᵥ midpoint ℝ B C ∈ (affineSpan ℝ {B, C}).directionᗮ
    rw [direction_affineSpan, vectorSpan_pair_rev,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact AffineSubspace.mem_perpBisector_iff_inner_eq_zero'.mp hperp
  have hproj :
      (EuclideanGeometry.orthogonalProjection L A : EuclideanSpace ℝ (Fin 2)) = midpoint ℝ B C :=
    EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr ⟨hmid, horth⟩
  change Metric.infDist A (L : Set (EuclideanSpace ℝ (Fin 2))) = _
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist L A, hproj]

private lemma viviani_equal_altitudes
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hABBC : dist A B = dist B C) (hBCCA : dist B C = dist C A) :
    Metric.infDist B ↑(affineSpan ℝ {C, A}) =
        Metric.infDist A ↑(affineSpan ℝ {B, C}) ∧
      Metric.infDist C ↑(affineSpan ℝ {A, B}) =
        Metric.infDist A ↑(affineSpan ℝ {B, C}) := by
  have hBC : dist B C = dist A B := hABBC.symm
  have hCA : dist C A = dist A B := hBCCA.symm.trans hBC
  have hAC : dist A C = dist A B := (dist_comm A C).trans hCA
  have hBA : dist B A = dist A B := dist_comm B A
  have hCB : dist C B = dist A B := (dist_comm C B).trans hBC
  have hA := viviani_infDist_eq_dist_midpoint A B C hAC.symm
  have hB := viviani_infDist_eq_dist_midpoint B C A (hBC.trans hBA.symm)
  have hC := viviani_infDist_eq_dist_midpoint C A B (hCA.trans hCB.symm)
  have ha :=
    EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq A B C
  have hb :=
    EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq B C A
  have hc :=
    EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq C A B
  rw [hAC, hBC] at ha
  rw [hBC, hBA, hCA] at hb
  rw [hCA, hCB] at hc
  have hmidB : dist B (midpoint ℝ C A) = dist A (midpoint ℝ B C) := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    linarith
  have hmidC : dist C (midpoint ℝ A B) = dist A (midpoint ℝ B C) := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    linarith
  exact ⟨hB.trans (hmidB.trans hA.symm), hC.trans (hmidC.trans hA.symm)⟩

private lemma viviani_face_sets {X : Type*} (A B C : X) :
    (![A, B, C] : Fin 3 → X) '' ({0}ᶜ : Set (Fin 3)) = {B, C} ∧
      (![A, B, C] : Fin 3 → X) '' ({1}ᶜ : Set (Fin 3)) = {C, A} ∧
      (![A, B, C] : Fin 3 → X) '' ({2}ᶜ : Set (Fin 3)) = {A, B} := by
  constructor
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp, by simp⟩
      · exact ⟨2, by simp, by simp⟩
  constructor
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨2, by simp, by simp⟩
      · exact ⟨0, by simp, by simp⟩
  · ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨1, by simp, by simp⟩

private lemma viviani_infDist_face_eq_weight_mul_height
    (s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)))
    (P : EuclideanSpace ℝ (Fin 2)) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) (hP : Finset.univ.affineCombination ℝ s.points w = P)
    (i : Fin 3) (hwi : 0 ≤ w i) :
    Metric.infDist P ↑(affineSpan ℝ (s.points '' {i}ᶜ)) = w i * s.height i := by
  have hpSpan : P ∈ affineSpan ℝ (Set.range s.points) := by
    rw [← hP]
    exact affineCombination_mem_affineSpan_of_nonempty hw _
  have hsigned : s.signedInfDist i P = w i * s.height i := by
    rw [← hP]
    simpa [Affine.Simplex.height, Affine.Simplex.altitudeFoot, dist_eq_norm_vsub] using
      s.signedInfDist_affineCombination i hw
  have habs := s.abs_signedInfDist_eq_dist_of_mem_affineSpan_range i hpSpan
  have hproj :
      dist P ((s.faceOpposite i).orthogonalProjectionSpan P) =
        Metric.infDist P ↑(affineSpan ℝ (s.points '' {i}ᶜ)) := by
    simpa only [Affine.Simplex.orthogonalProjectionSpan, s.range_faceOpposite_points] using
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist
        (affineSpan ℝ (Set.range (s.faceOpposite i).points)) P
  calc
    Metric.infDist P ↑(affineSpan ℝ (s.points '' {i}ᶜ)) =
        dist P ((s.faceOpposite i).orthogonalProjectionSpan P) := hproj.symm
    _ = |s.signedInfDist i P| := habs.symm
    _ = w i * s.height i := by
      rw [hsigned, abs_of_nonneg (mul_nonneg hwi (s.height_pos i).le)]

private lemma viviani_infDist_vertex_face_eq_height
    (s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3) :
    Metric.infDist (s.points i) ↑(affineSpan ℝ (s.points '' {i}ᶜ)) = s.height i := by
  rw [Affine.Simplex.height, Affine.Simplex.altitudeFoot,
    Affine.Simplex.orthogonalProjectionSpan]
  symm
  simpa only [s.range_faceOpposite_points] using
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist
      (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)

/-- **Viviani's theorem.** Let $A$, $B$, $C$ be points of the Euclidean plane $\mathbb{R}^2$ with
$AB = BC = CA$, and let $P$ be a point of the interior of the convex hull of
$\lbrace A, B, C \rbrace$. Then the sum of the distances from $P$ to the lines $AB$, $BC$ and
$CA$ equals the distance from $A$ to the line $BC$, the altitude of the triangle.

No positivity hypothesis on the side length is needed: since $P$ is an interior point, the
points $A$, $B$, $C$ are affinely independent, so the triangle is nondegenerate.

Proof: Following the barycentric-coordinate area decomposition in Wikipedia, "Viviani's theorem"
(Proof section), we express the three distances as barycentric weights times a common height.

Proves `Wanted` entry `viviani` (via the source-shaped wrapper `viviani`
below).

Source: https://en.wikipedia.org/wiki/Viviani%27s_theorem.
-/
theorem viviani_general : ∀ (A B C P : EuclideanSpace ℝ (Fin 2)),
  dist A B = dist B C → dist B C = dist C A →
  P ∈ interior (convexHull ℝ {A, B, C}) →
  Metric.infDist P ↑(affineSpan ℝ {A, B}) +
    Metric.infDist P ↑(affineSpan ℝ {B, C}) +
    Metric.infDist P ↑(affineSpan ℝ {C, A}) =
    Metric.infDist A ↑(affineSpan ℝ {B, C}) := by
  rintro A B C P hABBC hBCCA hP
  let s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![A, B, C], viviani_affineIndependent A B C P hP⟩
  have hsRange : Set.range s.points = {A, B, C} := by
    exact viviani_range_points A B C
  have hsSpan : affineSpan ℝ (Set.range s.points) = ⊤ := by
    rw [hsRange]
    exact affineSpan_eq_top_of_nonempty_interior ⟨P, hP⟩
  let b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨s.points, s.independent, hsSpan⟩
  let w : Fin 3 → ℝ := fun i ↦ b.coord i P
  have hw : ∑ i, w i = 1 := b.sum_coord_apply_eq_one P
  have hcomb : Finset.univ.affineCombination ℝ s.points w = P := by
    exact b.affineCombination_coord_eq_self P
  have hPb : P ∈ interior (convexHull ℝ (Set.range b)) := by
    change P ∈ interior (convexHull ℝ (Set.range s.points))
    simpa only [hsRange] using hP
  have hcoord : ∀ i, 0 < w i := by
    rw [b.interior_convexHull] at hPb
    change ∀ i, 0 < b.coord i P at hPb
    simpa only [w] using hPb
  have hfaces := viviani_face_sets A B C
  have hface0 : s.points '' ({0}ᶜ : Set (Fin 3)) = {B, C} := hfaces.1
  have hface1 : s.points '' ({1}ᶜ : Set (Fin 3)) = {C, A} := hfaces.2.1
  have hface2 : s.points '' ({2}ᶜ : Set (Fin 3)) = {A, B} := hfaces.2.2
  have hd0 :=
    viviani_infDist_face_eq_weight_mul_height s P w hw hcomb 0 (hcoord 0).le
  have hd1 :=
    viviani_infDist_face_eq_weight_mul_height s P w hw hcomb 1 (hcoord 1).le
  have hd2 :=
    viviani_infDist_face_eq_weight_mul_height s P w hw hcomb 2 (hcoord 2).le
  rw [hface0] at hd0
  rw [hface1] at hd1
  rw [hface2] at hd2
  have hv0 : Metric.infDist A ↑(affineSpan ℝ {B, C}) = s.height 0 := by
    simpa only [show s.points 0 = A by rfl, hface0] using
      viviani_infDist_vertex_face_eq_height s 0
  have hv1 : Metric.infDist B ↑(affineSpan ℝ {C, A}) = s.height 1 := by
    simpa only [show s.points 1 = B by rfl, hface1] using
      viviani_infDist_vertex_face_eq_height s 1
  have hv2 : Metric.infDist C ↑(affineSpan ℝ {A, B}) = s.height 2 := by
    simpa only [show s.points 2 = C by rfl, hface2] using
      viviani_infDist_vertex_face_eq_height s 2
  have halt := viviani_equal_altitudes A B C hABBC hBCCA
  have hh1 : s.height 1 = s.height 0 := hv1.symm.trans (halt.1.trans hv0)
  have hh2 : s.height 2 = s.height 0 := hv2.symm.trans (halt.2.trans hv0)
  have hwsum : w 0 + w 1 + w 2 = 1 := by
    simpa only [Fin.sum_univ_three] using hw
  rw [hd2, hd0, hd1, hv0, hh1, hh2]
  calc
    w 2 * s.height 0 + w 0 * s.height 0 + w 1 * s.height 0 =
        (w 0 + w 1 + w 2) * s.height 0 := by ring
    _ = s.height 0 := by rw [hwsum, one_mul]

/-- **Viviani's theorem with a positive side length.** Let $A$, $B$, $C$ be points of the
Euclidean plane $\mathbb{R}^2$ with $AB = BC = CA$ and $AB > 0$, and let $P$ be a point of the
interior of the convex hull of $\lbrace A, B, C \rbrace$. Then the sum of the distances from
$P$ to the lines $AB$, $BC$ and $CA$ equals the distance from $A$ to the line $BC$, the
altitude of the triangle.

The hypothesis $AB > 0$ is not needed: Viviani's theorem gives the same conclusion without it.
-/
theorem viviani : ∀ (A B C P : EuclideanSpace ℝ (Fin 2)),
  dist A B = dist B C → dist B C = dist C A → 0 < dist A B →
  P ∈ interior (convexHull ℝ {A, B, C}) →
  Metric.infDist P ↑(affineSpan ℝ {A, B}) +
    Metric.infDist P ↑(affineSpan ℝ {B, C}) +
    Metric.infDist P ↑(affineSpan ℝ {C, A}) =
    Metric.infDist A ↑(affineSpan ℝ {B, C}) := by
  intro A B C P hABBC hBCCA _hpos hP
  exact viviani_general A B C P hABBC hBCCA hP

end

end MetaMathlibExt
