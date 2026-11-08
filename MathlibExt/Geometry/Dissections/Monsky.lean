/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Convex.BetweenList
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Side
import Mathlib.RingTheory.Valuation.LocalSubring
import MathlibExt.MeasureTheory.Measure.Lebesgue.TriangleArea

/-!
# Monsky's theorem

This file proves that every dissection of the unit square into equal-area triangles has an even
number of pieces.
-/

@[expose] public section

namespace MetaMathlibExt

open MeasureTheory Set

local notation "euclideanPlaneBasis" => EuclideanSpace.basisFun (Fin 2) ℝ

private lemma monsky_volume_interior_convexHull_triangle
    (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (interior (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))) =
      volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) := by
  apply measure_eq_measure_of_null_sdiff interior_subset
  have hclosed : IsClosed
      (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    (by simp : Set.Finite
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ |>.isClosed
  rw [← hclosed.frontier_eq]
  exact (convex_convexHull ℝ _).addHaar_frontier volume

private lemma monsky_sum_volume_eq_one
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c})
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∑ t ∈ T, volume t = 1 := by
  let square : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}
  have hcover' : (⋃ t ∈ T, t) = square := by
    simpa only [sUnion_eq_biUnion, Finset.mem_coe, square] using hcover
  have hinterior :
      volume (⋃ t ∈ T, interior t) = ∑ t ∈ T, volume (interior t) :=
    measure_biUnion_finset hdisjoint fun _ _ ↦ isOpen_interior.measurableSet
  have hinterior_volume : ∀ t ∈ T, volume (interior t) = volume t := by
    intro t ht
    obtain ⟨a, b, c, rfl⟩ := htriangle t ht
    exact monsky_volume_interior_convexHull_triangle a b c
  have hsub : (⋃ t ∈ T, interior t) ⊆ square := by
    rw [← hcover']
    intro x hx
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨t, ht, hxt⟩ := hx
    exact ⟨t, ht, interior_subset hxt⟩
  apply le_antisymm
  · calc
      ∑ t ∈ T, volume t = volume (⋃ t ∈ T, interior t) := by
        rw [hinterior]
        exact (Finset.sum_congr rfl hinterior_volume).symm
      _ ≤ volume square := measure_mono hsub
      _ = 1 := MeasureTheory.volume_unitSquare
  · calc
      1 = volume square := MeasureTheory.volume_unitSquare.symm
      _ = volume (⋃ t ∈ T, t) := congrArg volume hcover'.symm
      _ ≤ ∑ t ∈ T, volume t := measure_biUnion_finset_le T id

private lemma monsky_common_volume_eq_card_inv
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (hsum : ∑ t ∈ T, volume t = 1) (A : ENNReal)
    (hA : ∀ t ∈ T, volume t = A) :
    T.card ≠ 0 ∧ ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ) := by
  have hsumA : (T.card : ENNReal) * A = 1 := by
    calc
      (T.card : ENNReal) * A = ∑ _t ∈ T, A := by simp
      _ = ∑ t ∈ T, volume t := Finset.sum_congr rfl fun t ht ↦ (hA t ht).symm
      _ = 1 := hsum
  have hcard : T.card ≠ 0 := by
    intro hzero
    simp [hzero] at hsumA
  have hAreal : A.toReal = 1 / (T.card : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hcard)).2
    have hre := congrArg ENNReal.toReal hsumA
    simpa [mul_comm] using hre
  exact ⟨hcard, fun t ht ↦ by rw [hA t ht, hAreal]⟩

private lemma monsky_abs_det_eq_two_div_card
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    {t : Set (EuclideanSpace ℝ (Fin 2))} (ht : t ∈ T)
    (a b c : EuclideanSpace ℝ (Fin 2))
    (htabc : t = convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) :
    |(a - c).ofLp 0 * (b - c).ofLp 1 -
      (a - c).ofLp 1 * (b - c).ofLp 0| = 2 / (T.card : ℝ) := by
  have hv := hvolume t ht
  rw [htabc] at hv
  have hv' :
      (volume (convexHull ℝ
        ({c, a, b} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
        1 / (T.card : ℝ) := by
    have hset : ({c, a, b} : Set (EuclideanSpace ℝ (Fin 2))) = {a, b, c} := by
      ext x
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
    rw [hset]
    exact hv
  rw [MeasureTheory.toReal_volume_convexHull_triangle] at hv'
  calc
    |(a - c).ofLp 0 * (b - c).ofLp 1 - (a - c).ofLp 1 * (b - c).ofLp 0| =
        2 * (|(a - c).ofLp 0 * (b - c).ofLp 1 -
          (a - c).ofLp 1 * (b - c).ofLp 0| / 2) := by ring
    _ = 2 * (1 / (T.card : ℝ)) := by rw [hv']
    _ = 2 / (T.card : ℝ) := by ring

private lemma monsky_affineIndependent_of_det_ne_zero
    (a b c : EuclideanSpace ℝ (Fin 2))
    (hdet : (a - c).ofLp 0 * (b - c).ofLp 1 -
      (a - c).ofLp 1 * (b - c).ofLp 0 ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcollinear
  obtain ⟨p, v, hp⟩ :=
    (collinear_iff_exists_forall_eq_smul_vadd
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).1 hcollinear
  obtain ⟨ra, hra⟩ := hp a (by simp)
  obtain ⟨rb, hrb⟩ := hp b (by simp)
  obtain ⟨rc, hrc⟩ := hp c (by simp)
  apply hdet
  rw [hra, hrb, hrc]
  simp only [vadd_eq_add, add_sub_add_right_eq_sub, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

private lemma monsky_exists_vertices
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    ∃ p : Fin 3 → EuclideanSpace ℝ (Fin 2),
      t.1 = convexHull ℝ (Set.range p) := by
  obtain ⟨a, b, c, habc⟩ := htriangle t.1 t.2
  refine ⟨![a, b, c], ?_⟩
  rw [habc]
  congr 1
  ext x
  simp [Matrix.range_cons]
  tauto

private noncomputable def monskyVertices
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  Classical.choose (monsky_exists_vertices T htriangle t)

private lemma monsky_vertices_spec
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (t : ↑T) :
    t.1 = convexHull ℝ (Set.range (monskyVertices T htriangle t)) :=
  Classical.choose_spec (monsky_exists_vertices T htriangle t)

private lemma monsky_vertices_independent
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineIndependent ℝ (monskyVertices T htriangle t) := by
  let p := monskyVertices T htriangle t
  have hp : t.1 = convexHull ℝ (Set.range p) := monsky_vertices_spec T htriangle t
  have hrange : Set.range p = {p 0, p 1, p 2} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hv := hvolume t.1 t.2
  rw [hp, hrange, MeasureTheory.toReal_volume_convexHull_triangle] at hv
  have hcyclic :
      (p 1 - p 0).ofLp 0 * (p 2 - p 0).ofLp 1 -
          (p 1 - p 0).ofLp 1 * (p 2 - p 0).ofLp 0 =
        (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
          (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 := by
    simp only [PiLp.sub_apply]
    ring
  have hdet : (p 0 - p 2).ofLp 0 * (p 1 - p 2).ofLp 1 -
      (p 0 - p 2).ofLp 1 * (p 1 - p 2).ofLp 0 ≠ 0 := by
    intro hzero
    rw [hcyclic, hzero, abs_zero, zero_div] at hv
    have hpos : (0 : ℝ) < 1 / (T.card : ℝ) := by
      positivity
    linarith
  have hi := monsky_affineIndependent_of_det_ne_zero (p 0) (p 1) (p 2) hdet
  have hpvec : ![p 0, p 1, p 2] = p := by
    funext i
    fin_cases i <;> rfl
  rw [hpvec] at hi
  exact hi

private noncomputable def monskyTriangleBasis
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
    ⟨monskyVertices T htriangle t, monsky_vertices_independent T htriangle hcard hvolume t⟩
  exact ⟨s.points, s.independent, s.affineSpan_eq_top (by simp)⟩

private lemma monsky_triangleBasis_apply
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (i : Fin 3) :
    monskyTriangleBasis T htriangle hcard hvolume t i = monskyVertices T htriangle t i := by
  rfl

private noncomputable def monskySquareCorner (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) :=
  ![0, euclideanPlaneBasis 0, euclideanPlaneBasis 0 + euclideanPlaneBasis 1,
    euclideanPlaneBasis 1] i

private abbrev MonskyFace
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))) := (↑T × Fin 3) ⊕ Fin 4

private noncomputable def monskyFaceLeft
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 1)
  | .inr i => monskySquareCorner i

private noncomputable def monskyFaceRight
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t (i + 2)
  | .inr i => monskySquareCorner (i + 1)

private noncomputable def monskyCoordinate (i : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  (EuclideanSpace.projₗ i).toAffineMap

private noncomputable def monskySquareSideForm (i : Fin 4) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  ![monskyCoordinate 1,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 0,
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 1 - monskyCoordinate 1,
    monskyCoordinate 0] i

private noncomputable def monskyFaceForm
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    MonskyFace T → EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ
  | .inl (t, i) => (monskyTriangleBasis T htriangle hcard hvolume t).coord i
  | .inr i => monskySquareSideForm i

private lemma monsky_face_endpoints_ne
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : monskyFaceLeft T htriangle f ≠ monskyFaceRight T htriangle f := by
  rcases f with ⟨t, i⟩ | i
  · apply (monsky_vertices_independent T htriangle hcard hvolume t).injective.ne
    fin_omega
  · fin_cases i
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 0) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this
    · intro h
      have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x.ofLp 1) h
      norm_num [monskyFaceLeft, monskyFaceRight, monskySquareCorner] at this

private lemma monsky_faceForm_left_right
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    monskyFaceForm T htriangle hcard hvolume f (monskyFaceLeft T htriangle f) = 0 ∧
      monskyFaceForm T htriangle hcard hvolume f (monskyFaceRight T htriangle f) = 0 := by
  rcases f with ⟨t, i⟩ | i
  · constructor <;> simp only [monskyFaceForm, monskyFaceLeft, monskyFaceRight]
    · rw [← monsky_triangleBasis_apply T htriangle hcard hvolume,
        (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne]
      fin_omega
    · rw [← monsky_triangleBasis_apply T htriangle hcard hvolume,
        (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne]
      fin_omega
  · fin_cases i <;> simp [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
      monskySquareSideForm, monskySquareCorner, monskyCoordinate]

private lemma monsky_mem_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ t.1 ↔ ∀ i : Fin 3, 0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.convexHull_eq_nonneg_coord]
  rfl

private lemma monsky_mem_interior_tile_iff_faceForms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (t : ↑T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ interior t.1 ↔
      ∀ i : Fin 3, 0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x := by
  let b := monskyTriangleBasis T htriangle hcard hvolume t
  have hrange : Set.range (monskyVertices T htriangle t) = Set.range b := by
    ext y
    simp only [Set.mem_range]
    constructor <;> rintro ⟨i, rfl⟩
    · exact ⟨i, (monsky_triangleBasis_apply T htriangle hcard hvolume t i).symm⟩
    · exact ⟨i, monsky_triangleBasis_apply T htriangle hcard hvolume t i⟩
  rw [monsky_vertices_spec T htriangle t, hrange, b.interior_convexHull]
  rfl

private lemma monsky_mem_unitSquare_iff_faceForms
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ {y | ∀ i, 0 ≤ y.ofLp i ∧ y.ofLp i ≤ 1} ↔
      ∀ i : Fin 4, 0 ≤ monskySquareSideForm i x := by
  constructor
  · intro hx i
    fin_cases i <;> simp [monskySquareSideForm, monskyCoordinate] <;>
      have := hx 0 <;> have := hx 1 <;> linarith
  · intro h i
    fin_cases i
    · have hleft := h 3
      have hright := h 1
      simp [monskySquareSideForm, monskyCoordinate] at hleft hright
      simpa using And.intro hleft hright
    · have hbottom := h 0
      have htop := h 2
      simp [monskySquareSideForm, monskyCoordinate] at hbottom htop
      simpa using And.intro hbottom htop

private lemma monsky_faceForm_eq_zero_of_mem_line
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ affineSpan ℝ
      ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
        Set (EuclideanSpace ℝ (Fin 2)))) :
    monskyFaceForm T htriangle hcard hvolume f x = 0 := by
  let g := monskyFaceForm T htriangle hcard hvolume f
  let z : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 2)) 0
  have heq :
      ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
        Set (EuclideanSpace ℝ (Fin 2))).EqOn g z := by
    intro y hy
    rcases hy with rfl | hy
    · exact (monsky_faceForm_left_right T htriangle hcard hvolume f).1
    · rw [Set.mem_singleton_iff] at hy
      subst y
      exact (monsky_faceForm_left_right T htriangle hcard hvolume f).2
  exact AffineMap.eqOn_affineSpan heq hx

private noncomputable def monskyFaceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ
    ({monskyFaceLeft T htriangle f, monskyFaceRight T htriangle f} :
      Set (EuclideanSpace ℝ (Fin 2)))

private lemma monsky_range_faceOpposite
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3) :
    Set.range ((⟨b, b.ind⟩ : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2).faceOpposite i).points =
      {b (i + 1), b (i + 2)} := by
  rw [Affine.Simplex.range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨i + 1, by fin_cases i <;> decide, rfl⟩
    · exact ⟨i + 2, by fin_cases i <;> decide, rfl⟩

private lemma monsky_mem_affineSpan_face_iff_coord_zero
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ affineSpan ℝ ({b (i + 1), b (i + 2)} : Set (EuclideanSpace ℝ (Fin 2))) ↔
      b.coord i x = 0 := by
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨b, b.ind⟩
  rw [← monsky_range_faceOpposite b i]
  have h := Affine.Simplex.affineCombination_mem_affineSpan_faceOpposite_iff
    (s := s) (i := i) (w := fun j ↦ b.coord j x) (b.sum_coord_apply_eq_one x)
  rw [b.affineCombination_coord_eq_self] at h
  exact h

private lemma monsky_mem_faceLine_iff_faceForm_eq_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ monskyFaceLine T htriangle f ↔
      monskyFaceForm T htriangle hcard hvolume f x = 0 := by
  constructor
  · exact monsky_faceForm_eq_zero_of_mem_line T htriangle hcard hvolume f
  · intro hx
    rcases f with ⟨t, i⟩ | i
    · simpa only [monskyFaceLine, monskyFaceLeft, monskyFaceRight, monskyFaceForm,
        monsky_triangleBasis_apply] using
        ((monsky_mem_affineSpan_face_iff_coord_zero
          (monskyTriangleBasis T htriangle hcard hvolume t) i x).2 hx :
            x ∈ affineSpan ℝ
              ({monskyTriangleBasis T htriangle hcard hvolume t (i + 1),
                monskyTriangleBasis T htriangle hcard hvolume t (i + 2)} :
                  Set (EuclideanSpace ℝ (Fin 2))))
    · rw [monskyFaceLine, mem_affineSpan_pair_iff_exists_lineMap_eq]
      fin_cases i
      · refine ⟨x.ofLp 0, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨x.ofLp 1, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨1 - x.ofLp 0, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          PiLp.smul_apply, smul_eq_mul] at hx ⊢
        all_goals linarith
      · refine ⟨1 - x.ofLp 1, ?_⟩
        ext j
        fin_cases j <;> norm_num [monskyFaceForm, monskyFaceLeft, monskyFaceRight,
          monskySquareSideForm, monskySquareCorner, monskyCoordinate,
          AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
          smul_eq_mul] at hx ⊢
        all_goals linarith

private noncomputable def monskyIntersectionPoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T) :
    EuclideanSpace ℝ (Fin 2) := by
  classical
  exact if h : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
      monskyFaceLine T htriangle g).Nonempty then Classical.choose h
    else monskyFaceLeft T htriangle f

private lemma monsky_intersectionPoint_mem
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T)
    (h : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
      monskyFaceLine T htriangle g).Nonempty) :
    monskyIntersectionPoint T htriangle f g ∈ monskyFaceLine T htriangle f ∧
      monskyIntersectionPoint T htriangle f g ∈ monskyFaceLine T htriangle g := by
  rw [monskyIntersectionPoint, dite_eq_left h]
  exact Classical.choose_spec h

private lemma monsky_intersectionPoint_eq_of_mem
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T)
    (hfg : monskyFaceLine T htriangle f ≠ monskyFaceLine T htriangle g)
    {x : EuclideanSpace ℝ (Fin 2)} (hxf : x ∈ monskyFaceLine T htriangle f)
    (hxg : x ∈ monskyFaceLine T htriangle g) :
    monskyIntersectionPoint T htriangle f g = x := by
  have hne : ((monskyFaceLine T htriangle f : Set (EuclideanSpace ℝ (Fin 2))) ∩
      monskyFaceLine T htriangle g).Nonempty := ⟨x, hxf, hxg⟩
  have hy := monsky_intersectionPoint_mem T htriangle f g hne
  by_contra hyx
  have hlinef : affineSpan ℝ
      ({monskyIntersectionPoint T htriangle f g, x} : Set (EuclideanSpace ℝ (Fin 2))) =
      monskyFaceLine T htriangle f :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hy.1 hxf hyx
  have hlineg : affineSpan ℝ
      ({monskyIntersectionPoint T htriangle f g, x} : Set (EuclideanSpace ℝ (Fin 2))) =
      monskyFaceLine T htriangle g :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hy.2 hxg hyx
  exact hfg (hlinef.symm.trans hlineg)

private noncomputable def monskyNodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (EuclideanSpace ℝ (Fin 2)) := by
  classical
  exact
    (Finset.univ.image (monskyFaceLeft T htriangle) ∪
      Finset.univ.image (monskyFaceRight T htriangle)) ∪
      Finset.univ.biUnion fun f : MonskyFace T ↦
        Finset.univ.image fun g : MonskyFace T ↦ monskyIntersectionPoint T htriangle f g

private lemma monsky_faceLeft_mem_nodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    monskyFaceLeft T htriangle f ∈ monskyNodes T htriangle := by
  classical
  simp [monskyNodes]

private lemma monsky_faceRight_mem_nodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    monskyFaceRight T htriangle f ∈ monskyNodes T htriangle := by
  classical
  simp [monskyNodes]

private lemma monsky_intersectionPoint_mem_nodes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f g : MonskyFace T) :
    monskyIntersectionPoint T htriangle f g ∈ monskyNodes T htriangle := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩

private noncomputable def monskyFaceInteriorParams
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) : Finset ℝ := by
  classical
  exact ((monskyNodes T htriangle).filter fun x ↦
      x ∈ openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)).image
    (Function.invFun (AffineMap.lineMap
      (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)))

private lemma monsky_faceInteriorParam_spec
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceInteriorParams T htriangle f) :
    r ∈ Set.Ioo (0 : ℝ) 1 ∧
      AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f) r ∈
        monskyNodes T htriangle := by
  classical
  rw [monskyFaceInteriorParams, Finset.mem_image] at hr
  obtain ⟨x, hx, hr⟩ := hr
  obtain ⟨hxnode, hxopen⟩ := Finset.mem_filter.mp hx
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨s, hs, hsx⟩ := hxopen
  have hinj := AffineMap.lineMap_injective ℝ
    (monsky_face_endpoints_ne T htriangle hcard hvolume f)
  have hinv : Function.invFun
      (AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)) x = s := by
    rw [← hsx]
    exact Function.leftInverse_invFun hinj s
  have hrs : r = s := hr.symm.trans hinv
  constructor
  · rwa [hrs]
  · rw [hrs, hsx]
    exact hxnode

private noncomputable def monskyFaceParamList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) : List ℝ :=
  0 :: (monskyFaceInteriorParams T htriangle f).sort (fun a b ↦ a ≤ b) ++ [1]

private lemma monsky_faceParamList_sorted
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceParamList T htriangle f).SortedLT := by
  let l := (monskyFaceInteriorParams T htriangle f).sort (fun a b ↦ a ≤ b)
  have hl : l.SortedLT := Finset.sortedLT_sort _
  have hmem : ∀ r ∈ l, r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
      ((Finset.mem_sort _).1 hr)).1
  change ((0 :: l) ++ [1]).SortedLT
  rw [List.sortedLT_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.sortedLT_cons]
    exact ⟨fun r hr ↦ (hmem r hr).1, hl⟩
  · rw [List.sortedLT_iff_pairwise]
    exact List.pairwise_singleton (· < ·) 1
  · intro r hr q hq
    have hq1 : q = 1 := List.mem_singleton.mp hq
    subst q
    rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · exact (hmem r hr).2

private noncomputable def monskyFacePointList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (EuclideanSpace ℝ (Fin 2)) :=
  (monskyFaceParamList T htriangle f).map
    (AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f))

private noncomputable def monskyFaceAtomList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    List (Sym2 (EuclideanSpace ℝ (Fin 2))) :=
  (monskyFacePointList T htriangle f).consecutivePairs.map fun e ↦ s(e.1, e.2)

private noncomputable def monskyAtoms
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : Finset (Sym2 (EuclideanSpace ℝ (Fin 2))) := by
  classical
  exact Finset.univ.biUnion fun f : MonskyFace T ↦
    (monskyFaceAtomList T htriangle f).toFinset

private lemma monsky_consecutivePairs_map {α β : Type*} (f : α → β) : ∀ l : List α,
    (l.map f).consecutivePairs = l.consecutivePairs.map (fun e ↦ (f e.1, f e.2)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil =>
          rw [show [a].consecutivePairs = [] from rfl]
          rfl
      | cons b l =>
          simp only [List.map_cons]
          rw [show (f a :: f b :: l.map f).consecutivePairs =
            (f a, f b) :: (f b :: l.map f).consecutivePairs from rfl,
            show (a :: b :: l).consecutivePairs =
              (a, b) :: (b :: l).consecutivePairs from rfl]
          simp only [List.map_cons]
          congr

private lemma monsky_mem_faceAtomList_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
    (e : Sym2 (EuclideanSpace ℝ (Fin 2))) :
    e ∈ monskyFaceAtomList T htriangle f ↔
      ∃ r q : ℝ, (r, q) ∈ (monskyFaceParamList T htriangle f).consecutivePairs ∧
        e = s(AffineMap.lineMap (monskyFaceLeft T htriangle f)
            (monskyFaceRight T htriangle f) r,
          AffineMap.lineMap (monskyFaceLeft T htriangle f)
            (monskyFaceRight T htriangle f) q) := by
  rw [monskyFaceAtomList, monskyFacePointList, monsky_consecutivePairs_map]
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.1, q.2, hq, rfl⟩
  · rintro ⟨r, q, hrq, rfl⟩
    exact ⟨_, ⟨(r, q), hrq, rfl⟩, rfl⟩

private noncomputable def monskyAtomMidpoint :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) :=
  Sym2.lift ⟨fun a b ↦ midpoint ℝ a b, fun a b ↦ midpoint_comm a b⟩

@[simp] private lemma monsky_atomMidpoint_mk
    (a b : EuclideanSpace ℝ (Fin 2)) :
    monskyAtomMidpoint s(a, b) = midpoint ℝ a b := by
  rfl

private theorem monsky_exists_valuation_int_le_one_two_lt_one :
    ∃ V : ValuationSubring ℝ,
      (∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) ∧ V.valuation 2 < 1 := by
  let A : Subring ℝ := (Int.castRingHom ℝ).range
  let e : ℤ ≃+* A := RingEquiv.ofBijective (Int.castRingHom ℝ).rangeRestrict
    ⟨fun x y h ↦ Int.cast_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  let J : Ideal ℤ := Ideal.span {2}
  let I : Ideal A := J.comap e.symm
  have hJ : J ≠ ⊤ := by
    dsimp only [J]
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  have hI : I ≠ ⊤ := Ideal.comap_ne_top e.symm hJ
  obtain ⟨V, hAV, hnonunits⟩ :=
    Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨V, ?_, ?_⟩
  · intro z
    rw [V.valuation_le_one_iff]
    apply hAV
    exact ⟨z, rfl⟩
  · rw [← V.mem_nonunits_iff]
    let a2 : A := e 2
    have ha2 : a2 ∈ I := by
      change e.symm (e 2) ∈ J
      rw [e.symm_apply_apply]
      exact Ideal.subset_span (by simp)
    have hcoe : A.subtype a2 = (2 : ℝ) := by
      change ((2 : ℤ) : ℝ) = (2 : ℝ)
      norm_num
    exact hnonunits ⟨a2, ha2, hcoe⟩

private theorem monsky_valuation_odd_eq_one (V : ValuationSubring ℝ)
    (hint : ∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) (htwo : V.valuation 2 < 1)
    {n : ℤ} (hn : Odd n) : V.valuation (n : ℝ) = 1 := by
  apply le_antisymm (hint n)
  by_contra hnot
  have hnlt : V.valuation (n : ℝ) < 1 := lt_of_not_ge hnot
  obtain ⟨m, hm⟩ := hn
  have hmle : V.valuation (m : ℝ) ≤ 1 := hint m
  have htwom : V.valuation ((2 : ℝ) * (m : ℝ)) < 1 := by
    rw [V.valuation.map_mul]
    calc
      V.valuation 2 * V.valuation (m : ℝ) ≤ V.valuation 2 * 1 := by
        simpa [mul_comm] using mul_le_mul_left hmle (V.valuation 2)
      _ = V.valuation 2 := mul_one _
      _ < 1 := htwo
  have hone : V.valuation (1 : ℝ) ≤
      max (V.valuation (n : ℝ)) (V.valuation (-((2 : ℝ) * (m : ℝ)))) := by
    have hadd := ValuationClass.map_add_le_max V.valuation
      (n : ℝ) (-((2 : ℝ) * (m : ℝ)))
    have hmR : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
    have honeq : (n : ℝ) + -((2 : ℝ) * (m : ℝ)) = 1 := by
      rw [hmR]
      ring
    simpa only [honeq] using hadd
  rw [V.valuation.map_neg] at hone
  have hmax : max (V.valuation (n : ℝ))
      (V.valuation ((2 : ℝ) * (m : ℝ))) < 1 := max_lt hnlt htwom
  rw [V.valuation.map_one] at hone
  exact (not_lt_of_ge hone) hmax

/-- The mod-two edge weight used in the Sperner count.  It detects an edge whose endpoint
colours are `0` and `2`. -/
private def monskyEdgeWeight (i j : Fin 3) : ZMod 2 :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0

/-- Subdividing an edge does not change its Monsky edge weight when its three points use at
most two colours. -/
private theorem monskyEdgeWeight_add (i j k : Fin 3) (h : i = j ∨ j = k ∨ i = k) :
    monskyEdgeWeight i k = monskyEdgeWeight i j + monskyEdgeWeight j k := by
  revert i j k
  decide

/-- A three-cycle has nonzero Monsky edge weight exactly when its vertices have three distinct
colours. -/
private theorem monskyEdgeWeight_triangle (i j k : Fin 3) :
    monskyEdgeWeight i j + monskyEdgeWeight j k + monskyEdgeWeight k i = 1 ↔
      i ≠ j ∧ j ≠ k ∧ k ≠ i := by
  revert i j k
  decide

private def monskyPathWeight : List (Fin 3) → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => monskyEdgeWeight a b + monskyPathWeight (b :: l)

private lemma monsky_pathWeight_eq_edgeWeight (i j : Fin 3) : ∀ (l : List (Fin 3)),
    (∀ x ∈ l, x = i ∨ x = j) → (h : l ≠ []) →
      monskyPathWeight l = monskyEdgeWeight (l.head h) (l.getLast h) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro hall hne
      cases l with
      | nil =>
          simp only [monskyPathWeight, List.head_cons, List.getLast_singleton]
          simp [monskyEdgeWeight]
          omega
      | cons b l =>
          have htail : ∀ x ∈ b :: l, x = i ∨ x = j := by
            intro x hx
            exact hall x (by simp [hx])
          have htailne : b :: l ≠ [] := by simp
          have hih := ih htail htailne
          have ha := hall a (by simp)
          have hb := hall b (by simp)
          have hc := hall ((b :: l).getLast htailne)
            (List.mem_cons_of_mem a (List.getLast_mem htailne))
          have hdup : a = b ∨ b = (b :: l).getLast htailne ∨
              a = (b :: l).getLast htailne := by
            aesop
          rw [monskyPathWeight, hih]
          exact (monskyEdgeWeight_add a b ((b :: l).getLast htailne) hdup).symm

private lemma monsky_mem_consecutivePairs_iff {α : Type*} {a b : α} : ∀ l : List α,
    (a, b) ∈ l.consecutivePairs ↔ ∃ pre post, l = pre ++ a :: b :: post := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
      cases l with
      | nil =>
          rw [show [x].consecutivePairs = [] from rfl]
          simp only [List.not_mem_nil, false_iff, not_exists]
          intro pre post h
          have hlen := congrArg List.length h
          simp at hlen
          omega
      | cons y l =>
          rw [show (x :: y :: l).consecutivePairs =
            (x, y) :: (y :: l).consecutivePairs from rfl]
          simp only [List.mem_cons, Prod.mk.injEq, ih]
          constructor
          · rintro (⟨rfl, rfl⟩ | ⟨pre, post, h⟩)
            · exact ⟨[], l, rfl⟩
            · exact ⟨x :: pre, post, by simp [h]⟩
          · rintro ⟨pre, post, h⟩
            cases pre with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at h
                exact Or.inl ⟨h.1.symm, h.2.1.symm⟩
            | cons z pre =>
                simp only [List.cons_append, List.cons.injEq] at h
                obtain ⟨rfl, h⟩ := h
                exact Or.inr ⟨pre, post, h⟩

private lemma monsky_not_between_of_mem_consecutivePairs {α : Type*} [LinearOrder α]
    {l : List α} (hs : l.SortedLT) {a b t : α}
    (hab : (a, b) ∈ l.consecutivePairs) (ht : t ∈ l) : ¬(a < t ∧ t < b) := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  have hsappend := List.sortedLT_append.mp hs
  have htail : (a :: b :: post).SortedLT := hsappend.2.1
  have hpre : ∀ x ∈ pre, x < a := by
    intro x hx
    exact hsappend.2.2 x hx a (by simp)
  have hpost : ∀ x ∈ post, b < x := by
    intro x hx
    exact (List.sortedLT_cons.mp (List.sortedLT_cons.mp htail).2).1 x hx
  rintro ⟨hat, htb⟩
  rcases List.mem_append.mp ht with ht | ht
  · exact (not_lt_of_ge (hpre t ht).le) hat
  · rcases List.mem_cons.mp ht with rfl | ht
    · exact lt_irrefl _ hat
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact lt_irrefl _ htb
      · exact (not_lt_of_ge (hpost t ht).le) htb

private lemma monsky_lt_of_mem_consecutivePairs {α : Type*} [LinearOrder α]
    {l : List α} (hs : l.SortedLT) {a b : α}
    (hab : (a, b) ∈ l.consecutivePairs) : a < b := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  have htail : (a :: b :: post).SortedLT := (List.sortedLT_append.mp hs).2.1
  exact (List.sortedLT_cons.mp htail).1 b (by simp)

private lemma monsky_fst_mem_of_mem_consecutivePairs {α : Type*} {l : List α} {a b : α}
    (hab : (a, b) ∈ l.consecutivePairs) : a ∈ l := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  simp

private lemma monsky_snd_mem_of_mem_consecutivePairs {α : Type*} {l : List α} {a b : α}
    (hab : (a, b) ∈ l.consecutivePairs) : b ∈ l := by
  obtain ⟨pre, post, rfl⟩ := (monsky_mem_consecutivePairs_iff _).1 hab
  simp

private lemma monsky_mem_faceParamList_bounds
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    0 ≤ r ∧ r ≤ 1 := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · have hir := (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).1
      exact ⟨hir.1.le, hir.2.le⟩
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    norm_num

private lemma monsky_atomMidpoint_eq_lineMap_midpoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
    (e : Sym2 (EuclideanSpace ℝ (Fin 2))) {r q : ℝ}
    (he : e = s(AffineMap.lineMap (monskyFaceLeft T htriangle f)
          (monskyFaceRight T htriangle f) r,
        AffineMap.lineMap (monskyFaceLeft T htriangle f)
          (monskyFaceRight T htriangle f) q)) :
    monskyAtomMidpoint e =
      AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) (midpoint ℝ r q) := by
  rw [he, monsky_atomMidpoint_mk]
  exact (AffineMap.lineMap _ _).map_midpoint r q |>.symm

private lemma monsky_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f) :
    monskyAtomMidpoint e ∈
      openSegment ℝ (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f) := by
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hr := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hq := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  rw [openSegment_eq_image_lineMap]
  refine ⟨midpoint ℝ r q, ?_, ?_⟩
  · simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  · exact (monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq).symm

private lemma monsky_invFun_mem_faceInteriorParams
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
    {x : EuclideanSpace ℝ (Fin 2)} (hnode : x ∈ monskyNodes T htriangle)
    (hopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f)) :
    Function.invFun (AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f)) x ∈ monskyFaceInteriorParams T htriangle f := by
  classical
  rw [monskyFaceInteriorParams, Finset.mem_image]
  exact ⟨x, Finset.mem_filter.mpr ⟨hnode, hopen⟩, rfl⟩

private lemma monsky_atomMidpoint_not_mem_distinct_faceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f g : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ monskyFaceAtomList T htriangle f)
    (hfg : monskyFaceLine T htriangle f ≠ monskyFaceLine T htriangle g) :
    monskyAtomMidpoint e ∉ monskyFaceLine T htriangle g := by
  intro hmg
  obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 he
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  let u := midpoint ℝ r q
  have hm : monskyAtomMidpoint e = L u :=
    monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
  have hmf : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle f := by
    rw [hm, monskyFaceLine]
    exact AffineMap.lineMap_mem_affineSpan_pair u _ _
  have hinter : monskyIntersectionPoint T htriangle f g = monskyAtomMidpoint e :=
    monsky_intersectionPoint_eq_of_mem T htriangle f g hfg hmf hmg
  have hmnode : monskyAtomMidpoint e ∈ monskyNodes T htriangle := by
    rw [← hinter]
    exact monsky_intersectionPoint_mem_nodes T htriangle f g
  have hmopen := monsky_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e he
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hmnode hmopen
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L (monskyAtomMidpoint e) = u := by
      rw [hm]
      exact Function.leftInverse_invFun hLinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    left
    exact List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam)
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    constructor <;> norm_num <;> linarith
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

private lemma monsky_mem_consecutivePairs_of_sortedLT {α : Type*} [LinearOrder α]
    {l : List α} (hs : l.SortedLT) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a < b) (hno : ∀ t ∈ l, ¬(a < t ∧ t < b)) :
    (a, b) ∈ l.consecutivePairs := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [List.mem_singleton] at ha hb
          subst x
          subst b
          exact (lt_irrefl _ hab).elim
      | cons y ys =>
          have hsorted := List.sortedLT_cons.mp hs
          have htailSorted : (y :: ys).SortedLT := hsorted.2
          rw [show (x :: y :: ys).consecutivePairs =
            (x, y) :: (y :: ys).consecutivePairs from rfl]
          by_cases hxa : x = a
          · subst x
            have hbTail : b ∈ y :: ys := by
              rcases List.mem_cons.mp hb with hba | hbTail
              · exact (hab.ne hba.symm).elim
              · exact hbTail
            rcases List.mem_cons.mp hbTail with hby | hbys
            · exact List.mem_cons.mpr (Or.inl (Prod.ext rfl hby))
            · have hay : a < y := hsorted.1 y (by simp)
              have hyb : y < b := (List.sortedLT_cons.mp htailSorted).1 b hbys
              exact (hno y (by simp) ⟨hay, hyb⟩).elim
          · apply List.mem_cons.mpr
            right
            have haTail : a ∈ y :: ys :=
              (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
            have hbTail : b ∈ y :: ys := by
              rcases List.mem_cons.mp hb with hbx | hbTail
              · subst x
                have hba : b < a := hsorted.1 a haTail
                exact (asymm hab hba).elim
              · exact hbTail
            exact ih htailSorted haTail hbTail
              (fun t ht ↦ hno t (List.mem_cons_of_mem x ht))

private lemma monsky_lineMap_mem_nodes_of_mem_paramList
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r : ℝ} (hr : r ∈ monskyFaceParamList T htriangle f) :
    AffineMap.lineMap (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) r ∈ monskyNodes T htriangle := by
  rw [monskyFaceParamList, List.mem_append] at hr
  rcases hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · simpa using monsky_faceLeft_mem_nodes T htriangle f
    · exact (monsky_faceInteriorParam_spec T htriangle hcard hvolume f
        ((Finset.mem_sort _).1 hr)).2
  · have hr1 : r = 1 := List.mem_singleton.mp hr
    subst r
    simpa using monsky_faceRight_mem_nodes T htriangle f

private lemma monsky_mem_pointList_of_mem_nodes_of_mem_segment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {x : EuclideanSpace ℝ (Fin 2)}
    (hnode : x ∈ monskyNodes T htriangle)
    (hsegment : x ∈ segment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f)) :
    x ∈ monskyFacePointList T htriangle f := by
  rw [segment_eq_image_lineMap] at hsegment
  obtain ⟨r, hr, hrx⟩ := hsegment
  have hparam : r ∈ monskyFaceParamList T htriangle f := by
    rcases eq_or_lt_of_le hr.1 with rfl | hr0
    · rw [monskyFaceParamList, List.mem_append]
      exact Or.inl (by simp)
    · rcases eq_or_lt_of_le hr.2 with rfl | hr1
      · rw [monskyFaceParamList, List.mem_append]
        exact Or.inr (by simp)
      · have hopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
            (monskyFaceRight T htriangle f) := by
          rw [openSegment_eq_image_lineMap]
          exact ⟨r, ⟨hr0, hr1⟩, hrx⟩
        have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode hopen
        have hinj := AffineMap.lineMap_injective ℝ
          (monsky_face_endpoints_ne T htriangle hcard hvolume f)
        have hinvr : Function.invFun (AffineMap.lineMap
            (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)) x = r := by
          rw [← hrx]
          exact Function.leftInverse_invFun hinj r
        rw [hinvr] at hinv
        rw [monskyFaceParamList, List.mem_append]
        exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 hinv))
  rw [monskyFacePointList, List.mem_map]
  exact ⟨r, hparam, hrx⟩

private lemma monsky_no_node_mem_openSegment_of_consecutive
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) {r q : ℝ}
    (hrq : (r, q) ∈ (monskyFaceParamList T htriangle f).consecutivePairs)
    {x : EuclideanSpace ℝ (Fin 2)} (hnode : x ∈ monskyNodes T htriangle) :
    x ∉ openSegment ℝ
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) r)
      (AffineMap.lineMap (monskyFaceLeft T htriangle f)
        (monskyFaceRight T htriangle f) q) := by
  intro hxopen
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
  rw [openSegment_eq_image_lineMap] at hxopen
  obtain ⟨t, ht, htx⟩ := hxopen
  let u := AffineMap.lineMap r q t
  have hLux : L u = x := by
    change L (AffineMap.lineMap r q t) = x
    rw [L.apply_lineMap, htx]
  have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
  have hubetween : r < u ∧ u < q := by
    simp only [u, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    constructor <;> nlinarith [ht.1, ht.2]
  have hrbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_fst_mem_of_mem_consecutivePairs hrq)
  have hqbounds := monsky_mem_faceParamList_bounds T htriangle hcard hvolume f
    (monsky_snd_mem_of_mem_consecutivePairs hrq)
  have huopen : x ∈ openSegment ℝ (monskyFaceLeft T htriangle f)
      (monskyFaceRight T htriangle f) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨u, ⟨hrbounds.1.trans_lt hubetween.1,
      hubetween.2.trans_le hqbounds.2⟩, hLux⟩
  have huparam : u ∈ monskyFaceInteriorParams T htriangle f := by
    have hinv := monsky_invFun_mem_faceInteriorParams T htriangle f hnode huopen
    have hinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hinvu : Function.invFun L x = u := by
      rw [← hLux]
      exact Function.leftInverse_invFun hinj u
    rwa [hinvu] at hinv
  have hulist : u ∈ monskyFaceParamList T htriangle f := by
    rw [monskyFaceParamList, List.mem_append]
    exact Or.inl (List.mem_cons_of_mem 0 ((Finset.mem_sort _).2 huparam))
  exact monsky_not_between_of_mem_consecutivePairs
    (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq hulist hubetween

private lemma monsky_scalar_segment_enclosure {r q a b t : ℝ} (hrq : r < q)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hmid : midpoint ℝ r q = AffineMap.lineMap a b t)
    (ha : a ∉ Set.Ioo r q) (hb : b ∉ Set.Ioo r q) :
    (a ≤ r ∧ q ≤ b) ∨ (b ≤ r ∧ q ≤ a) := by
  have hru : r < midpoint ℝ r q := by
    simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    norm_num
    linarith
  have huq : midpoint ℝ r q < q := by
    simp only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      smul_eq_mul, invOf_eq_inv]
    norm_num
    linarith
  rcases lt_trichotomy a b with hab | hab | hab
  · left
    have hau : a < midpoint ℝ r q := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    have hub : midpoint ℝ r q < b := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    constructor
    · by_contra h
      exact ha ⟨lt_of_not_ge h, hau.trans huq⟩
    · by_contra h
      exact hb ⟨hru.trans hub, lt_of_not_ge h⟩
  · subst b
    have hma : midpoint ℝ r q = a := by
      simpa [AffineMap.lineMap_apply] using hmid
    exact (ha ⟨hma ▸ hru, hma ▸ huq⟩).elim
  · right
    have hbu : b < midpoint ℝ r q := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    have hua : midpoint ℝ r q < a := by
      rw [hmid]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      nlinarith [ht.1, ht.2]
    constructor
    · by_contra h
      exact hb ⟨lt_of_not_ge h, hbu.trans huq⟩
    · by_contra h
      exact ha ⟨hru.trans hua, lt_of_not_ge h⟩

private lemma monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T) :
    e ∈ monskyFaceAtomList T htriangle g ↔
      monskyAtomMidpoint e ∈
        openSegment ℝ (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g) := by
  constructor
  · exact monsky_atomMidpoint_mem_openSegment T htriangle hcard hvolume g e
  · intro hmopen
    obtain ⟨r, q, hrq, heq⟩ := (monsky_mem_faceAtomList_iff T htriangle f e).1 hef
    let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle f) (monskyFaceRight T htriangle f)
    let G : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap (monskyFaceLeft T htriangle g) (monskyFaceRight T htriangle g)
    have hrqlt : r < q := monsky_lt_of_mem_consecutivePairs
      (monsky_faceParamList_sorted T htriangle hcard hvolume f) hrq
    have hm : monskyAtomMidpoint e = L (midpoint ℝ r q) :=
      monsky_atomMidpoint_eq_lineMap_midpoint T htriangle f e heq
    rw [openSegment_eq_image_lineMap] at hmopen
    obtain ⟨t, ht, htm⟩ := hmopen
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g := by
      rw [← htm, monskyFaceLine]
      exact AffineMap.lineMap_mem_affineSpan_pair t _ _
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hgleft : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact left_mem_affineSpan_pair ℝ _ _
    have hgright : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle g := by
      rw [monskyFaceLine]
      exact right_mem_affineSpan_pair ℝ _ _
    have hgleft' : monskyFaceLeft T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    have hgright' : monskyFaceRight T htriangle g ∈ monskyFaceLine T htriangle f := by
      rwa [hline]
    rw [monskyFaceLine, mem_affineSpan_pair_iff_exists_lineMap_eq] at hgleft' hgright'
    obtain ⟨a, ha⟩ := hgleft'
    obtain ⟨b, hb⟩ := hgright'
    have hLinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f)
    have hscalar : midpoint ℝ r q = AffineMap.lineMap a b t := by
      apply hLinj
      calc
        L (midpoint ℝ r q) = monskyAtomMidpoint e := hm.symm
        _ = G t := htm.symm
        _ = AffineMap.lineMap (L a) (L b) t := by rw [ha, hb]
        _ = L (AffineMap.lineMap a b t) := (L.apply_lineMap a b t).symm
    have hleftNode : monskyFaceLeft T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceLeft_mem_nodes T htriangle g
    have hrightNode : monskyFaceRight T htriangle g ∈ monskyNodes T htriangle :=
      monsky_faceRight_mem_nodes T htriangle g
    have haout : a ∉ Set.Ioo r q := by
      intro hain
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hleftNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨a, hain, ha⟩
    have hbout : b ∉ Set.Ioo r q := by
      intro hbin
      apply monsky_no_node_mem_openSegment_of_consecutive
        T htriangle hcard hvolume f hrq hrightNode
      rw [← image_openSegment ℝ L r q, openSegment_eq_Ioo hrqlt]
      exact ⟨b, hbin, hb⟩
    have henclose := monsky_scalar_segment_enclosure hrqlt ht hscalar haout hbout
    have hrseg : r ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1, hrqlt.le.trans henclose.2⟩
    have hqseg : q ∈ segment ℝ a b := by
      rcases henclose with henclose | henclose
      · exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
      · rw [segment_symm]
        exact Icc_subset_segment ⟨henclose.1.trans hrqlt.le, henclose.2⟩
    have hLrseg : L r ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨r, hrseg, rfl⟩
    have hLqseg : L q ∈ segment ℝ (monskyFaceLeft T htriangle g)
        (monskyFaceRight T htriangle g) := by
      rw [← ha, ← hb, ← image_segment ℝ L a b]
      exact ⟨q, hqseg, rfl⟩
    have hrmem := monsky_fst_mem_of_mem_consecutivePairs hrq
    have hqmem := monsky_snd_mem_of_mem_consecutivePairs hrq
    have hLrNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hrmem
    have hLqNode := monsky_lineMap_mem_nodes_of_mem_paramList
      T htriangle hcard hvolume f hqmem
    have hLrPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLrNode hLrseg
    have hLqPoint := monsky_mem_pointList_of_mem_nodes_of_mem_segment
      T htriangle hcard hvolume g hLqNode hLqseg
    rw [monskyFacePointList, List.mem_map] at hLrPoint hLqPoint
    obtain ⟨r', hr'mem, hr'eq⟩ := hLrPoint
    obtain ⟨q', hq'mem, hq'eq⟩ := hLqPoint
    have hGinj := AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume g)
    have hrqne : L r ≠ L q := hLinj.ne hrqlt.ne
    have hr'q'ne : r' ≠ q' := by
      intro h
      apply hrqne
      rw [← hr'eq, ← hq'eq, h]
    rcases lt_or_gt_of_ne hr'q'ne with hr'q' | hq'r'
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(r' < u ∧ u < q') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hr'eq, ← hq'eq, ← image_openSegment ℝ G r' q',
          openSegment_eq_Ioo hr'q']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hr'mem hq'mem hr'q' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨r', q', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq]
    · have hno : ∀ u ∈ monskyFaceParamList T htriangle g,
          ¬(q' < u ∧ u < r') := by
        intro u hu hubetween
        have huNode := monsky_lineMap_mem_nodes_of_mem_paramList
          T htriangle hcard hvolume g hu
        apply monsky_no_node_mem_openSegment_of_consecutive
          T htriangle hcard hvolume f hrq huNode
        rw [← hq'eq, ← hr'eq, openSegment_symm, ← image_openSegment ℝ G q' r',
          openSegment_eq_Ioo hq'r']
        exact ⟨u, hubetween, rfl⟩
      have hadj := monsky_mem_consecutivePairs_of_sortedLT
        (monsky_faceParamList_sorted T htriangle hcard hvolume g)
        hq'mem hr'mem hq'r' hno
      apply (monsky_mem_faceAtomList_iff T htriangle g e).2
      refine ⟨q', r', hadj, ?_⟩
      rw [heq, ← hr'eq, ← hq'eq, Sym2.eq_swap]

private noncomputable def monskyFaceOffPoint
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) : MonskyFace T → EuclideanSpace ℝ (Fin 2)
  | .inl (t, i) => monskyVertices T htriangle t i
  | .inr _ => (2 : ℝ)⁻¹ • (euclideanPlaneBasis 0 + euclideanPlaneBasis 1)

private lemma monsky_faceForm_offPoint_pos
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    0 < monskyFaceForm T htriangle hcard hvolume f
      (monskyFaceOffPoint T htriangle f) := by
  rcases f with ⟨t, i⟩ | i
  · simp only [monskyFaceForm, monskyFaceOffPoint,
      ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    rw [(monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_eq]
    norm_num
  · fin_cases i <;> norm_num [monskyFaceForm, monskyFaceOffPoint,
      monskySquareSideForm, monskyCoordinate]

private lemma monsky_faceForm_continuous
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : Continuous (monskyFaceForm T htriangle hcard hvolume f) := by
  rcases f with ⟨t, i⟩ | i
  · exact continuous_barycentric_coord
      (monskyTriangleBasis T htriangle hcard hvolume t) i
  · fin_cases i
    all_goals norm_num [monskyFaceForm, monskySquareSideForm, monskyCoordinate]
    all_goals fun_prop

private lemma monsky_exists_atom_probes
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∃ p n : EuclideanSpace ℝ (Fin 2),
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g p ∧
            0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
              monskyFaceForm T htriangle hcard hvolume g n) ∧
      (∀ g : MonskyFace T,
        monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
          monskyFaceForm T htriangle hcard hvolume g p *
            monskyFaceForm T htriangle hcard hvolume g n < 0) := by
  let m := monskyAtomMidpoint e
  let z := monskyFaceOffPoint T htriangle f
  let probe : ℝ → EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap m z
  have hevent : ∀ᶠ r in nhds (0 : ℝ), ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g m ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe r) ∧
          0 < monskyFaceForm T htriangle hcard hvolume g m *
            monskyFaceForm T htriangle hcard hvolume g (probe (-r)) := by
    rw [Filter.eventually_all]
    intro g
    by_cases hzero : monskyFaceForm T htriangle hcard hvolume g m = 0
    · exact Filter.Eventually.of_forall fun _ hne ↦ (hne hzero).elim
    · let F := monskyFaceForm T htriangle hcard hvolume g
      have hFcont := monsky_faceForm_continuous T htriangle hcard hvolume g
      have hprobeCont : Continuous probe := AffineMap.lineMap_continuous
      have hnegProbeCont : Continuous (fun r ↦ probe (-r)) :=
        hprobeCont.comp continuous_neg
      have hplusCont : Continuous (fun r ↦ F m * F (probe r)) :=
        continuous_const.mul (hFcont.comp hprobeCont)
      have hminusCont : Continuous (fun r ↦ F m * F (probe (-r))) :=
        continuous_const.mul (hFcont.comp hnegProbeCont)
      have hsquare : 0 < F m * F m := mul_self_pos.mpr hzero
      have hplus0 : 0 < F m * F (probe 0) := by
        simpa [probe] using hsquare
      have hminus0 : 0 < F m * F (probe (-0)) := by
        simpa [probe] using hsquare
      filter_upwards [continuousAt_const.eventually_lt hplusCont.continuousAt hplus0,
        continuousAt_const.eventually_lt hminusCont.continuousAt hminus0] with r hp hn
      exact fun _ ↦ ⟨hp, hn⟩
  obtain ⟨ε, hε, hpreserve⟩ := Metric.eventually_nhds_iff.mp hevent
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδdist : dist δ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    dsimp [δ]
    linarith
  have hpreserveδ := hpreserve hδdist
  refine ⟨probe δ, probe (-δ), ?_, ?_⟩
  · simpa only [m] using hpreserveδ
  · intro g hgm
    have hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g :=
      (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g (monskyAtomMidpoint e)).2 hgm
    have hline : monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
      by_contra hne
      exact monsky_atomMidpoint_not_mem_distinct_faceLine
        T htriangle hcard hvolume f g e hef hne hmg
    have hznotf : z ∉ monskyFaceLine T htriangle f := by
      intro hzf
      have hz0 := (monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume f z).1 hzf
      exact (ne_of_gt (monsky_faceForm_offPoint_pos
        T htriangle hcard hvolume f)) hz0
    have hznotg : z ∉ monskyFaceLine T htriangle g := by
      rwa [← hline]
    have hgz : monskyFaceForm T htriangle hcard hvolume g z ≠ 0 := by
      intro hzero
      exact hznotg ((monsky_mem_faceLine_iff_faceForm_eq_zero
        T htriangle hcard hvolume g z).2 hzero)
    have hplus : monskyFaceForm T htriangle hcard hvolume g (probe δ) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) δ := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z δ
    have hminus : monskyFaceForm T htriangle hcard hvolume g (probe (-δ)) =
        AffineMap.lineMap
          (monskyFaceForm T htriangle hcard hvolume g m)
          (monskyFaceForm T htriangle hcard hvolume g z) (-δ) := by
      exact (monskyFaceForm T htriangle hcard hvolume g).apply_lineMap m z (-δ)
    rw [hplus, hminus]
    have hgm' : monskyFaceForm T htriangle hcard hvolume g m = 0 := by
      simpa only [m] using hgm
    rw [hgm']
    change AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) δ *
      AffineMap.lineMap 0
        (monskyFaceForm T htriangle hcard hvolume g z) (-δ) < 0
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul,
      sub_zero]
    have hprod : δ * monskyFaceForm T htriangle hcard hvolume g z ≠ 0 :=
      mul_ne_zero hδ.ne' hgz
    nlinarith [mul_self_pos.mpr hprod]

private noncomputable def monskyIndicator (P : Prop) : ZMod 2 := by
  classical
  exact if P then 1 else 0

private lemma monsky_form_parity {ι : Type*} [Fintype ι]
    (m p n : ι → ℝ) (occ : ι → Prop)
    (hunique : ∀ i j, m i = 0 → m j = 0 → i = j)
    (hstable : ∀ i, m i ≠ 0 → 0 < m i * p i ∧ 0 < m i * n i)
    (hflip : ∀ i, m i = 0 → p i * n i < 0)
    (hocc : ∀ i, occ i ↔ m i = 0 ∧ ∀ j, j ≠ i → 0 < m j) :
    ∑ i, monskyIndicator (occ i) =
      monskyIndicator (∀ i, 0 ≤ p i) + monskyIndicator (∀ i, 0 ≤ n i) := by
  classical
  by_cases hz : ∃ k, m k = 0
  · obtain ⟨k, hk⟩ := hz
    have hzero : ∀ i, m i = 0 ↔ i = k := by
      intro i
      constructor
      · intro hi
        exact hunique i k hi hk
      · rintro rfl
        exact hk
    by_cases hall : ∀ j, j ≠ k → 0 < m j
    · have hocck : ∀ i, occ i ↔ i = k := by
        intro i
        rw [hocc, hzero]
        constructor
        · exact fun h ↦ h.1
        · rintro rfl
          exact ⟨rfl, hall⟩
      have hpother : ∀ i, i ≠ k → 0 < p i := by
        intro i hik
        have hm := hall i hik
        have hs := (hstable i (ne_of_gt hm)).1
        nlinarith
      have hnother : ∀ i, i ≠ k → 0 < n i := by
        intro i hik
        have hm := hall i hik
        have hs := (hstable i (ne_of_gt hm)).2
        nlinarith
      have hsum : ∑ i, monskyIndicator (occ i) = 1 := by
        simp_rw [hocck]
        simp only [monskyIndicator]
        simpa only [eq_comm] using
          (Fintype.sum_ite_eq k (fun _ ↦ (1 : ZMod 2)))
      rw [hsum]
      rcases (mul_neg_iff.mp (hflip k hk)) with hcase | hcase
      · have hpall : ∀ i, 0 ≤ p i := by
          intro i
          by_cases hik : i = k
          · simpa [hik] using hcase.1.le
          · exact (hpother i hik).le
        have hnnot : ¬∀ i, 0 ≤ n i := by
          intro hn
          exact (not_lt_of_ge (hn k)) hcase.2
        simp [monskyIndicator, hpall, hnnot]
      · have hpnot : ¬∀ i, 0 ≤ p i := by
          intro hp
          exact (not_lt_of_ge (hp k)) hcase.1
        have hnall : ∀ i, 0 ≤ n i := by
          intro i
          by_cases hik : i = k
          · simpa [hik] using hcase.2.le
          · exact (hnother i hik).le
        simp [monskyIndicator, hpnot, hnall]
    · push Not at hall
      obtain ⟨j, hjk, hj⟩ := hall
      have hmj0 : m j ≠ 0 := by
        intro hmj
        exact hjk (hunique j k hmj hk)
      have hmjneg : m j < 0 := lt_of_le_of_ne hj hmj0
      have hpjneg : p j < 0 := by
        have hs := (hstable j hmj0).1
        nlinarith
      have hnjneg : n j < 0 := by
        have hs := (hstable j hmj0).2
        nlinarith
      have hoccfalse : ∀ i, ¬occ i := by
        intro i hi
        obtain ⟨hmi, hiother⟩ := (hocc i).1 hi
        have hik := hunique i k hmi hk
        subst i
        exact (not_lt_of_ge hj) (hiother j hjk)
      have hpnot : ¬∀ i, 0 ≤ p i := by
        intro hp
        exact (not_lt_of_ge (hp j)) hpjneg
      have hnnot : ¬∀ i, 0 ≤ n i := by
        intro hn
        exact (not_lt_of_ge (hn j)) hnjneg
      simp [monskyIndicator, hoccfalse, hpnot, hnnot]
  · push Not at hz
    have hoccfalse : ∀ i, ¬occ i := by
      intro i hi
      exact hz i ((hocc i).1 hi).1
    have hpiff : (∀ i, 0 ≤ p i) ↔ ∀ i, 0 ≤ m i := by
      constructor
      · intro hp i
        by_contra hmi
        have hmneg : m i < 0 := lt_of_not_ge hmi
        have hs := (hstable i (hz i)).1
        nlinarith [hp i]
      · intro hm i
        have hmpos : 0 < m i := lt_of_le_of_ne (hm i) (Ne.symm (hz i))
        have hs := (hstable i (hz i)).1
        nlinarith
    have hniff : (∀ i, 0 ≤ n i) ↔ ∀ i, 0 ≤ m i := by
      constructor
      · intro hn i
        by_contra hmi
        have hmneg : m i < 0 := lt_of_not_ge hmi
        have hs := (hstable i (hz i)).2
        nlinarith [hn i]
      · intro hm i
        have hmpos : 0 < m i := lt_of_le_of_ne (hm i) (Ne.symm (hz i))
        have hs := (hstable i (hz i)).2
        nlinarith
    rw [hpiff, hniff]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    by_cases hm : ∀ i, 0 ≤ m i
    · simp [monskyIndicator, hoccfalse, hm, htwo]
    · simp [monskyIndicator, hoccfalse, hm]

private lemma monsky_mem_open_affineBasis_face_iff
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : AffineBasis (Fin 3) ℝ V) (i : Fin 3) (x : V) :
    x ∈ openSegment ℝ (b (i + 1)) (b (i + 2)) ↔
      b.coord i x = 0 ∧ ∀ j, j ≠ i → 0 < b.coord j x := by
  rw [openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · rw [(b.coord i).apply_lineMap]
      fin_cases i <;> norm_num [b.coord_apply, AffineMap.lineMap_apply]
    · intro j hji
      rw [(b.coord j).apply_lineMap]
      fin_cases i <;> fin_cases j
      all_goals norm_num [b.coord_apply, AffineMap.lineMap_apply] at hji
      all_goals norm_num [b.coord_apply, AffineMap.lineMap_apply]
      all_goals first | exact hr.1 | exact hr.2
  · rintro ⟨hi, hpos⟩
    have hsum := b.sum_coord_apply_eq_one x
    rw [Fin.sum_univ_three] at hsum
    fin_cases i
    · change b.coord 0 x = 0 at hi
      refine ⟨b.coord 2 x, ?_, ?_⟩
      · constructor
        · exact hpos 2 (by decide)
        · have := hpos 1 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith
    · change b.coord 1 x = 0 at hi
      refine ⟨b.coord 0 x, ?_, ?_⟩
      · constructor
        · exact hpos 0 (by decide)
        · have := hpos 2 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith
    · change b.coord 2 x = 0 at hi
      refine ⟨b.coord 1 x, ?_, ?_⟩
      · constructor
        · exact hpos 1 (by decide)
        · have := hpos 0 (by decide)
          linarith
      · apply b.ext_elem
        intro j
        rw [(b.coord j).apply_lineMap]
        fin_cases j <;> norm_num [b.coord_apply, AffineMap.lineMap_apply] <;> linarith

private lemma monsky_triangle_faceLine_injective
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) (t : ↑T) :
    Function.Injective fun i : Fin 3 ↦ monskyFaceLine T htriangle (.inl (t, i)) := by
  intro i j hij
  change monskyFaceLine T htriangle (.inl (t, i)) =
    monskyFaceLine T htriangle (.inl (t, j)) at hij
  by_contra hne
  have hvi : monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
      (monskyVertices T htriangle t i) ≠ 0 := by
    simp only [monskyFaceForm, ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    rw [(monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_eq]
    norm_num
  have hvj : monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
      (monskyVertices T htriangle t i) = 0 := by
    simp only [monskyFaceForm, ← monsky_triangleBasis_apply T htriangle hcard hvolume]
    exact (monskyTriangleBasis T htriangle hcard hvolume t).coord_apply_ne (Ne.symm hne)
  have hvjmem : monskyVertices T htriangle t i ∈
      monskyFaceLine T htriangle (.inl (t, j)) :=
    (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
      (.inl (t, j)) _).2 hvj
  rw [← hij] at hvjmem
  exact hvi ((monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, i)) _).1 hvjmem)

private lemma monsky_square_faceLine_injective
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    Function.Injective fun i : Fin 4 ↦ monskyFaceLine T htriangle (.inr i) := by
  intro i j hij
  change monskyFaceLine T htriangle (.inr i) =
    monskyFaceLine T htriangle (.inr j) at hij
  by_contra hne
  let x := midpoint ℝ (monskyFaceLeft T htriangle (.inr i))
    (monskyFaceRight T htriangle (.inr i))
  have hxi : x ∈ monskyFaceLine T htriangle (.inr i) := by
    rw [monskyFaceLine]
    exact AffineMap.lineMap_mem_affineSpan_pair (⅟2 : ℝ) _ _
  have hxj : x ∈ monskyFaceLine T htriangle (.inr j) := by
    rwa [← hij]
  have hxjzero := (monsky_mem_faceLine_iff_faceForm_eq_zero
    T htriangle hcard hvolume (.inr j) x).1 hxj
  fin_cases i <;> fin_cases j
  all_goals norm_num at hne
  all_goals norm_num [x, monskyFaceForm, monskyFaceLeft, monskyFaceRight,
      monskySquareSideForm, monskySquareCorner, monskyCoordinate,
      midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply,
      smul_eq_mul] at hxjzero

private lemma monsky_mem_open_square_face_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (i : Fin 4) (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ openSegment ℝ (monskyFaceLeft T htriangle (.inr i))
        (monskyFaceRight T htriangle (.inr i)) ↔
      monskySquareSideForm i x = 0 ∧
        ∀ j, j ≠ i → 0 < monskySquareSideForm j x := by
  rw [openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · fin_cases i <;> norm_num [monskyFaceLeft, monskyFaceRight,
        monskySquareSideForm, monskySquareCorner, monskyCoordinate,
        AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul]
    · intro j hji
      fin_cases i <;> fin_cases j
      all_goals norm_num [monskyFaceLeft, monskyFaceRight, monskySquareSideForm,
        monskySquareCorner, monskyCoordinate, AffineMap.lineMap_apply,
        vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul] at hji
      all_goals norm_num [monskyFaceLeft, monskyFaceRight, monskySquareSideForm,
        monskySquareCorner, monskyCoordinate, AffineMap.lineMap_apply,
        vsub_eq_sub, vadd_eq_add, PiLp.smul_apply, smul_eq_mul]
      all_goals first | exact hr.1 | exact hr.2
  · rintro ⟨hi, hpos⟩
    fin_cases i
    · refine ⟨x.ofLp 0, ?_, ?_⟩
      · have hxpos := hpos 3 (by decide)
        have hxlt := hpos 1 (by decide)
        change 0 < x.ofLp 0 at hxpos
        change 0 < 1 - x.ofLp 0 at hxlt
        exact ⟨hxpos, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨x.ofLp 1, ?_, ?_⟩
      · have hypos := hpos 0 (by decide)
        have hylt := hpos 2 (by decide)
        change 0 < x.ofLp 1 at hypos
        change 0 < 1 - x.ofLp 1 at hylt
        exact ⟨hypos, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨1 - x.ofLp 0, ?_, ?_⟩
      · have hxpos := hpos 3 (by decide)
        have hxlt := hpos 1 (by decide)
        change 0 < x.ofLp 0 at hxpos
        change 0 < 1 - x.ofLp 0 at hxlt
        exact ⟨by linarith, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith
    · refine ⟨1 - x.ofLp 1, ?_, ?_⟩
      · have hypos := hpos 0 (by decide)
        have hylt := hpos 2 (by decide)
        change 0 < x.ofLp 1 at hypos
        change 0 < 1 - x.ofLp 1 at hylt
        exact ⟨by linarith, by linarith⟩
      · ext j
        fin_cases j <;> norm_num [monskyFaceLeft, monskyFaceRight,
          monskySquareCorner, AffineMap.lineMap_apply, vsub_eq_sub,
          vadd_eq_add, PiLp.smul_apply, smul_eq_mul, monskySquareSideForm,
          monskyCoordinate] at hi ⊢
        all_goals linarith

private lemma monsky_faceLine_eq_of_atomMidpoint_mem
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (g : MonskyFace T)
    (hmg : monskyAtomMidpoint e ∈ monskyFaceLine T htriangle g) :
    monskyFaceLine T htriangle f = monskyFaceLine T htriangle g := by
  by_contra hne
  exact monsky_atomMidpoint_not_mem_distinct_faceLine
    T htriangle hcard hvolume f g e hef hne hmg

private lemma monsky_triangle_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i : Fin 3) :
    e ∈ monskyFaceAtomList T htriangle (.inl (t, i)) ↔
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
          (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceLeft, monskyFaceRight, monskyFaceForm,
    monsky_triangleBasis_apply] using
    (monsky_mem_open_affineBasis_face_iff
      (monskyTriangleBasis T htriangle hcard hvolume t) i (monskyAtomMidpoint e))

private lemma monsky_square_atom_occ_iff
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i : Fin 4) :
    e ∈ monskyFaceAtomList T htriangle (.inr i) ↔
      monskyFaceForm T htriangle hcard hvolume (.inr i) (monskyAtomMidpoint e) = 0 ∧
        ∀ j, j ≠ i →
          0 < monskyFaceForm T htriangle hcard hvolume (.inr j)
            (monskyAtomMidpoint e) := by
  rw [monsky_mem_faceAtomList_iff_atomMidpoint_mem_openSegment
    T htriangle hcard hvolume f e hef]
  simpa only [monskyFaceForm] using
    (monsky_mem_open_square_face_iff T htriangle i (monskyAtomMidpoint e))

private lemma monsky_triangle_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (t : ↑T) (i j : Fin 3)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inl (t, i))
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inl (t, j))
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, i)) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inl (t, j)) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, i)) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inl (t, j)) hmj
  exact monsky_triangle_faceLine_injective T htriangle hcard hvolume t
    (hfi.symm.trans hfj)

private lemma monsky_square_atom_unique_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) (i j : Fin 4)
    (hi : monskyFaceForm T htriangle hcard hvolume (.inr i)
      (monskyAtomMidpoint e) = 0)
    (hj : monskyFaceForm T htriangle hcard hvolume (.inr j)
      (monskyAtomMidpoint e) = 0) : i = j := by
  have hmi := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr i) (monskyAtomMidpoint e)).2 hi
  have hmj := (monsky_mem_faceLine_iff_faceForm_eq_zero T htriangle hcard hvolume
    (.inr j) (monskyAtomMidpoint e)).2 hj
  have hfi := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr i) hmi
  have hfj := monsky_faceLine_eq_of_atomMidpoint_mem
    T htriangle hcard hvolume f e hef (.inr j) hmj
  exact monsky_square_faceLine_injective T htriangle hcard hvolume (hfi.symm.trans hfj)

private lemma monsky_triangle_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0)
    (t : ↑T) :
    ∑ i : Fin 3, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1) := by
  have h := monsky_form_parity
    (m := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inl (t, i)) (monskyAtomMidpoint e))
    (p := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p)
    (n := fun i : Fin 3 ↦ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n)
    (occ := fun i : Fin 3 ↦ e ∈ monskyFaceAtomList T htriangle (.inl (t, i)))
    (monsky_triangle_atom_unique_zero T htriangle hcard hvolume f e hef t)
    (fun i ↦ hstable (.inl (t, i))) (fun i ↦ hflip (.inl (t, i)))
    (monsky_triangle_atom_occ_iff T htriangle hcard hvolume f e hef t)
  calc
    _ = monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) p) +
        monskyIndicator (∀ i : Fin 3,
          0 ≤ monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) n) := h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t n))).symm

private lemma monsky_square_atom_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f)
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0) :
    ∑ i : Fin 4, monskyIndicator
        (e ∈ monskyFaceAtomList T htriangle (.inr i)) =
      monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
  have h := monsky_form_parity
    (m := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume
      (.inr i) (monskyAtomMidpoint e))
    (p := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) p)
    (n := fun i : Fin 4 ↦ monskyFaceForm T htriangle hcard hvolume (.inr i) n)
    (occ := fun i : Fin 4 ↦ e ∈ monskyFaceAtomList T htriangle (.inr i))
    (monsky_square_atom_unique_zero T htriangle hcard hvolume f e hef)
    (fun i ↦ hstable (.inr i)) (fun i ↦ hflip (.inr i))
    (monsky_square_atom_occ_iff T htriangle hcard hvolume f e hef)
  calc
    _ = monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i p) +
        monskyIndicator (∀ i : Fin 4, 0 ≤ monskySquareSideForm i n) := by
      simpa only [monskyFaceForm] using h
    _ = _ := congrArg₂ (· + ·)
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms p))).symm
      (congrArg monskyIndicator
        (propext (monsky_mem_unitSquare_iff_faceForms n))).symm

private lemma monsky_sum_indicator_eq_indicator_of_unique
    {ι : Type*} [Fintype ι] (P : ι → Prop) (Q : Prop)
    (hexists : Q ↔ ∃ i, P i) (hunique : ∀ i j, P i → P j → i = j) :
    ∑ i, monskyIndicator (P i) = monskyIndicator Q := by
  classical
  by_cases hQ : Q
  · obtain ⟨k, hk⟩ := hexists.mp hQ
    have hP : ∀ i, P i ↔ i = k := by
      intro i
      exact ⟨fun hi ↦ hunique i k hi hk, fun hik ↦ hik ▸ hk⟩
    simp_rw [hP]
    simp [monskyIndicator, hQ]
  · have hP : ∀ i, ¬P i := by
      intro i hi
      exact hQ (hexists.mpr ⟨i, hi⟩)
    simp [monskyIndicator, hQ, hP]

private lemma monsky_probe_faceForms_ne_zero
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (p n : EuclideanSpace ℝ (Fin 2))
    (hstable : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) ≠ 0 →
        0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g p ∧
          0 < monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) *
            monskyFaceForm T htriangle hcard hvolume g n)
    (hflip : ∀ g : MonskyFace T,
      monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0 →
        monskyFaceForm T htriangle hcard hvolume g p *
          monskyFaceForm T htriangle hcard hvolume g n < 0) (g : MonskyFace T) :
    monskyFaceForm T htriangle hcard hvolume g p ≠ 0 ∧
      monskyFaceForm T htriangle hcard hvolume g n ≠ 0 := by
  by_cases hm : monskyFaceForm T htriangle hcard hvolume g (monskyAtomMidpoint e) = 0
  · have hprod := hflip g hm
    constructor <;> intro hzero <;> simp [hzero] at hprod
  · have hprod := hstable g hm
    constructor
    · intro hzero
      rw [hzero, mul_zero] at hprod
      exact (lt_irrefl 0) hprod.1
    · intro hzero
      rw [hzero, mul_zero] at hprod
      exact (lt_irrefl 0) hprod.2

private lemma monsky_tile_membership_unique
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0)
    (t u : ↑T) (hxt : x ∈ t.1) (hxu : x ∈ u.1) : t = u := by
  apply Subtype.ext
  apply hdisjoint.elim t.2 u.2
  apply Set.not_disjoint_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume t x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume t x).1 hxt i)
      (Ne.symm (hface t i))
  · apply (monsky_mem_interior_tile_iff_faceForms
      T htriangle hcard hvolume u x).2
    intro i
    exact lt_of_le_of_ne
      ((monsky_mem_tile_iff_faceForms T htriangle hcard hvolume u x).1 hxu i)
      (Ne.symm (hface u i))

private lemma monsky_sum_tile_indicator_eq_square
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (x : EuclideanSpace ℝ (Fin 2))
    (hface : ∀ (t : ↑T) (i : Fin 3),
      monskyFaceForm T htriangle hcard hvolume (.inl (t, i)) x ≠ 0) :
    ∑ t : ↑T, monskyIndicator (x ∈ t.1) =
      monskyIndicator
        (x ∈ {y : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ y.ofLp i ∧ y.ofLp i ≤ 1}) := by
  apply monsky_sum_indicator_eq_indicator_of_unique
  · constructor
    · intro hx
      have hxunion : x ∈ Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) :=
        hcover.symm ▸ hx
      obtain ⟨s, hsT, hxs⟩ := Set.mem_sUnion.mp hxunion
      exact ⟨⟨s, hsT⟩, hxs⟩
    · rintro ⟨t, hxt⟩
      rw [← hcover]
      exact Set.mem_sUnion_of_mem hxt t.2
  · intro t u hxt hxu
    exact monsky_tile_membership_unique
      T htriangle hcard hvolume hdisjoint x hface t u hxt hxu

private lemma monsky_atom_incidence_parity
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior)
    (f : MonskyFace T) (e : Sym2 (EuclideanSpace ℝ (Fin 2)))
    (hef : e ∈ monskyFaceAtomList T htriangle f) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) =
      ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  obtain ⟨p, n, hstable, hflip⟩ :=
    monsky_exists_atom_probes T htriangle hcard hvolume f e hef
  have hne := monsky_probe_faceForms_ne_zero
    T htriangle hcard hvolume e p n hstable hflip
  have hp := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint p (fun t i ↦ (hne (.inl (t, i))).1)
  have hn := monsky_sum_tile_indicator_eq_square
    T htriangle hcard hvolume hcover hdisjoint n (fun t i ↦ (hne (.inl (t, i))).2)
  calc
    _ = ∑ t : ↑T, (monskyIndicator (p ∈ t.1) + monskyIndicator (n ∈ t.1)) :=
      Finset.sum_congr rfl fun t _ ↦
        monsky_triangle_atom_parity
          T htriangle hcard hvolume f e hef p n hstable hflip t
    _ = (∑ t : ↑T, monskyIndicator (p ∈ t.1)) +
        ∑ t : ↑T, monskyIndicator (n ∈ t.1) := Finset.sum_add_distrib
    _ = monskyIndicator
          (p ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) +
        monskyIndicator
          (n ∈ {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}) := by
      rw [hp, hn]
    _ = _ := (monsky_square_atom_parity
      T htriangle hcard hvolume f e hef p n hstable hflip).symm

private noncomputable def monskyColor (V : ValuationSubring ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) : Fin 3 :=
  if 1 ≤ V.valuation (p.ofLp 0) ∧ V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) then
    0
  else if 1 ≤ V.valuation (p.ofLp 1) then 1 else 2

private lemma monsky_color_eq_zero_iff (V : ValuationSubring ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    monskyColor V p = 0 ↔
      1 ≤ V.valuation (p.ofLp 0) ∧
        V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
      V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · simp [monskyColor, h]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · simp [monskyColor, h, hy]
    · simp [monskyColor, h, hy]

private lemma monsky_color_eq_one_iff (V : ValuationSubring ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    monskyColor V p = 1 ↔
      1 ≤ V.valuation (p.ofLp 1) ∧
        V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
      V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · have hnlt : ¬V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) :=
      not_lt_of_ge h.2
    simp [monskyColor, h, hnlt]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · have hxlt : V.valuation (p.ofLp 0) < V.valuation (p.ofLp 1) := by
        by_contra hnlt
        have hyvx : V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0) :=
          le_of_not_gt hnlt
        exact h ⟨hy.trans hyvx, hyvx⟩
      simp [monskyColor, h, hy, hxlt]
    · simp [monskyColor, h, hy]

private lemma monsky_color_eq_two_iff (V : ValuationSubring ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    monskyColor V p = 2 ↔
      V.valuation (p.ofLp 0) < 1 ∧ V.valuation (p.ofLp 1) < 1 := by
  by_cases h : 1 ≤ V.valuation (p.ofLp 0) ∧
      V.valuation (p.ofLp 1) ≤ V.valuation (p.ofLp 0)
  · have hnx : ¬V.valuation (p.ofLp 0) < 1 := not_lt_of_ge h.1
    simp [monskyColor, h, hnx]
  · by_cases hy : 1 ≤ V.valuation (p.ofLp 1)
    · have hny : ¬V.valuation (p.ofLp 1) < 1 := not_lt_of_ge hy
      simp [monskyColor, h, hy, hny]
    · have hylt : V.valuation (p.ofLp 1) < 1 := lt_of_not_ge hy
      have hxlt : V.valuation (p.ofLp 0) < 1 := by
        by_contra hnx
        have hx : 1 ≤ V.valuation (p.ofLp 0) := le_of_not_gt hnx
        exact h ⟨hx, hylt.le.trans hx⟩
      simp [monskyColor, h, hy, hxlt, hylt]

private lemma monsky_color_add_of_color_two (V : ValuationSubring ℝ)
    (p z : EuclideanSpace ℝ (Fin 2)) (hz : monskyColor V z = 2) :
    monskyColor V (p + z) = monskyColor V p := by
  obtain ⟨hz0, hz1⟩ := (monsky_color_eq_two_iff V z).1 hz
  generalize hc : monskyColor V p = c
  fin_cases c
  · obtain ⟨hp0, hp10⟩ := (monsky_color_eq_zero_iff V p).1 hc
    change monskyColor V (p + z) = 0
    have hx : V.valuation ((p + z).ofLp 0) = V.valuation (p.ofLp 0) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz0.trans_le hp0)
    rw [monsky_color_eq_zero_iff, hx]
    refine ⟨hp0, ?_⟩
    by_cases hp1 : 1 ≤ V.valuation (p.ofLp 1)
    · have hy : V.valuation ((p + z).ofLp 1) = V.valuation (p.ofLp 1) := by
        simpa using V.valuation.map_add_eq_of_lt_left (hz1.trans_le hp1)
      rw [hy]
      exact hp10
    · exact (V.valuation.map_add_lt (lt_of_not_ge hp1) hz1).le.trans hp0
  · obtain ⟨hp1, hp01⟩ := (monsky_color_eq_one_iff V p).1 hc
    change monskyColor V (p + z) = 1
    have hy : V.valuation ((p + z).ofLp 1) = V.valuation (p.ofLp 1) := by
      simpa using V.valuation.map_add_eq_of_lt_left (hz1.trans_le hp1)
    rw [monsky_color_eq_one_iff, hy]
    refine ⟨hp1, ?_⟩
    by_cases hp0 : 1 ≤ V.valuation (p.ofLp 0)
    · have hx : V.valuation ((p + z).ofLp 0) = V.valuation (p.ofLp 0) := by
        simpa using V.valuation.map_add_eq_of_lt_left (hz0.trans_le hp0)
      rw [hx]
      exact hp01
    · exact (V.valuation.map_add_lt (lt_of_not_ge hp0) hz0).trans_le hp1
  · obtain ⟨hp0, hp1⟩ := (monsky_color_eq_two_iff V p).1 hc
    change monskyColor V (p + z) = 2
    rw [monsky_color_eq_two_iff]
    exact ⟨by simpa using V.valuation.map_add_lt hp0 hz0,
      by simpa using V.valuation.map_add_lt hp1 hz1⟩

private lemma monsky_det_ne_zero_of_colors (V : ValuationSubring ℝ)
    (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
    (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
    (a - c).ofLp 0 * (b - c).ofLp 1 -
      (a - c).ofLp 1 * (b - c).ofLp 0 ≠ 0 := by
  obtain ⟨hc0, hc1⟩ := (monsky_color_eq_two_iff V c).1 hc
  have hnegc : monskyColor V (-c) = 2 := (monsky_color_eq_two_iff V (-c)).2 ⟨by
    simpa using (V.valuation.map_neg (c.ofLp 0)).trans_lt hc0, by
    simpa using (V.valuation.map_neg (c.ofLp 1)).trans_lt hc1⟩
  have ha' : monskyColor V (a - c) = 0 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V a (-c) hnegc, ha]
  have hb' : monskyColor V (b - c) = 1 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V b (-c) hnegc, hb]
  obtain ⟨ha0, ha10⟩ := (monsky_color_eq_zero_iff V (a - c)).1 ha'
  obtain ⟨hb1, hb01⟩ := (monsky_color_eq_one_iff V (b - c)).1 hb'
  intro hdet
  have hprod : (a - c).ofLp 0 * (b - c).ofLp 1 =
      (a - c).ofLp 1 * (b - c).ofLp 0 := sub_eq_zero.mp hdet
  have hval := congrArg V.valuation hprod
  rw [V.valuation.map_mul, V.valuation.map_mul] at hval
  have hlt : V.valuation ((a - c).ofLp 1) * V.valuation ((b - c).ofLp 0) <
      V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) := calc
    _ ≤ V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 0) :=
      mul_le_mul_left ha10 _
    _ < V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) :=
      mul_lt_mul_of_pos_left hb01 (zero_lt_one.trans_le ha0)
  exact hlt.ne hval.symm

private lemma monsky_not_collinear_of_colors (V : ValuationSubring ℝ)
    (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
    (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
    ¬Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hcollinear
  obtain ⟨p, v, hp⟩ :=
    (collinear_iff_exists_forall_eq_smul_vadd
      ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))).1 hcollinear
  obtain ⟨ra, hra⟩ := hp a (by simp)
  obtain ⟨rb, hrb⟩ := hp b (by simp)
  obtain ⟨rc, hrc⟩ := hp c (by simp)
  apply monsky_det_ne_zero_of_colors V a b c ha hb hc
  rw [hra, hrb, hrc]
  simp only [vadd_eq_add, add_sub_add_right_eq_sub, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

private lemma monsky_facePointList_mem_faceLine
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ monskyFacePointList T htriangle f) :
    x ∈ monskyFaceLine T htriangle f := by
  rw [monskyFacePointList, List.mem_map] at hx
  obtain ⟨r, _, rfl⟩ := hx
  rw [monskyFaceLine]
  exact AffineMap.lineMap_mem_affineSpan_pair r _ _

private lemma monsky_facePointList_uses_two_colors (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    ∃ i j : Fin 3, ∀ x ∈ monskyFacePointList T htriangle f,
      monskyColor V x = i ∨ monskyColor V x = j := by
  classical
  by_cases hzero : ∃ x ∈ monskyFacePointList T htriangle f, monskyColor V x = 0
  · obtain ⟨a, haList, ha⟩ := hzero
    by_cases hone : ∃ x ∈ monskyFacePointList T htriangle f, monskyColor V x = 1
    · obtain ⟨b, hbList, hb⟩ := hone
      refine ⟨0, 1, ?_⟩
      intro x hxList
      have htwo : monskyColor V x ≠ 2 := by
        intro hx
        apply monsky_not_collinear_of_colors V a b x ha hb hx
        exact collinear_triple_of_mem_affineSpan_pair
          (monsky_facePointList_mem_faceLine T htriangle f haList)
          (monsky_facePointList_mem_faceLine T htriangle f hbList)
          (monsky_facePointList_mem_faceLine T htriangle f hxList)
      generalize hx : monskyColor V x = c
      fin_cases c <;> simp_all
    · refine ⟨0, 2, ?_⟩
      intro x hxList
      have hxone : monskyColor V x ≠ 1 := fun hx ↦ hone ⟨x, hxList, hx⟩
      generalize hx : monskyColor V x = c
      fin_cases c <;> simp_all
  · refine ⟨1, 2, ?_⟩
    intro x hxList
    have hxzero : monskyColor V x ≠ 0 := fun hx ↦ hzero ⟨x, hxList, hx⟩
    generalize hx : monskyColor V x = c
    fin_cases c <;> simp_all

private lemma monsky_edgeWeight_comm (i j : Fin 3) :
    monskyEdgeWeight i j = monskyEdgeWeight j i := by
  revert i j
  decide

private noncomputable def monskyAtomWeight (V : ValuationSubring ℝ) :
    Sym2 (EuclideanSpace ℝ (Fin 2)) → ZMod 2 :=
  Sym2.lift ⟨fun a b ↦ monskyEdgeWeight (monskyColor V a) (monskyColor V b), by
    intro a b
    exact monsky_edgeWeight_comm _ _⟩

@[simp] private lemma monsky_atomWeight_mk (V : ValuationSubring ℝ)
    (a b : EuclideanSpace ℝ (Fin 2)) :
    monskyAtomWeight V s(a, b) =
      monskyEdgeWeight (monskyColor V a) (monskyColor V b) := by
  rfl

private lemma monsky_pathWeight_eq_sum_consecutivePairs : ∀ l : List (Fin 3),
    monskyPathWeight l =
      (l.consecutivePairs.map fun e ↦ monskyEdgeWeight e.1 e.2).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b l =>
          rw [show (a :: b :: l).consecutivePairs =
            (a, b) :: (b :: l).consecutivePairs from rfl]
          simp only [List.map_cons, List.sum_cons, monskyPathWeight]
          rw [ih]

private lemma monsky_facePointList_ne_nil
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    monskyFacePointList T htriangle f ≠ [] := by
  simp [monskyFacePointList, monskyFaceParamList]

private lemma monsky_facePointList_head
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    (monskyFacePointList T htriangle f).head
        (monsky_facePointList_ne_nil T htriangle f) = monskyFaceLeft T htriangle f := by
  simp [monskyFacePointList, monskyFaceParamList, AffineMap.lineMap_apply]

private lemma monsky_facePointList_getLast
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    (monskyFacePointList T htriangle f).getLast
        (monsky_facePointList_ne_nil T htriangle f) = monskyFaceRight T htriangle f := by
  simp [monskyFacePointList, monskyFaceParamList, AffineMap.lineMap_apply]

private lemma monsky_sum_faceAtomWeight (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (f : MonskyFace T) :
    ((monskyFaceAtomList T htriangle f).map (monskyAtomWeight V)).sum =
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle f))
        (monskyColor V (monskyFaceRight T htriangle f)) := by
  let l := monskyFacePointList T htriangle f
  obtain ⟨i, j, hij⟩ := monsky_facePointList_uses_two_colors V T htriangle f
  have hall : ∀ c ∈ l.map (monskyColor V), c = i ∨ c = j := by
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact hij x hx
  have hne : l.map (monskyColor V) ≠ [] := by
    rw [Ne, List.map_eq_nil_iff]
    exact monsky_facePointList_ne_nil T htriangle f
  calc
    _ = (l.consecutivePairs.map fun e ↦
          monskyEdgeWeight (monskyColor V e.1) (monskyColor V e.2)).sum := by
      change ((l.consecutivePairs.map fun e ↦ s(e.1, e.2)).map
          (monskyAtomWeight V)).sum = _
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      rcases e with ⟨a, b⟩
      rfl
    _ = monskyPathWeight (l.map (monskyColor V)) := by
      rw [monsky_pathWeight_eq_sum_consecutivePairs, monsky_consecutivePairs_map]
      apply congrArg List.sum
      rw [List.map_map]
      apply List.map_congr_left
      intro e he
      rfl
    _ = monskyEdgeWeight
          ((l.map (monskyColor V)).head hne) ((l.map (monskyColor V)).getLast hne) :=
      monsky_pathWeight_eq_edgeWeight i j _ hall hne
    _ = _ := by
      rw [List.head_map, List.getLast_map, monsky_facePointList_head,
        monsky_facePointList_getLast]

private lemma monsky_sym2_consecutivePairs_nodup {α : Type*} : ∀ l : List α,
    l.Nodup → (l.consecutivePairs.map fun e ↦ s(e.1, e.2)).Nodup := by
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil =>
          rw [show [a].consecutivePairs = [] from rfl]
          exact List.Pairwise.nil
      | cons b l =>
          rw [show (a :: b :: l).consecutivePairs =
            (a, b) :: (b :: l).consecutivePairs from rfl, List.map_cons,
            List.nodup_cons]
          refine ⟨?_, ih hl.tail⟩
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨⟨x, y⟩, hxy, heq⟩ := hmem
          have ha : a ∈ s(x, y) := by
            rw [heq]
            exact Sym2.mem_mk_left a b
          rw [Sym2.mem_iff] at ha
          have ha_not : a ∉ b :: l := (List.nodup_cons.mp hl).1
          rcases ha with hax | hay
          · exact ha_not (hax ▸ monsky_fst_mem_of_mem_consecutivePairs hxy)
          · exact ha_not (hay ▸ monsky_snd_mem_of_mem_consecutivePairs hxy)

private lemma monsky_facePointList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFacePointList T htriangle f).Nodup := by
  rw [monskyFacePointList]
  exact (monsky_faceParamList_sorted T htriangle hcard hvolume f).nodup.map
    (AffineMap.lineMap_injective ℝ
      (monsky_face_endpoints_ne T htriangle hcard hvolume f))

private lemma monsky_faceAtomList_nodup
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) : (monskyFaceAtomList T htriangle f).Nodup := by
  rw [monskyFaceAtomList]
  exact monsky_sym2_consecutivePairs_nodup _
    (monsky_facePointList_nodup T htriangle hcard hvolume f)

private lemma monsky_sum_atoms_weighted_faceIndicator (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) =
      ((monskyFaceAtomList T htriangle f).map (monskyAtomWeight V)).sum := by
  classical
  let s := (monskyFaceAtomList T htriangle f).toFinset
  have hsubset : s ⊆ monskyAtoms T htriangle := by
    intro e he
    simp only [s, List.mem_toFinset] at he
    simp only [monskyAtoms, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨f, by simpa using he⟩
  calc
    _ = ∑ e ∈ monskyAtoms T htriangle,
        if e ∈ s then monskyAtomWeight V e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hes : e ∈ s
      · have hesList : e ∈ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, hesList]
      · have henot : e ∉ monskyFaceAtomList T htriangle f := by
          simpa only [s, List.mem_toFinset] using hes
        simp [monskyIndicator, hes, henot]
    _ = ∑ e ∈ s, if e ∈ s then monskyAtomWeight V e else 0 := by
      symm
      apply Finset.sum_subset hsubset
      intro e he henot
      simp [henot]
    _ = ∑ e ∈ s, monskyAtomWeight V e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [he]
    _ = _ := List.sum_toFinset (monskyAtomWeight V)
      (monsky_faceAtomList_nodup T htriangle hcard hvolume f)

private lemma monsky_atom_mem_exists_face
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c})
    {e : Sym2 (EuclideanSpace ℝ (Fin 2))} (he : e ∈ monskyAtoms T htriangle) :
    ∃ f : MonskyFace T, e ∈ monskyFaceAtomList T htriangle f := by
  rw [monskyAtoms, Finset.mem_biUnion] at he
  obtain ⟨f, _, hef⟩ := he
  exact ⟨f, List.mem_toFinset.mp hef⟩

private lemma monsky_faceEndpointWeight_eq_sum_atoms (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (f : MonskyFace T) :
    monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle f))
        (monskyColor V (monskyFaceRight T htriangle f)) =
      ∑ e ∈ monskyAtoms T htriangle,
        monskyAtomWeight V e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle f) :=
  (monsky_sum_faceAtomWeight V T htriangle f).symm.trans
    (monsky_sum_atoms_weighted_faceIndicator
      V T htriangle hcard hvolume f).symm

private lemma monsky_sum_weighted_swap {α β : Type*} [Fintype β]
    (s : Finset α) (w : α → ZMod 2) (q : α → β → ZMod 2) :
    ∑ b : β, ∑ a ∈ s, w a * q a b =
      ∑ a ∈ s, w a * ∑ b : β, q a b := by
  classical
  calc
    _ = ∑ a ∈ s, ∑ b : β, w a * q a b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

private lemma monsky_triangle_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ t : ↑T, ∑ i : Fin 3,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ t : ↑T, ∑ i : Fin 3, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inl (t, i))
    _ = ∑ t : ↑T, ∑ e ∈ A, w e * ∑ i : Fin 3,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inl (t, i))) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact monsky_sum_weighted_swap A w _
    _ = _ := by
      exact monsky_sum_weighted_swap A w _

private lemma monsky_square_boundary_eq_atom_sum (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ)) :
    ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) =
      ∑ e ∈ monskyAtoms T htriangle, monskyAtomWeight V e *
        ∑ i : Fin 4,
          monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
  classical
  let A := monskyAtoms T htriangle
  let w := monskyAtomWeight V
  calc
    _ = ∑ i : Fin 4, ∑ e ∈ A,
        w e * monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact monsky_faceEndpointWeight_eq_sum_atoms
        V T htriangle hcard hvolume (.inr i)
    _ = ∑ e ∈ A, w e * ∑ i : Fin 4,
        monskyIndicator (e ∈ monskyFaceAtomList T htriangle (.inr i)) :=
      monsky_sum_weighted_swap A w _

private lemma monsky_boundary_weight_identity (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∑ t : ↑T, ∑ i : Fin 3,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
          (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) =
      ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) := by
  rw [monsky_triangle_boundary_eq_atom_sum V T htriangle hcard hvolume,
    monsky_square_boundary_eq_atom_sum V T htriangle hcard hvolume]
  apply Finset.sum_congr rfl
  intro e he
  apply congrArg (monskyAtomWeight V e * ·)
  obtain ⟨f, hef⟩ := monsky_atom_mem_exists_face T htriangle he
  exact monsky_atom_incidence_parity
    T htriangle hcard hvolume hcover hdisjoint f e hef

private lemma monsky_square_boundary_weight_eq_one (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) :
    ∑ i : Fin 4,
        monskyEdgeWeight
          (monskyColor V (monskyFaceLeft T htriangle (.inr i)))
          (monskyColor V (monskyFaceRight T htriangle (.inr i))) = 1 := by
  have h0 : monskyColor V (monskySquareCorner 0) = 2 :=
    (monsky_color_eq_two_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h1 : monskyColor V (monskySquareCorner 1) = 0 :=
    (monsky_color_eq_zero_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h2 : monskyColor V (monskySquareCorner 2) = 0 :=
    (monsky_color_eq_zero_iff V _).2 (by
      norm_num [monskySquareCorner])
  have h3 : monskyColor V (monskySquareCorner 3) = 1 :=
    (monsky_color_eq_one_iff V _).2 (by
      norm_num [monskySquareCorner])
  rw [Fin.sum_univ_four]
  norm_num [monskyFaceLeft, monskyFaceRight, h0, h1, h2, h3, monskyEdgeWeight]

private lemma monsky_zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val = 0 ∨ x.val = 1 := by
    have := x.val_lt
    omega
  rcases hx with hx | hx
  · left
    apply ZMod.val_injective
    simpa using hx
  · right
    apply ZMod.val_injective
    rw [ZMod.val_one]
    exact hx

private lemma monsky_exists_rainbow_triangle (V : ValuationSubring ℝ)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (htriangle : ∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2),
      t = convexHull ℝ {a, b, c}) (hcard : T.card ≠ 0)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    (hcover : Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
      {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1})
    (hdisjoint : (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior) :
    ∃ (t : ↑T) (a b c : EuclideanSpace ℝ (Fin 2)),
      t.1 = convexHull ℝ {a, b, c} ∧
        monskyColor V a = 0 ∧ monskyColor V b = 1 ∧ monskyColor V c = 2 := by
  have hsum : ∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i)))) = 1 :=
    (monsky_boundary_weight_identity
      V T htriangle hcard hvolume hcover hdisjoint).trans
      (monsky_square_boundary_weight_eq_one V T htriangle)
  have hsumne : (∑ t : ↑T, ∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨t, _, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have htone : (∑ i : Fin 3,
      monskyEdgeWeight
        (monskyColor V (monskyFaceLeft T htriangle (.inl (t, i))))
        (monskyColor V (monskyFaceRight T htriangle (.inl (t, i))))) = 1 :=
    (monsky_zmod_two_eq_zero_or_one _).resolve_left htne
  let v := monskyVertices T htriangle t
  have hcycle :
      monskyEdgeWeight (monskyColor V (v 1)) (monskyColor V (v 2)) +
          monskyEdgeWeight (monskyColor V (v 2)) (monskyColor V (v 0)) +
        monskyEdgeWeight (monskyColor V (v 0)) (monskyColor V (v 1)) = 1 := by
    simpa [Fin.sum_univ_three, monskyFaceLeft, monskyFaceRight, v] using htone
  obtain ⟨h12, h20, h01⟩ :=
    (monskyEdgeWeight_triangle
      (monskyColor V (v 1)) (monskyColor V (v 2)) (monskyColor V (v 0))).1 hcycle
  let colorIndex : Fin 3 → Fin 3 := fun i ↦ monskyColor V (v i)
  have hinj : Function.Injective colorIndex := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [colorIndex]
  have hsurj : Function.Surjective colorIndex := Finite.surjective_of_injective hinj
  obtain ⟨i0, hi0⟩ := hsurj 0
  obtain ⟨i1, hi1⟩ := hsurj 1
  obtain ⟨i2, hi2⟩ := hsurj 2
  have hindices : ∀ i : Fin 3, i = i0 ∨ i = i1 ∨ i = i2 := by
    intro i
    have hc : colorIndex i = 0 ∨ colorIndex i = 1 ∨ colorIndex i = 2 := by
      generalize hci : colorIndex i = ci
      fin_cases ci <;> simp_all
    rcases hc with hc | hc | hc
    · exact Or.inl (hinj (hc.trans hi0.symm))
    · exact Or.inr (Or.inl (hinj (hc.trans hi1.symm)))
    · exact Or.inr (Or.inr (hinj (hc.trans hi2.symm)))
  have hrange : ({v i0, v i1, v i2} : Set (EuclideanSpace ℝ (Fin 2))) = Set.range v := by
    ext x
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨i0, rfl⟩
      · exact ⟨i1, rfl⟩
      · exact ⟨i2, rfl⟩
    · rintro ⟨i, rfl⟩
      rcases hindices i with rfl | rfl | rfl <;> simp
  refine ⟨t, v i0, v i1, v i2, ?_, hi0, hi1, hi2⟩
  rw [monsky_vertices_spec T htriangle t, ← hrange]

private lemma monsky_one_le_valuation_det_of_colors (V : ValuationSubring ℝ)
    (a b c : EuclideanSpace ℝ (Fin 2)) (ha : monskyColor V a = 0)
    (hb : monskyColor V b = 1) (hc : monskyColor V c = 2) :
    1 ≤ V.valuation ((a - c).ofLp 0 * (b - c).ofLp 1 -
      (a - c).ofLp 1 * (b - c).ofLp 0) := by
  obtain ⟨hc0, hc1⟩ := (monsky_color_eq_two_iff V c).1 hc
  have hnegc : monskyColor V (-c) = 2 := (monsky_color_eq_two_iff V (-c)).2 ⟨by
    simpa using (V.valuation.map_neg (c.ofLp 0)).trans_lt hc0, by
    simpa using (V.valuation.map_neg (c.ofLp 1)).trans_lt hc1⟩
  have ha' : monskyColor V (a - c) = 0 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V a (-c) hnegc, ha]
  have hb' : monskyColor V (b - c) = 1 := by
    rw [sub_eq_add_neg, monsky_color_add_of_color_two V b (-c) hnegc, hb]
  obtain ⟨ha0, ha10⟩ := (monsky_color_eq_zero_iff V (a - c)).1 ha'
  obtain ⟨hb1, hb01⟩ := (monsky_color_eq_one_iff V (b - c)).1 hb'
  have hlt : V.valuation ((a - c).ofLp 1 * (b - c).ofLp 0) <
      V.valuation ((a - c).ofLp 0 * (b - c).ofLp 1) := by
    simp only [V.valuation.map_mul]
    calc
      _ ≤ V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 0) :=
        mul_le_mul_left ha10 _
      _ < V.valuation ((a - c).ofLp 0) * V.valuation ((b - c).ofLp 1) :=
        mul_lt_mul_of_pos_left hb01 (zero_lt_one.trans_le ha0)
  rw [V.valuation.map_sub_eq_of_lt_left hlt, V.valuation.map_mul]
  simpa only [one_mul] using mul_le_mul' ha0 hb1

private lemma monsky_odd_card_contradiction (V : ValuationSubring ℝ)
    (hint : ∀ z : ℤ, V.valuation (z : ℝ) ≤ 1) (htwo : V.valuation 2 < 1)
    (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))) (hodd : Odd T.card)
    (hvolume : ∀ t ∈ T, (volume t).toReal = 1 / (T.card : ℝ))
    {t : Set (EuclideanSpace ℝ (Fin 2))} (ht : t ∈ T)
    (a b c : EuclideanSpace ℝ (Fin 2))
    (htabc : t = convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))
    (ha : monskyColor V a = 0) (hb : monskyColor V b = 1)
    (hc : monskyColor V c = 2) : False := by
  let d : ℝ := (a - c).ofLp 0 * (b - c).ofLp 1 -
    (a - c).ofLp 1 * (b - c).ofLp 0
  have habs : |d| = 2 / (T.card : ℝ) :=
    monsky_abs_det_eq_two_div_card T hvolume ht a b c htabc
  have hoddInt : Odd (T.card : ℤ) := by exact_mod_cast hodd
  have hcardVal : V.valuation (T.card : ℝ) = 1 := by
    simpa using monsky_valuation_odd_eq_one V hint htwo hoddInt
  have habsVal : V.valuation |d| = V.valuation d := by
    rcases abs_choice d with hd | hd
    · rw [hd]
    · rw [hd, V.valuation.map_neg]
  have hdVal : V.valuation d = V.valuation 2 := calc
    V.valuation d = V.valuation |d| := habsVal.symm
    _ = V.valuation (2 / (T.card : ℝ)) := congrArg V.valuation habs
    _ = V.valuation 2 / V.valuation (T.card : ℝ) := V.valuation.map_div _ _
    _ = V.valuation 2 := by rw [hcardVal, div_one]
  have hone : 1 ≤ V.valuation d :=
    monsky_one_le_valuation_det_of_colors V a b c ha hb hc
  exact (not_lt_of_ge (hdVal ▸ hone)) htwo

/-- Monsky's theorem (statement_id `monsky-s1`): a dissection of a square into
finitely many triangles of equal area (an equidissection) uses an even number
of triangles.

Source: Paul Monsky, "On Dividing A Square Into Triangles," *The American Mathematical
Monthly* 77(2) (1970), 161–164, DOI 10.1080/00029890.1970.11992441.

Proves `Wanted` entry `monsky_theorem`.

Proof: A 2-adic valuation on ℝ gives a three-colouring of the plane, and a Sperner-type parity
count supplies a rainbow triangle whose area valuation rules out an odd number of pieces.
-/
theorem monsky_theorem :
    ∀ (T : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ t ∈ T, ∃ a b c : EuclideanSpace ℝ (Fin 2), t = convexHull ℝ {a, b, c}) →
      Set.sUnion (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))) =
        {x | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} →
      (↑T : Set (Set (EuclideanSpace ℝ (Fin 2)))).PairwiseDisjoint interior →
      (∃ A : ENNReal, ∀ t ∈ T, MeasureTheory.volume t = A) →
      Even T.card := by
  intro T htriangle hcover hdisjoint hcommon
  obtain ⟨A, hA⟩ := hcommon
  have hsum := monsky_sum_volume_eq_one T htriangle hcover hdisjoint
  obtain ⟨hcard, hvolume⟩ := monsky_common_volume_eq_card_inv T hsum A hA
  obtain ⟨V, hint, htwo⟩ := monsky_exists_valuation_int_le_one_two_lt_one
  obtain ⟨t, a, b, c, htabc, ha, hb, hc⟩ :=
    monsky_exists_rainbow_triangle
      V T htriangle hcard hvolume hcover hdisjoint
  by_contra heven
  exact monsky_odd_card_contradiction V hint htwo T
    (Nat.not_even_iff_odd.mp heven) hvolume t.2 a b c htabc ha hb hc

end MetaMathlibExt
