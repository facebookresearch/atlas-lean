/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.ZMultiples

/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/

namespace MetaMathlibExt

@[expose] public section
open Filter MeasureTheory
open scoped Pointwise

private abbrev pickCast (z : Fin 2 → ℤ) : Fin 2 → ℝ := fun i ↦ z i

private theorem pick_cast_injective : Function.Injective pickCast := by
  intro x y hxy
  ext i
  exact_mod_cast congrFun hxy i

private theorem pick_lattice_preimage_finite {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    Set.Finite (pickCast ⁻¹' K) := by
  have hcast : Tendsto pickCast Filter.cofinite (cocompact (Fin 2 → ℝ)) := by
    convert! Tendsto.pi_map_coprodᵢ fun _ ↦ Int.tendsto_coe_cofinite
    · rw [coprodᵢ_cofinite]
    · rw [coprodᵢ_cocompact]
  exact tendsto_cofinite_cocompact_iff.mp hcast K hK

private def pickVecs (u v : Fin 2 → ℤ) : Fin 2 → Fin 2 → ℝ := ![pickCast u, pickCast v]

private def pickMatrix (u v : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (pickVecs u v)

private def pickDet (u v : Fin 2 → ℤ) : ℤ := u 0 * v 1 - u 1 * v 0

private theorem pick_matrix_det (u v : Fin 2 → ℤ) :
    (pickMatrix u v).det = (pickDet u v : ℝ) := by
  simp [pickMatrix, pickVecs, pickDet, pickCast, Matrix.det_fin_two]

private noncomputable def pickBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  let A := (pickMatrix u v).transpose
  let e : (Fin 2 → ℝ) ≃ₗ[ℝ] Fin 2 → ℝ :=
    Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) A <| by
      rw [isUnit_iff_ne_zero, Matrix.det_transpose, pick_matrix_det]
      exact_mod_cast h
  (Pi.basisFun ℝ (Fin 2)).map e

private theorem pick_basis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) (i : Fin 2) :
    pickBasis u v h i = pickVecs u v i := by
  rw [pickBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one]
  ext j
  simp [pickMatrix, pickVecs, pickCast]

private theorem pick_matrix_of_basis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Matrix.of (pickBasis u v h) = pickMatrix u v := by
  ext i j
  simp [pick_basis_apply, pickMatrix]

private noncomputable def pickTrianglePoints (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 3 → Fin 2 → ℝ := ![0, pickBasis u v h 0, pickBasis u v h 1]

private theorem pick_trianglePoints_affineIndependent (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : AffineIndependent ℝ (pickTrianglePoints u v h) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
  let e := finSuccAboveEquiv (0 : Fin 3)
  have hli := (pickBasis u v h).linearIndependent.comp e.symm e.symm.injective
  convert hli using 1
  funext q
  rcases q with ⟨j, hj⟩
  fin_cases j
  · simp at hj
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  · simp only [pickTrianglePoints, Function.comp_apply, vsub_eq_sub, sub_zero,
      Matrix.cons_val_zero]
    apply congrArg (pickBasis u v h)
    symm
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rfl

private noncomputable def pickAffineBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    AffineBasis (Fin 3) ℝ (Fin 2 → ℝ) :=
  let t : Affine.Simplex ℝ (Fin 2 → ℝ) 2 :=
    ⟨pickTrianglePoints u v h, pick_trianglePoints_affineIndependent u v h⟩
  AffineBasis.mk (pickTrianglePoints u v h) (pick_trianglePoints_affineIndependent u v h)
    (t.affineSpan_eq_top (by simp))

@[simp]
private theorem pick_affineBasis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 3) : pickAffineBasis u v h i = pickTrianglePoints u v h i := rfl

private theorem pick_affineBasis_basisOf_zero (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    ((pickAffineBasis u v h).basisOf 0).reindex
        (finSuccAboveEquiv (0 : Fin 3)).symm = pickBasis u v h := by
  ext i x
  fin_cases i <;>
    simp [Module.Basis.reindex_apply, pickTrianglePoints, finSuccAboveEquiv_apply,
      pick_basis_apply, pickVecs, pickCast]

private theorem pick_coord_eq_basisOf_repr (a : AffineBasis (Fin 3) ℝ (Fin 2 → ℝ))
    (ha0 : a 0 = 0) (j : {i : Fin 3 // i ≠ 0}) (x : Fin 2 → ℝ) :
    a.coord j x = (a.basisOf 0).repr x j := by
  let f : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
    ((Finsupp.lapply j).comp (a.basisOf 0).repr.toLinearMap).toAffineMap
  have hfa : f = a.coord j := by
    apply AffineMap.ext_on a.tot
    rintro _ ⟨i, rfl⟩
    rcases eq_or_ne i 0 with rfl | hi
    · calc
        f (a 0) = 0 := by simp [f, ha0]
        _ = a.coord (j : Fin 3) (a 0) := (a.coord_apply_ne j.property).symm
    · let q : {i : Fin 3 // i ≠ 0} := ⟨i, hi⟩
      change ((a.basisOf 0).repr (a i)) j = a.coord (j : Fin 3) (a i)
      have hb : a i = a.basisOf 0 q := by simp [q, ha0]
      conv_lhs => rw [hb, Module.Basis.repr_self]
      rw [a.coord_apply, Finsupp.single_apply]
      by_cases hq : q = j
      · have hji : (j : Fin 3) = i := congrArg Subtype.val hq.symm
        simp [hq, hji]
      · have hji : (j : Fin 3) ≠ i := by
          intro hij
          exact hq (Subtype.ext hij.symm)
        simp [hq, hji]
  rw [← hfa]
  rfl

private theorem pick_affineBasis_coord_succ (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) (x : Fin 2 → ℝ) :
    (pickAffineBasis u v h).coord (Fin.succ i) x = (pickBasis u v h).repr x i := by
  let e := finSuccAboveEquiv (0 : Fin 3)
  have he : (e i : Fin 3) = Fin.succ i := by simp [e, finSuccAboveEquiv_apply]
  rw [← he]
  calc
    (pickAffineBasis u v h).coord (e i) x =
        ((pickAffineBasis u v h).basisOf 0).repr x (e i) :=
      pick_coord_eq_basisOf_repr _ (by simp [pickTrianglePoints]) (e i) x
    _ = (((pickAffineBasis u v h).basisOf 0).reindex e.symm).repr x i := by
      simp [Module.Basis.repr_reindex]
    _ = (pickBasis u v h).repr x i := by rw [pick_affineBasis_basisOf_zero]

private noncomputable def pickTriangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Set (Fin 2 → ℝ) := convexHull ℝ (Set.range (pickAffineBasis u v h))

private theorem pick_mem_triangle_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) :
    x ∈ pickTriangle u v h ↔
      0 ≤ (pickBasis u v h).repr x 0 ∧
        0 ≤ (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 ≤ 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).convexHull_eq_nonneg_coord]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumle⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

private theorem pick_mem_interior_triangle_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ interior (pickTriangle u v h) ↔
      0 < (pickBasis u v h).repr x 0 ∧
        0 < (pickBasis u v h).repr x 1 ∧
          (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 < 1 := by
  rw [pickTriangle, (pickAffineBasis u v h).interior_convexHull]
  have hsum :
      (pickAffineBasis u v h).coord 0 x +
          ∑ i : Fin 2, (pickAffineBasis u v h).coord (Fin.succ i) x = 1 := by
    simpa only [Fin.sum_univ_succ] using (pickAffineBasis u v h).sum_coord_apply_eq_one x
  have hsum' :
      (pickAffineBasis u v h).coord 0 x + ∑ i : Fin 2, (pickBasis u v h).repr x i = 1 := by
    simpa only [pick_affineBasis_coord_succ] using hsum
  rw [Fin.sum_univ_two] at hsum'
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← pick_affineBasis_coord_succ u v h 0 x] using hx (Fin.succ 0)
    · simpa only [← pick_affineBasis_coord_succ u v h 1 x] using hx (Fin.succ 1)
    · linarith [hx 0]
  · rintro ⟨h0, h1, hsumlt⟩
    refine Fin.cases (by linarith) (fun i ↦ ?_)
    rw [pick_affineBasis_coord_succ]
    fin_cases i
    · exact h0
    · exact h1

private noncomputable def pickReflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  pickBasis u v h 0 + pickBasis u v h 1 - x

private theorem pick_repr_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) (i : Fin 2) :
    (pickBasis u v h).repr (pickReflect u v h x) i =
      1 - (pickBasis u v h).repr x i := by
  rw [pickReflect, map_sub, map_add, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

private theorem pick_reflect_cast (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickReflect u v h (pickCast z) = pickCast (u + v - z) := by
  ext i
  simp [pickReflect, pick_basis_apply, pickVecs, pickCast]

@[simp]
private theorem pick_reflect_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) : pickReflect u v h (pickReflect u v h x) = x := by
  simp [pickReflect]

private theorem pick_mem_reflect_image_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) :
    x ∈ pickReflect u v h '' pickTriangle u v h ↔ pickReflect u v h x ∈ pickTriangle u v h := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨pickReflect u v h x, hx, pick_reflect_reflect u v h x⟩

private theorem pick_mem_reflected_triangle_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ pickReflect u v h '' pickTriangle u v h ↔
      (pickBasis u v h).repr x 0 ≤ 1 ∧
        (pickBasis u v h).repr x 1 ≤ 1 ∧
          1 ≤ (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 := by
  rw [pick_mem_reflect_image_iff, pick_mem_triangle_iff,
    pick_repr_reflect, pick_repr_reflect]
  constructor <;> rintro ⟨h0, h1, hsum⟩ <;> constructor
  · linarith
  · constructor <;> linarith
  · linarith
  · constructor <;> linarith

private theorem pick_parallelepiped_eq_union (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    parallelepiped (pickBasis u v h) =
      pickTriangle u v h ∪ pickReflect u v h '' pickTriangle u v h := by
  rw [parallelepiped_basis_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1 := hx 1
    rcases le_total ((pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1) 1 with
      hsum | hsum
    · left
      exact (pick_mem_triangle_iff u v h x).2 ⟨hx0.1, hx1.1, hsum⟩
    · right
      exact (pick_mem_reflected_triangle_iff u v h x).2 ⟨hx0.2, hx1.2, hsum⟩
  · rintro (hx | hx) i
    · obtain ⟨h0, h1, hsum⟩ := (pick_mem_triangle_iff u v h x).1 hx
      fin_cases i
      · change 0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 ≤ 1
        constructor <;> linarith
      · change 0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 ≤ 1
        constructor <;> linarith
    · obtain ⟨h0, h1, hsum⟩ := (pick_mem_reflected_triangle_iff u v h x).1 hx
      fin_cases i
      · change 0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 ≤ 1
        constructor <;> linarith
      · change 0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 ≤ 1
        constructor <;> linarith

private noncomputable def pickDiagonal (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    AffineSubspace ℝ (Fin 2 → ℝ) :=
  AffineSubspace.mk' (pickBasis u v h 0) (LinearMap.ker (pickBasis u v h).sumCoords)

private theorem pick_mem_diagonal_iff (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (x : Fin 2 → ℝ) :
    x ∈ pickDiagonal u v h ↔
      (pickBasis u v h).repr x 0 + (pickBasis u v h).repr x 1 = 1 := by
  rw [pickDiagonal, AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub,
    Module.Basis.sumCoords_self_apply, sub_eq_zero]
  classical
  simp [Fin.sum_univ_two]

private theorem pick_diagonal_ne_top (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickDiagonal u v h ≠ ⊤ := by
  intro htop
  have hz : (0 : Fin 2 → ℝ) ∈ pickDiagonal u v h := by rw [htop]; trivial
  rw [pick_mem_diagonal_iff] at hz
  simp at hz

private theorem pick_triangle_inter_reflect_subset_diagonal (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h) ⊆ pickDiagonal u v h := by
  rintro x ⟨hx, hrx⟩
  obtain ⟨-, -, hle⟩ := (pick_mem_triangle_iff u v h x).1 hx
  obtain ⟨-, -, hge⟩ := (pick_mem_reflected_triangle_iff u v h x).1 hrx
  exact (pick_mem_diagonal_iff u v h x).2 (le_antisymm hle hge)

private theorem pick_volume_triangle_inter_reflect (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h ∩ (pickReflect u v h '' pickTriangle u v h)) = 0 := by
  exact MeasureTheory.measure_mono_null (pick_triangle_inter_reflect_subset_diagonal u v h)
    (volume.addHaar_affineSubspace (pickDiagonal u v h) (pick_diagonal_ne_top u v h))

private theorem pick_triangle_isCompact (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    IsCompact (pickTriangle u v h) := by
  exact (Set.finite_range (pickAffineBasis u v h)).isCompact_convexHull ℝ

private theorem pick_triangle_measurableSet (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    MeasurableSet (pickTriangle u v h) := (pick_triangle_isCompact u v h).isClosed.measurableSet

private theorem pick_measurePreserving_neg :
    MeasurePreserving (fun x : Fin 2 → ℝ ↦ -x) volume volume := by
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [Matrix.det_neg]
    norm_num
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := (-1 : Matrix (Fin 2) (Fin 2) ℝ)) (by simp [hdet])
  rw [hdet] at hmap
  norm_num at hmap
  refine ⟨measurable_neg, ?_⟩
  convert hmap using 1
  ext x i
  rfl

private theorem pick_measurePreserving_reflect (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    MeasurePreserving (pickReflect u v h) volume volume := by
  change MeasurePreserving
    ((fun x : Fin 2 → ℝ ↦ pickBasis u v h 0 + pickBasis u v h 1 + x) ∘ fun x ↦ -x)
      volume volume
  exact (measurePreserving_add_left volume (pickBasis u v h 0 + pickBasis u v h 1)).comp
    pick_measurePreserving_neg

private theorem pick_reflect_image_eq_preimage (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickReflect u v h '' pickTriangle u v h = pickReflect u v h ⁻¹' pickTriangle u v h := by
  ext x
  exact pick_mem_reflect_image_iff u v h x

private theorem pick_reflected_triangle_measurableSet (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : MeasurableSet (pickReflect u v h '' pickTriangle u v h) := by
  rw [pick_reflect_image_eq_preimage]
  exact (pick_triangle_measurableSet u v h).preimage
    (pick_measurePreserving_reflect u v h).measurable

private theorem pick_volume_reflected_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    volume (pickReflect u v h '' pickTriangle u v h) = volume (pickTriangle u v h) := by
  rw [pick_reflect_image_eq_preimage]
  exact (pick_measurePreserving_reflect u v h).measure_preimage
    (pick_triangle_measurableSet u v h).nullMeasurableSet

private theorem pick_two_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
      ENNReal.ofReal |(pickDet u v : ℝ)| := by
  calc
    volume (pickTriangle u v h) + volume (pickTriangle u v h) =
        volume (pickTriangle u v h) +
          volume (pickReflect u v h '' pickTriangle u v h) := by
      rw [pick_volume_reflected_triangle]
    _ = volume (pickTriangle u v h ∪ pickReflect u v h '' pickTriangle u v h) := by
      have hunion := measure_union_add_inter (μ := volume) (pickTriangle u v h)
        (pick_reflected_triangle_measurableSet u v h)
      rw [pick_volume_triangle_inter_reflect, add_zero] at hunion
      exact hunion.symm
    _ = volume (parallelepiped (pickBasis u v h)) := by
      rw [pick_parallelepiped_eq_union]
    _ = volume (ZSpan.fundamentalDomain (pickBasis u v h)) := by
      exact (ZSpan.fundamentalDomain_ae_parallelepiped (pickBasis u v h) volume).measure_eq.symm
    _ = ENNReal.ofReal |(pickDet u v : ℝ)| := by
      rw [ZSpan.volume_fundamentalDomain, pick_matrix_of_basis, pick_matrix_det]

private theorem pick_volume_triangle (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (volume (pickTriangle u v h)).toReal = |(pickDet u v : ℝ)| / 2 := by
  have hfinite : volume (pickTriangle u v h) ≠ ⊤ :=
    ne_of_lt (pick_triangle_isCompact u v h).measure_lt_top
  have hre := congrArg ENNReal.toReal (pick_two_volume_triangle u v h)
  rw [ENNReal.toReal_add hfinite hfinite, ENNReal.toReal_ofReal (abs_nonneg _)] at hre
  linarith

private def pickIntMatrix (u v : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Matrix.of ![u, v]

private theorem pick_intMatrix_det (u v : Fin 2 → ℤ) :
    (pickIntMatrix u v).det = pickDet u v := by
  simp [pickIntMatrix, pickDet, Matrix.det_fin_two]

private def pickIntMap (u v : Fin 2 → ℤ) : (Fin 2 → ℤ) →ₗ[ℤ] Fin 2 → ℤ :=
  Matrix.toLin' (pickIntMatrix u v).transpose

private theorem pick_intMap_injective (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Function.Injective (pickIntMap u v) := by
  apply Matrix.mulVec_injective_of_det_ne_zero
  rw [Matrix.det_transpose, pick_intMatrix_det]
  exact h

private def pickSublattice (u v : Fin 2 → ℤ) : AddSubgroup (Fin 2 → ℤ) :=
  (pickIntMap u v).toAddMonoidHom.range

private noncomputable def pickSublatticeBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℤ (pickSublattice u v) :=
  let g : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) := (pickIntMap u v).toAddMonoidHom
  let f : (Fin 2 → ℤ) →+ pickSublattice u v := g.rangeRestrict
  let e : (Fin 2 → ℤ) ≃+ pickSublattice u v := AddEquiv.ofBijective f ⟨by
    intro x y hxy
    exact pick_intMap_injective u v h (congrArg Subtype.val hxy), g.rangeRestrict_surjective⟩
  (Pi.basisFun ℤ (Fin 2)).map e.toIntLinearEquiv

private theorem pick_intMap_basisFun (u v : Fin 2 → ℤ) (i : Fin 2) :
    pickIntMap u v ((Pi.basisFun ℤ (Fin 2)) i) = ![u, v] i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [pickIntMap, pickIntMatrix, Matrix.toLin'_apply, Pi.basisFun_apply]

private theorem pick_sublatticeBasis_apply (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) : (pickSublatticeBasis u v h i : Fin 2 → ℤ) = ![u, v] i := by
  rw [pickSublatticeBasis, Module.Basis.map_apply]
  change pickIntMap u v ((Pi.basisFun ℤ (Fin 2)) i) = ![u, v] i
  rw [pick_intMap_basisFun]

private theorem pick_sublattice_index (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickSublattice u v).index = (pickDet u v).natAbs := by
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) (pickSublattice u v)
    (pickSublatticeBasis u v h), Module.Basis.det_apply]
  have hmatrix :
      (Pi.basisFun ℤ (Fin 2)).toMatrix
          (fun i ↦ (pickSublatticeBasis u v h i : Fin 2 → ℤ)) =
        (pickIntMatrix u v).transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, pick_sublatticeBasis_apply, pickIntMatrix]
  rw [hmatrix, Matrix.det_transpose, pick_intMatrix_det]

private theorem pick_repr_cast_intMap (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) :
    (pickBasis u v h).repr (pickCast (pickIntMap u v c)) i = (c i : ℝ) := by
  have hcast :
      pickCast (pickIntMap u v c) =
        (c 0 : ℝ) • pickBasis u v h 0 + (c 1 : ℝ) • pickBasis u v h 1 := by
    ext j
    fin_cases j <;>
      simp [pickIntMap, pickIntMatrix, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, pickCast, pick_basis_apply, pickVecs] <;> ring
  rw [hcast, map_add, map_smul, map_smul, Module.Basis.repr_self,
    Module.Basis.repr_self]
  fin_cases i <;> simp

private noncomputable def pickFloorCoeffs (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 2 → ℤ := fun i ↦ ⌊(pickBasis u v h).repr (pickCast z) i⌋

private noncomputable def pickFractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Fin 2 → ℤ := z - pickIntMap u v (pickFloorCoeffs u v z h)

private theorem pick_repr_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (i : Fin 2) :
    (pickBasis u v h).repr (pickCast (pickFractInt u v z h)) i =
      Int.fract ((pickBasis u v h).repr (pickCast z) i) := by
  have hcast :
      pickCast (pickFractInt u v z h) =
        pickCast z - pickCast (pickIntMap u v (pickFloorCoeffs u v z h)) := by
    ext j
    simp [pickFractInt, pickCast]
  rw [hcast, map_sub, Finsupp.coe_sub, Pi.sub_apply, pick_repr_cast_intMap]
  rfl

private theorem pick_fractInt_mem_fundamentalDomain (u v z : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) ∈ ZSpan.fundamentalDomain (pickBasis u v h) := by
  rw [ZSpan.mem_fundamentalDomain]
  intro i
  rw [pick_repr_cast_fractInt]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

private theorem pick_cast_fractInt (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickFractInt u v z h) = ZSpan.fract (pickBasis u v h) (pickCast z) := by
  apply (pickBasis u v h).ext_elem
  intro i
  rw [pick_repr_cast_fractInt, ZSpan.repr_fract_apply]

private theorem pick_cast_intMap_mem_zspan (u v c : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickCast (pickIntMap u v c) ∈ Submodule.span ℤ (Set.range (pickBasis u v h)) := by
  rw [(pickBasis u v h).mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨c i, (pick_repr_cast_intMap u v c h i).symm⟩

private theorem pick_fractInt_eq_of_rel (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    {z z' : Fin 2 → ℤ} (hrel : QuotientAddGroup.leftRel (pickSublattice u v) z z') :
    pickFractInt u v z h = pickFractInt u v z' h := by
  apply pick_cast_injective
  rw [pick_cast_fractInt, pick_cast_fractInt]
  apply (ZSpan.fract_eq_fract (pickBasis u v h) (pickCast z) (pickCast z')).2
  have hs : -z + z' ∈ pickSublattice u v := QuotientAddGroup.leftRel_apply.mp hrel
  rcases hs with ⟨c, hc⟩
  have hcast : -pickCast z + pickCast z' = pickCast (pickIntMap u v c) := by
    change -pickCast z + pickCast z' = pickCast ((pickIntMap u v).toAddMonoidHom c)
    rw [hc]
    ext i
    simp [pickCast]
  rw [hcast]
  exact pick_cast_intMap_mem_zspan u v c h

private noncomputable def pickFundamentalLatticePoints (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : Set (Fin 2 → ℤ) :=
  {z | pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)}

private noncomputable def pickQuotientToFundamental (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) → pickFundamentalLatticePoints u v h := fun q ↦
  Quotient.liftOn q
    (fun z ↦ ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩)
    (fun _ _ hrel ↦ Subtype.ext (pick_fractInt_eq_of_rel u v h hrel))

@[simp]
private theorem pick_quotientToFundamental_mk (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickQuotientToFundamental u v h (QuotientAddGroup.mk z) =
      ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩ := rfl

private theorem pick_quotient_fractInt_eq (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (QuotientAddGroup.mk (pickFractInt u v z h) : (Fin 2 → ℤ) ⧸ pickSublattice u v) =
      QuotientAddGroup.mk z := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hm : pickIntMap u v (pickFloorCoeffs u v z h) ∈ pickSublattice u v :=
    ⟨pickFloorCoeffs u v z h, rfl⟩
  convert (pickSublattice u v).neg_mem hm using 1
  simp [pickFractInt]

private theorem pick_fractInt_eq_self_of_mem (u v z : Fin 2 → ℤ) (h : pickDet u v ≠ 0)
    (hz : pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)) :
    pickFractInt u v z h = z := by
  apply pick_cast_injective
  rw [pick_cast_fractInt]
  exact ZSpan.fract_eq_self.mpr hz

private theorem pick_quotientToFundamental_bijective (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : Function.Bijective (pickQuotientToFundamental u v h) := by
  constructor
  · intro q q' hq
    induction q using Quotient.inductionOn with
    | _ z =>
      induction q' using Quotient.inductionOn with
      | _ z' =>
        have hval : pickFractInt u v z h = pickFractInt u v z' h :=
          congrArg Subtype.val hq
        calc
          QuotientAddGroup.mk z = QuotientAddGroup.mk (pickFractInt u v z h) :=
            (pick_quotient_fractInt_eq u v z h).symm
          _ = QuotientAddGroup.mk (pickFractInt u v z' h) := congrArg QuotientAddGroup.mk hval
          _ = QuotientAddGroup.mk z' := pick_quotient_fractInt_eq u v z' h
  · rintro ⟨z, hz⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    apply Subtype.ext
    exact pick_fractInt_eq_self_of_mem u v z h hz

private noncomputable def pickQuotientFundamentalEquiv (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) ≃ pickFundamentalLatticePoints u v h :=
  Equiv.ofBijective (pickQuotientToFundamental u v h)
    (pick_quotientToFundamental_bijective u v h)

private theorem pick_fundamentalLatticePoints_ncard (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    (pickFundamentalLatticePoints u v h).ncard = (pickDet u v).natAbs := by
  calc
    (pickFundamentalLatticePoints u v h).ncard =
        Nat.card (pickFundamentalLatticePoints u v h) := by
      rw [← Set.ncard_coe, Set.ncard_univ]
    _ = Nat.card ((Fin 2 → ℤ) ⧸ pickSublattice u v) :=
      (Nat.card_congr (pickQuotientFundamentalEquiv u v h)).symm
    _ = (pickSublattice u v).index := (pickSublattice u v).index_eq_card.symm
    _ = (pickDet u v).natAbs := pick_sublattice_index u v h

private abbrev pickLatticePoints (K : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℤ) :=
  pickCast ⁻¹' K

private theorem pick_fundamentalLatticePoints_finite (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : (pickFundamentalLatticePoints u v h).Finite := by
  apply (pick_lattice_preimage_finite (pickBasis u v h).parallelepiped.isCompact).subset
  intro z hz
  exact ZSpan.fundamentalDomain_subset_parallelepiped (pickBasis u v h) hz

private theorem pick_triangleLatticePoints_finite (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : (pickLatticePoints (pickTriangle u v h)).Finite :=
  pick_lattice_preimage_finite (pick_triangle_isCompact u v h)

private theorem pick_mem_fundamentalDomain_iff (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) (x : Fin 2 → ℝ) :
    x ∈ ZSpan.fundamentalDomain (pickBasis u v h) ↔
      0 ≤ (pickBasis u v h).repr x 0 ∧ (pickBasis u v h).repr x 0 < 1 ∧
        0 ≤ (pickBasis u v h).repr x 1 ∧ (pickBasis u v h).repr x 1 < 1 := by
  rw [ZSpan.mem_fundamentalDomain]
  constructor
  · intro hx
    exact ⟨(hx 0).1, (hx 0).2, (hx 1).1, (hx 1).2⟩
  · rintro ⟨h00, h01, h10, h11⟩ i
    fin_cases i
    · exact ⟨h00, h01⟩
    · exact ⟨h10, h11⟩

private theorem pick_repr_cast_u (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast u) = Finsupp.single 0 1 := by
  have hu : pickBasis u v h 0 = pickCast u := by
    simp [pick_basis_apply, pickVecs]
  rw [← hu, Module.Basis.repr_self]

private theorem pick_repr_cast_v (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickBasis u v h).repr (pickCast v) = Finsupp.single 1 1 := by
  have hv : pickBasis u v h 1 = pickCast v := by
    simp [pick_basis_apply, pickVecs]
  rw [← hv, Module.Basis.repr_self]

private theorem pick_u_ne_v (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) : u ≠ v := by
  intro huv
  apply h
  rw [huv]
  simp [pickDet, mul_comm]

private theorem pick_fundamental_inter_triangle (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    pickFundamentalLatticePoints u v h ∩ pickLatticePoints (pickTriangle u v h) =
      pickLatticePoints (pickTriangle u v h) \ {u, v} := by
  ext z
  constructor
  · rintro ⟨hzD, hzT⟩
    refine ⟨hzT, ?_⟩
    rintro (hzu | hzv)
    · have hcoord := (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
      rw [hzu, pick_repr_cast_u] at hcoord
      norm_num at hcoord
    · rw [Set.mem_singleton_iff] at hzv
      have hcoord := (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
      rw [hzv, pick_repr_cast_v] at hcoord
      norm_num at hcoord
  · rintro ⟨hzT, hzuv⟩
    obtain ⟨h0, h1, hsum⟩ := (pick_mem_triangle_iff u v h (pickCast z)).1 hzT
    have hzu : z ≠ u := fun hzu ↦ hzuv (by simp [hzu])
    have hzv : z ≠ v := fun hzv ↦ hzuv (by simp [hzv])
    have h0lt : (pickBasis u v h).repr (pickCast z) 0 < 1 := by
      apply lt_of_le_of_ne (by linarith)
      intro h0eq
      have h1eq : (pickBasis u v h).repr (pickCast z) 1 = 0 := by linarith
      apply hzu
      apply pick_cast_injective
      apply (pickBasis u v h).repr.injective
      rw [pick_repr_cast_u]
      ext i
      fin_cases i <;> simp [h0eq, h1eq]
    have h1lt : (pickBasis u v h).repr (pickCast z) 1 < 1 := by
      apply lt_of_le_of_ne (by linarith)
      intro h1eq
      have h0eq : (pickBasis u v h).repr (pickCast z) 0 = 0 := by linarith
      apply hzv
      apply pick_cast_injective
      apply (pickBasis u v h).repr.injective
      rw [pick_repr_cast_v]
      ext i
      fin_cases i <;> simp [h0eq, h1eq]
    exact ⟨(pick_mem_fundamentalDomain_iff u v h (pickCast z)).2
      ⟨h0, h0lt, h1, h1lt⟩, hzT⟩

private def pickIntReflect (u v z : Fin 2 → ℤ) : Fin 2 → ℤ := u + v - z

@[simp]
private theorem pick_intReflect_involutive (u v z : Fin 2 → ℤ) :
    pickIntReflect u v (pickIntReflect u v z) = z := by
  simp [pickIntReflect]

private theorem pick_intReflect_mem_interior_iff (u v z : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    z ∈ pickFundamentalLatticePoints u v h \ pickLatticePoints (pickTriangle u v h) ↔
      pickIntReflect u v z ∈ pickLatticePoints (interior (pickTriangle u v h)) := by
  let a := (pickBasis u v h).repr (pickCast z) 0
  let b := (pickBasis u v h).repr (pickCast z) 1
  have hreflect : pickCast (pickIntReflect u v z) = pickReflect u v h (pickCast z) := by
    exact (pick_reflect_cast u v z h).symm
  constructor
  · rintro ⟨hzD, hzT⟩
    obtain ⟨ha0, ha1, hb0, hb1⟩ :=
      (pick_mem_fundamentalDomain_iff u v h (pickCast z)).1 hzD
    have hab : 1 < a + b := by
      apply lt_of_not_ge
      intro hab
      exact hzT ((pick_mem_triangle_iff u v h (pickCast z)).2 ⟨ha0, hb0, hab⟩)
    change pickCast (pickIntReflect u v z) ∈ interior (pickTriangle u v h)
    rw [hreflect, pick_mem_interior_triangle_iff, pick_repr_reflect, pick_repr_reflect]
    exact ⟨by linarith, by linarith, by dsimp only [a, b] at hab ⊢; linarith⟩
  · intro hzI
    change pickCast (pickIntReflect u v z) ∈ interior (pickTriangle u v h) at hzI
    rw [hreflect, pick_mem_interior_triangle_iff, pick_repr_reflect,
      pick_repr_reflect] at hzI
    obtain ⟨ha, hb, hab⟩ := hzI
    have ha0 : 0 ≤ a := by dsimp only [a] at ha ⊢; linarith
    have ha1 : a < 1 := by dsimp only [a] at ha ⊢; linarith
    have hb0 : 0 ≤ b := by dsimp only [b] at hb ⊢; linarith
    have hb1 : b < 1 := by dsimp only [b] at hb ⊢; linarith
    have hab' : 1 < a + b := by dsimp only [a, b] at hab ⊢; linarith
    refine ⟨(pick_mem_fundamentalDomain_iff u v h (pickCast z)).2
      ⟨ha0, ha1, hb0, hb1⟩, ?_⟩
    intro hzT
    have hsum := ((pick_mem_triangle_iff u v h (pickCast z)).1 hzT).2.2
    dsimp only [a, b] at hab'
    linarith

private theorem pick_intReflect_bijOn (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Set.BijOn (pickIntReflect u v)
      (pickFundamentalLatticePoints u v h \ pickLatticePoints (pickTriangle u v h))
      (pickLatticePoints (interior (pickTriangle u v h))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (pick_intReflect_mem_interior_iff u v z h).1 hz
  · intro z _ z' _ hzz'
    have := congrArg (pickIntReflect u v) hzz'
    simpa using this
  · intro z hz
    refine ⟨pickIntReflect u v z, ?_, by simp⟩
    apply (pick_intReflect_mem_interior_iff u v (pickIntReflect u v z) h).2
    simpa using hz

private theorem pick_triangle_lattice_count (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    (pickDet u v).natAbs + 2 =
      2 * (pickLatticePoints (interior (pickTriangle u v h))).ncard +
        (pickLatticePoints (frontier (pickTriangle u v h))).ncard := by
  let F := pickFundamentalLatticePoints u v h
  let L := pickLatticePoints (pickTriangle u v h)
  let I := pickLatticePoints (interior (pickTriangle u v h))
  let B := pickLatticePoints (frontier (pickTriangle u v h))
  have hF : F.Finite := pick_fundamentalLatticePoints_finite u v h
  have hL : L.Finite := pick_triangleLatticePoints_finite u v h
  have hI : I.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ pickTriangle u v h
    exact interior_subset hz
  have hB : B.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ pickTriangle u v h
    exact (pick_triangle_isCompact u v h).isClosed.frontier_subset hz
  have hsplitDisjoint : Disjoint (F ∩ L) (F \ L) := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hy.2 hx.2
  have hsplit : F.ncard = (F ∩ L).ncard + (F \ L).ncard := by
    calc
      F.ncard = ((F ∩ L) ∪ (F \ L)).ncard := by rw [Set.inter_union_sdiff]
      _ = (F ∩ L).ncard + (F \ L).ncard :=
        Set.ncard_union_eq hsplitDisjoint (hF.inter_of_left L) hF.sdiff
  have hreflect : (F \ L).ncard = I.ncard := by
    exact (pick_intReflect_bijOn u v h).ncard_eq
  have huL : u ∈ L := by
    change pickCast u ∈ pickTriangle u v h
    rw [pick_mem_triangle_iff, pick_repr_cast_u]
    norm_num
  have hvL : v ∈ L := by
    change pickCast v ∈ pickTriangle u v h
    rw [pick_mem_triangle_iff, pick_repr_cast_v]
    norm_num
  have huvL : {u, v} ⊆ L := by
    rintro z (rfl | hz)
    · exact huL
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hvL
  have hinter : (F ∩ L).ncard + 2 = L.ncard := by
    rw [pick_fundamental_inter_triangle u v h]
    calc
      (L \ {u, v}).ncard + 2 =
          (L \ {u, v}).ncard + ({u, v} : Set (Fin 2 → ℤ)).ncard := by
        rw [Set.ncard_pair (pick_u_ne_v u v h)]
      _ = L.ncard := Set.ncard_sdiff_add_ncard_of_subset huvL hL
  have hdecomp : L = I ∪ B := by
    change pickCast ⁻¹' pickTriangle u v h =
      pickCast ⁻¹' interior (pickTriangle u v h) ∪
        pickCast ⁻¹' frontier (pickTriangle u v h)
    rw [← Set.preimage_union]
    congr 1
    calc
      pickTriangle u v h = closure (pickTriangle u v h) :=
        (pick_triangle_isCompact u v h).isClosed.closure_eq.symm
      _ = interior (pickTriangle u v h) ∪ frontier (pickTriangle u v h) :=
        closure_eq_interior_union_frontier _
  have hIBdisjoint : Disjoint I B := by
    rw [Set.disjoint_left]
    intro z hzI hzB
    exact Set.disjoint_left.mp disjoint_interior_frontier hzI hzB
  have hLB : L.ncard = I.ncard + B.ncard := by
    rw [hdecomp, Set.ncard_union_eq hIBdisjoint hI hB]
  have hFcard : F.ncard = (pickDet u v).natAbs :=
    pick_fundamentalLatticePoints_ncard u v h
  dsimp only [F, L, I, B] at hsplit hreflect hinter hLB hFcard ⊢
  omega

private theorem pick_triangle_eq_explicit (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    pickTriangle u v h = convexHull ℝ ({0, pickCast u, pickCast v} : Set (Fin 2 → ℝ)) := by
  unfold pickTriangle
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rw [pick_affineBasis_apply]
    fin_cases i <;> simp [pickTrianglePoints, pick_basis_apply, pickVecs]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [pickTrianglePoints]⟩
    · refine ⟨1, ?_⟩
      simp [pickTrianglePoints, pick_basis_apply, pickVecs]
    · refine ⟨2, ?_⟩
      simp [pickTrianglePoints, pick_basis_apply, pickVecs]

/-- **Pick's theorem for lattice triangles with a vertex at the origin.** Let
$u, v \in \mathbb{Z}^2$ with $u_0 v_1 - u_1 v_0 \neq 0$, and let $T \subset \mathbb{R}^2$ be
the convex hull of $0$, $u$ and $v$. Let $I$ be the number of points of $\mathbb{Z}^2$ in the
interior of $T$ and $B$ the number of points of $\mathbb{Z}^2$ on the boundary of $T$. Then
the area (two-dimensional Lebesgue measure) of $T$ equals $I + B/2 - 1$. -/
theorem _root_.MeasureTheory.toReal_volume_convexHull_lattice_triangle (u v : Fin 2 → ℤ)
    (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    (volume (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
      Set (Fin 2 → ℝ)))).toReal =
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        interior (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
          Set (Fin 2 → ℝ)))} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        frontier (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
          Set (Fin 2 → ℝ)))} : ℝ) / 2 - 1 := by
  have hdet : pickDet u v ≠ 0 := h
  rw [← pick_triangle_eq_explicit u v hdet]
  have hcount := pick_triangle_lattice_count u v hdet
  rw [pick_volume_triangle u v hdet]
  have habs : |(pickDet u v : ℝ)| = ((pickDet u v).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  have hcountR := congrArg (fun n : ℕ ↦ (n : ℝ)) hcount
  push_cast at hcountR
  change ((pickDet u v).natAbs : ℝ) + 2 =
    2 * (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
      interior (pickTriangle u v hdet)} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
        frontier (pickTriangle u v hdet)} : ℝ) at hcountR
  change ((pickDet u v).natAbs : ℝ) / 2 =
    (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
      interior (pickTriangle u v hdet)} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | pickCast z ∈
        frontier (pickTriangle u v hdet)} : ℝ) / 2 - 1
  linarith

private noncomputable def pickNormal (a c : Fin 2 → ℝ) :
    StrongDual ℝ (Fin 2 → ℝ) :=
  (c 0 - a 0) • ContinuousLinearMap.proj 1 -
    (c 1 - a 1) • ContinuousLinearMap.proj 0

private noncomputable def pickSide (a c x : Fin 2 → ℝ) : ℝ :=
  pickNormal a c x - pickNormal a c a

private theorem pick_side_apply (a c x : Fin 2 → ℝ) :
    pickSide a c x =
      (c 0 - a 0) * (x 1 - a 1) - (c 1 - a 1) * (x 0 - a 0) := by
  simp [pickSide, pickNormal]
  ring

private theorem pick_normal_ne_zero {a c : Fin 2 → ℝ} (hac : a ≠ c) :
    pickNormal a c ≠ 0 := by
  intro hzero
  have h0 := DFunLike.congr_fun hzero ![0, 1]
  have h1 := DFunLike.congr_fun hzero ![1, 0]
  simp [pickNormal] at h0 h1
  apply hac
  funext i
  fin_cases i
  · change a 0 = c 0
    linarith
  · change a 1 = c 1
    linarith

private theorem pick_side_eq_zero_iff_mem_line {a c : Fin 2 → ℝ} (hac : a ≠ c)
    (x : Fin 2 → ℝ) : pickSide a c x = 0 ↔ x ∈ line[ℝ, a, c] := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · intro hx
    rw [pick_side_apply] at hx
    by_cases h0 : c 0 - a 0 ≠ 0
    · refine ⟨(x 0 - a 0) / (c 0 - a 0), ?_⟩
      ext i
      fin_cases i
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 0 - a 0) / (c 0 - a 0) * (c 0 - a 0) + a 0 = x 0
        field_simp [h0]
        ring
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 0 - a 0) / (c 0 - a 0) * (c 1 - a 1) + a 1 = x 1
        field_simp [h0]
        nlinarith
    · have h1 : c 1 - a 1 ≠ 0 := by
        intro h1
        apply hac
        funext i
        fin_cases i
        · change a 0 = c 0
          exact sub_eq_zero.mp (not_ne_iff.mp h0) |>.symm
        · change a 1 = c 1
          exact sub_eq_zero.mp h1 |>.symm
      have h0eq : c 0 - a 0 = 0 := not_ne_iff.mp h0
      refine ⟨(x 1 - a 1) / (c 1 - a 1), ?_⟩
      ext i
      fin_cases i
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 1 - a 1) / (c 1 - a 1) * (c 0 - a 0) + a 0 = x 0
        simp only [h0eq, zero_mul, zero_sub, neg_eq_zero] at hx
        have hx0 : x 0 - a 0 = 0 := (mul_eq_zero.mp hx).resolve_left h1
        rw [h0eq, mul_zero, zero_add]
        nlinarith
      · rw [AffineMap.lineMap_apply_module']
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        change (x 1 - a 1) / (c 1 - a 1) * (c 1 - a 1) + a 1 = x 1
        field_simp [h1]
        ring
  · rintro ⟨r, rfl⟩
    rw [pick_side_apply, AffineMap.lineMap_apply_module']
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

private noncomputable def pickHalfPlus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Ici (pickNormal a c a)

private noncomputable def pickHalfMinus (a c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  pickNormal a c ⁻¹' Set.Iic (pickNormal a c a)

private theorem pick_mem_halfPlus_iff (a c x : Fin 2 → ℝ) :
    x ∈ pickHalfPlus a c ↔ 0 ≤ pickSide a c x := by
  simp [pickHalfPlus, pickSide]

private theorem pick_mem_halfMinus_iff (a c x : Fin 2 → ℝ) :
    x ∈ pickHalfMinus a c ↔ pickSide a c x ≤ 0 := by
  simp [pickHalfMinus, pickSide]

private theorem pick_halfPlus_convex (a c : Fin 2 → ℝ) : Convex ℝ (pickHalfPlus a c) := by
  exact convex_halfSpace_ge (pickNormal a c).toLinearMap.isLinear _

private theorem pick_halfPlus_isClosed (a c : Fin 2 → ℝ) : IsClosed (pickHalfPlus a c) :=
  isClosed_Ici.preimage (pickNormal a c).continuous

private theorem pick_halfMinus_isClosed (a c : Fin 2 → ℝ) : IsClosed (pickHalfMinus a c) :=
  isClosed_Iic.preimage (pickNormal a c).continuous

private theorem pick_interior_halfPlus {a c : Fin 2 → ℝ} (hac : a ≠ c) :
    interior (pickHalfPlus a c) = {x | pickNormal a c a < pickNormal a c x} := by
  rw [pickHalfPlus, ← (pickNormal a c).isOpenMap_of_ne_zero
    (pick_normal_ne_zero hac) |>.preimage_interior_eq_interior_preimage
      (pickNormal a c).continuous, interior_Ici]
  rfl

private theorem pick_interior_halfMinus {a c : Fin 2 → ℝ} (hac : a ≠ c) :
    interior (pickHalfMinus a c) = {x | pickNormal a c x < pickNormal a c a} := by
  rw [pickHalfMinus, ← (pickNormal a c).isOpenMap_of_ne_zero
    (pick_normal_ne_zero hac) |>.preimage_interior_eq_interior_preimage
      (pickNormal a c).continuous, interior_Iic]
  rfl

private theorem pick_half_inter_eq_line {a c : Fin 2 → ℝ} (hac : a ≠ c) :
    pickHalfPlus a c ∩ pickHalfMinus a c = (line[ℝ, a, c] : Set (Fin 2 → ℝ)) := by
  ext x
  rw [Set.mem_inter_iff, pick_mem_halfPlus_iff, pick_mem_halfMinus_iff]
  constructor
  · rintro ⟨hpos, hneg⟩
    exact (pick_side_eq_zero_iff_mem_line hac x).1 (le_antisymm hneg hpos)
  · intro hx
    have hz := (pick_side_eq_zero_iff_mem_line hac x).2 hx
    rw [hz]
    exact ⟨le_rfl, le_rfl⟩

private theorem pick_line_ne_top {a c : Fin 2 → ℝ} (hac : a ≠ c) : line[ℝ, a, c] ≠ ⊤ := by
  intro htop
  have hall : ∀ x : Fin 2 → ℝ, pickSide a c x = 0 := by
    intro x
    apply (pick_side_eq_zero_iff_mem_line hac x).2
    rw [htop]
    trivial
  have ha : pickNormal a c a = 0 := by
    have := hall 0
    simp [pickSide] at this
    linarith
  apply pick_normal_ne_zero hac
  ext x
  have hx := hall x
  change pickNormal a c x = 0
  change pickNormal a c x - pickNormal a c a = 0 at hx
  rw [ha, sub_zero] at hx
  exact hx

private theorem pick_inter_line_eq_segment {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    {a c : Fin 2 → ℝ} (hac : a ≠ c) (ha : a ∈ P.extremePoints ℝ)
    (hc : c ∈ P.extremePoints ℝ) :
    P ∩ (line[ℝ, a, c] : Set (Fin 2 → ℝ)) = segment ℝ a c := by
  ext x
  constructor
  · rintro ⟨hxP, hxline⟩
    have hcol : Collinear ℝ ({a, x, c} : Set (Fin 2 → ℝ)) := by
      have h := collinear_insert_of_mem_affineSpan_pair hxline
      have hset : ({x, a, c} : Set (Fin 2 → ℝ)) = {a, x, c} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [← hset]
      exact h
    rcases hcol.wbtw_or_wbtw_or_wbtw with haxc | hxca | hcax
    · exact haxc.mem_segment
    · rcases (mem_extremePoints_iff_forall_segment.mp hc).2 x hxP a ha.1 hxca.mem_segment
        with hxc | hac'
      · rw [hxc]
        exact right_mem_segment ℝ a c
      · exact (hac hac').elim
    · rcases (mem_extremePoints_iff_forall_segment.mp ha).2 c hc.1 x hxP hcax.mem_segment
        with hca | hxa
      · exact (hac hca.symm).elim
      · rw [hxa]
        exact left_mem_segment ℝ a c
  · intro hx
    refine ⟨hP.segment_subset ha.1 hc.1 hx, ?_⟩
    rw [← affineSegment_eq_segment ℝ] at hx
    exact affineSegment_subset_affineSpan ℝ a c hx

private theorem pick_map_eq_of_mem_openSegment_of_eq (f : StrongDual ℝ (Fin 2 → ℝ))
    {p q x : Fin 2 → ℝ} {r : ℝ} (hx : x ∈ openSegment ℝ p q)
    (hp : f p = r) (hq : f q = r) : f x = r := by
  rcases hx with ⟨s, t, hs, ht, hst, rfl⟩
  rw [map_add, map_smul, map_smul, hp, hq]
  simp only [smul_eq_mul]
  rw [← add_mul, hst, one_mul]

private theorem pick_endpoint_eq_of_openSegment_max (f : StrongDual ℝ (Fin 2 → ℝ))
    {p q x : Fin 2 → ℝ} (hx : x ∈ openSegment ℝ p q)
    (hp : f p ≤ f x) (hq : f q ≤ f x) : f p = f x ∧ f q = f x := by
  rcases hx with ⟨s, t, hs, ht, hst, hxeq⟩
  have hmap := congrArg f hxeq
  rw [map_add, map_smul, map_smul] at hmap
  simp only [smul_eq_mul] at hmap
  have hsum : s * f x + t * f x = f x := by
    rw [← add_mul, hst, one_mul]
  constructor
  · apply le_antisymm hp
    apply le_of_not_gt
    intro hlt
    have hslt : s * f p < s * f x := mul_lt_mul_of_pos_left hlt hs
    have htle : t * f q ≤ t * f x := mul_le_mul_of_nonneg_left hq ht.le
    have := add_lt_add_of_lt_of_le hslt htle
    rw [hmap, hsum] at this
    exact (lt_irrefl _ this)
  · apply le_antisymm hq
    apply le_of_not_gt
    intro hlt
    have hsle : s * f p ≤ s * f x := mul_le_mul_of_nonneg_left hp hs.le
    have htlt : t * f q < t * f x := mul_lt_mul_of_pos_left hlt ht
    have := add_lt_add_of_le_of_lt hsle htlt
    rw [hmap, hsum] at this
    exact (lt_irrefl _ this)

private theorem pick_continuousLinearMap_apply_coordinates
    (f : StrongDual ℝ (Fin 2 → ℝ)) (x : Fin 2 → ℝ) :
    f x = x 0 * f ![1, 0] + x 1 * f ![0, 1] := by
  have hx : x = x 0 • ![1, 0] + x 1 • ![0, 1] := by
    funext i
    fin_cases i <;> simp
  calc
    f x = f (x 0 • ![1, 0] + x 1 • ![0, 1]) := congrArg f hx
    _ = x 0 * f ![1, 0] + x 1 * f ![0, 1] := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]

private theorem pick_openSegment_subset_interior {P : Set (Fin 2 → ℝ)}
    (hP : Convex ℝ P) (hPint : (interior P).Nonempty) {a b c d y : Fin 2 → ℝ}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P) (hac : a ≠ c)
    (hyac : y ∈ openSegment ℝ a c) (hybd : y ∈ openSegment ℝ b d)
    (hbline : b ∉ line[ℝ, a, c]) : openSegment ℝ a c ⊆ interior P := by
  intro x hx
  by_contra hxint
  obtain ⟨f, hfne, hmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hP hxint hPint
  obtain ⟨hfa, hfc⟩ :=
    pick_endpoint_eq_of_openSegment_max f hx (hmax a ha) (hmax c hc)
  have hfy : f y = f x := pick_map_eq_of_mem_openSegment_of_eq f hyac hfa hfc
  have hfb_le : f b ≤ f y := by rw [hfy]; exact hmax b hb
  have hfd_le : f d ≤ f y := by rw [hfy]; exact hmax d hd
  obtain ⟨hfb, -⟩ := pick_endpoint_eq_of_openSegment_max f hybd hfb_le hfd_le
  have hw : f (c - a) = 0 := by rw [map_sub, hfc, hfa, sub_self]
  have hq : f (b - a) = 0 := by rw [map_sub, hfb, hfy, hfa, sub_self]
  have hw' :
      (c 0 - a 0) * f ![1, 0] + (c 1 - a 1) * f ![0, 1] = 0 := by
    have hcoord := pick_continuousLinearMap_apply_coordinates f (c - a)
    rw [hw] at hcoord
    simpa only [Pi.sub_apply] using hcoord.symm
  have hq' :
      (b 0 - a 0) * f ![1, 0] + (b 1 - a 1) * f ![0, 1] = 0 := by
    have hcoord := pick_continuousLinearMap_apply_coordinates f (b - a)
    rw [hq] at hcoord
    simpa only [Pi.sub_apply] using hcoord.symm
  have hdet :
      (c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0) ≠ 0 := by
    rw [← pick_side_apply]
    exact fun hz ↦ hbline ((pick_side_eq_zero_iff_mem_line hac b).1 hz)
  have hf0prod :
      ((c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0)) *
        f ![1, 0] = 0 := by
    linear_combination (b 1 - a 1) * hw' - (c 1 - a 1) * hq'
  have hf1prod :
      ((c 0 - a 0) * (b 1 - a 1) - (c 1 - a 1) * (b 0 - a 0)) *
        f ![0, 1] = 0 := by
    linear_combination (c 0 - a 0) * hq' - (b 0 - a 0) * hw'
  have hf0 : f ![1, 0] = 0 := (mul_eq_zero.mp hf0prod).resolve_left hdet
  have hf1 : f ![0, 1] = 0 := (mul_eq_zero.mp hf1prod).resolve_left hdet
  apply hfne
  ext z
  rw [pick_continuousLinearMap_apply_coordinates, hf0, hf1]
  simp

private theorem pick_side_combo (a c p q : Fin 2 → ℝ) (s t : ℝ) (hst : s + t = 1) :
    pickSide a c (s • p + t • q) = s * pickSide a c p + t * pickSide a c q := by
  simp only [pickSide, map_add, map_smul, smul_eq_mul]
  linear_combination (pickNormal a c a) * hst

private theorem pick_extreme_of_extreme_inter_halfPlus {P : Set (Fin 2 → ℝ)}
    (hP : Convex ℝ P) {a c x : Fin 2 → ℝ}
    (hx : x ∈ (P ∩ pickHalfPlus a c).extremePoints ℝ) (hsx : 0 < pickSide a c x) :
    x ∈ P.extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨hx.1.1, ?_⟩
  intro y hy z hz hxyz
  rcases hxyz with ⟨s, t, hs, ht, hst, hxeq⟩
  let sx := pickSide a c x
  let sy := pickSide a c y
  let sz := pickSide a c z
  let A := |sy| + |sz| + sx
  let r := sx / (2 * A)
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith [abs_nonneg sy, abs_nonneg sz]
  have hr : 0 < r := div_pos hsx (by positivity)
  have hr1 : r < 1 := by
    apply (div_lt_one (by positivity)).2
    dsimp only [A]
    nlinarith [abs_nonneg sy, abs_nonneg sz]
  have hrA : r * A = sx / 2 := by
    dsimp only [r]
    field_simp [ne_of_gt hA]
  have hry : r * (sx + |sy|) ≤ sx / 2 := by
    calc
      r * (sx + |sy|) ≤ r * A := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        dsimp only [A]
        linarith [abs_nonneg sz]
      _ = sx / 2 := hrA
  have hrz : r * (sx + |sz|) ≤ sx / 2 := by
    calc
      r * (sx + |sz|) ≤ r * A := by
        apply mul_le_mul_of_nonneg_left _ hr.le
        dsimp only [A]
        linarith [abs_nonneg sy]
      _ = sx / 2 := hrA
  let y' := (1 - r) • x + r • y
  let z' := (1 - r) • x + r • z
  have hy'side : 0 < pickSide a c y' := by
    rw [show pickSide a c y' = (1 - r) * sx + r * sy by
      exact pick_side_combo a c x y (1 - r) r (by ring)]
    have hsy : -|sy| ≤ sy := neg_abs_le sy
    have hrsy : -(r * |sy|) ≤ r * sy := by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left hsy hr.le
    nlinarith
  have hz'side : 0 < pickSide a c z' := by
    rw [show pickSide a c z' = (1 - r) * sx + r * sz by
      exact pick_side_combo a c x z (1 - r) r (by ring)]
    have hsz : -|sz| ≤ sz := neg_abs_le sz
    have hrsz : -(r * |sz|) ≤ r * sz := by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left hsz hr.le
    nlinarith
  have hy'P : y' ∈ P := hP hx.1.1 hy (by linarith) hr.le (by ring)
  have hz'P : z' ∈ P := hP hx.1.1 hz (by linarith) hr.le (by ring)
  have hy' : y' ∈ P ∩ pickHalfPlus a c :=
    ⟨hy'P, (pick_mem_halfPlus_iff a c y').2 hy'side.le⟩
  have hz' : z' ∈ P ∩ pickHalfPlus a c :=
    ⟨hz'P, (pick_mem_halfPlus_iff a c z').2 hz'side.le⟩
  have hbetween : x ∈ openSegment ℝ y' z' := by
    refine ⟨s, t, hs, ht, hst, ?_⟩
    dsimp only [y', z']
    calc
      s • ((1 - r) • x + r • y) + t • ((1 - r) • x + r • z) =
          (s * (1 - r) + t * (1 - r)) • x + r • (s • y + t • z) := by module
      _ = (1 - r) • x + r • (s • y + t • z) := by rw [← add_mul, hst, one_mul]
      _ = (1 - r) • x + r • x := by rw [hxeq]
      _ = x := by module
  have hy'x : y' = x := hx.2 hy' hz' hbetween
  have hz'x : z' = x := hx.2 hz' hy' (by rwa [openSegment_symm])
  constructor
  · funext i
    have hi := congrFun hy'x i
    dsimp only [y'] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    nlinarith
  · funext i
    have hi := congrFun hz'x i
    dsimp only [z'] at hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    nlinarith

private theorem pick_side_swap (a c x : Fin 2 → ℝ) :
    pickSide c a x = -pickSide a c x := by
  rw [pick_side_apply, pick_side_apply]
  ring

private theorem pick_halfMinus_eq_halfPlus (a c : Fin 2 → ℝ) :
    pickHalfMinus a c = pickHalfPlus c a := by
  ext x
  rw [pick_mem_halfMinus_iff, pick_mem_halfPlus_iff, pick_side_swap]
  constructor <;> intro h <;> linarith

private theorem pick_convexHull_inter_halfPlus {S : Set (Fin 2 → ℝ)} (hS : S.Finite)
    {a c : Fin 2 → ℝ} (hac : a ≠ c)
    (ha : a ∈ (convexHull ℝ S).extremePoints ℝ)
    (hc : c ∈ (convexHull ℝ S).extremePoints ℝ) :
    convexHull ℝ (S ∩ pickHalfPlus a c) = convexHull ℝ S ∩ pickHalfPlus a c := by
  let P := convexHull ℝ S
  let K := P ∩ pickHalfPlus a c
  have hP : Convex ℝ P := convex_convexHull ℝ S
  have hK : Convex ℝ K := hP.inter (pick_halfPlus_convex a c)
  have hPcomp : IsCompact P := hS.isCompact_convexHull ℝ
  have hKcomp : IsCompact K := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have haS : a ∈ S := extremePoints_convexHull_subset ha
  have hcS : c ∈ S := extremePoints_convexHull_subset hc
  have haK : a ∈ K := ⟨ha.1, (pick_mem_halfPlus_iff a c a).2 (by simp [pickSide])⟩
  have hcK : c ∈ K := ⟨hc.1, (pick_mem_halfPlus_iff a c c).2 (by
    rw [pick_side_apply]
    ring_nf
    exact le_rfl)⟩
  have hext : K.extremePoints ℝ ⊆ S ∩ pickHalfPlus a c := by
    intro x hx
    have hxside := (pick_mem_halfPlus_iff a c x).1 hx.1.2
    refine ⟨?_, hx.1.2⟩
    rcases hxside.eq_or_lt with hxzero | hxpos
    · have hxline : x ∈ line[ℝ, a, c] :=
        (pick_side_eq_zero_iff_mem_line hac x).1 hxzero.symm
      have hxseg : x ∈ segment ℝ a c := by
        rw [← pick_inter_line_eq_segment hP hac ha hc]
        exact ⟨hx.1.1, hxline⟩
      rcases (mem_extremePoints_iff_forall_segment.mp hx).2 a haK c hcK hxseg with hax | hcx
      · simpa [hax] using haS
      · simpa [hcx] using hcS
    · exact extremePoints_convexHull_subset
        (pick_extreme_of_extreme_inter_halfPlus hP hx hxpos)
  apply Set.Subset.antisymm
  · exact convexHull_min (Set.inter_subset_inter_left _ (subset_convexHull ℝ S)) hK
  · change K ⊆ convexHull ℝ (S ∩ pickHalfPlus a c)
    rw [← closure_convexHull_extremePoints hKcomp hK]
    apply closure_minimal (convexHull_mono hext)
    exact (hS.inter_of_left (pickHalfPlus a c)).isCompact_convexHull ℝ |>.isClosed

private theorem pick_convexHull_inter_halfMinus {S : Set (Fin 2 → ℝ)} (hS : S.Finite)
    {a c : Fin 2 → ℝ} (hac : a ≠ c)
    (ha : a ∈ (convexHull ℝ S).extremePoints ℝ)
    (hc : c ∈ (convexHull ℝ S).extremePoints ℝ) :
    convexHull ℝ (S ∩ pickHalfMinus a c) = convexHull ℝ S ∩ pickHalfMinus a c := by
  rw [pick_halfMinus_eq_halfPlus]
  exact pick_convexHull_inter_halfPlus hS hac.symm hc ha

private theorem pick_side_mul_side_neg_of_cross {a b c d y : Fin 2 → ℝ}
    (hac : a ≠ c) (hyac : y ∈ openSegment ℝ a c) (hybd : y ∈ openSegment ℝ b d)
    (hbline : b ∉ line[ℝ, a, c]) : pickSide a c b * pickSide a c d < 0 := by
  have hyline : y ∈ line[ℝ, a, c] := by
    apply affineSegment_subset_affineSpan ℝ a c
    rw [affineSegment_eq_segment]
    exact openSegment_subset_segment ℝ a c hyac
  have hyzero : pickSide a c y = 0 := (pick_side_eq_zero_iff_mem_line hac y).2 hyline
  rcases hybd with ⟨s, t, hs, ht, hst, hyeq⟩
  have hsum : s * pickSide a c b + t * pickSide a c d = 0 := by
    have h := congrArg (pickSide a c) hyeq
    rw [pick_side_combo a c b d s t hst, hyzero] at h
    exact h
  have hbzero : pickSide a c b ≠ 0 := fun hbzero ↦
    hbline ((pick_side_eq_zero_iff_mem_line hac b).1 hbzero)
  rcases lt_or_gt_of_ne hbzero with hbneg | hbpos
  · have hsneg : s * pickSide a c b < 0 := mul_neg_of_pos_of_neg hs hbneg
    have htdpos : 0 < t * pickSide a c d := by linarith
    have hdpos : 0 < pickSide a c d := by
      rcases (mul_pos_iff.mp htdpos) with ⟨-, hdpos⟩ | ⟨htneg, -⟩
      · exact hdpos
      · exact (htneg.not_gt ht).elim
    exact mul_neg_of_neg_of_pos hbneg hdpos
  · have hspos : 0 < s * pickSide a c b := mul_pos hs hbpos
    have htdneg : t * pickSide a c d < 0 := by linarith
    have hdneg : pickSide a c d < 0 := by
      rcases (mul_neg_iff.mp htdneg) with ⟨-, hdneg⟩ | ⟨htneg, -⟩
      · exact hdneg
      · exact (htneg.not_gt ht).elim
    exact mul_neg_of_pos_of_neg hbpos hdneg

private theorem pick_interior_inter_halfPlus_nonempty {P : Set (Fin 2 → ℝ)}
    (hP : Convex ℝ P) (hPclosed : IsClosed P) (hPint : (interior P).Nonempty)
    {a c x : Fin 2 → ℝ} (hac : a ≠ c) (hxP : x ∈ P) (hxside : 0 < pickSide a c x) :
    (interior (P ∩ pickHalfPlus a c)).Nonempty := by
  let U : Set (Fin 2 → ℝ) := {z | pickNormal a c a < pickNormal a c z}
  have hUopen : IsOpen U := isOpen_lt continuous_const (pickNormal a c).continuous
  have hxU : x ∈ U := by
    change pickNormal a c a < pickNormal a c x
    dsimp only [pickSide] at hxside
    linarith
  have hxcl : x ∈ closure (interior P) := by
    rw [hP.closure_interior_eq_closure_of_nonempty_interior hPint, hPclosed.closure_eq]
    exact hxP
  obtain ⟨z, hzU, hzP⟩ := (mem_closure_iff.mp hxcl) U hUopen hxU
  refine ⟨z, ?_⟩
  rw [interior_inter, pick_interior_halfPlus hac]
  exact ⟨hzP, hzU⟩

private theorem pick_interior_inter_halfMinus_nonempty {P : Set (Fin 2 → ℝ)}
    (hP : Convex ℝ P) (hPclosed : IsClosed P) (hPint : (interior P).Nonempty)
    {a c x : Fin 2 → ℝ} (hac : a ≠ c) (hxP : x ∈ P) (hxside : pickSide a c x < 0) :
    (interior (P ∩ pickHalfMinus a c)).Nonempty := by
  rw [pick_halfMinus_eq_halfPlus]
  apply pick_interior_inter_halfPlus_nonempty hP hPclosed hPint hac.symm hxP
  rw [pick_side_swap]
  linarith

private theorem pick_interior_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    (hPint : (interior P).Nonempty) {a b c d y : Fin 2 → ℝ}
    (ha : a ∈ P.extremePoints ℝ) (hb : b ∈ P) (hc : c ∈ P.extremePoints ℝ)
    (hd : d ∈ P) (hac : a ≠ c) (hyac : y ∈ openSegment ℝ a c)
    (hybd : y ∈ openSegment ℝ b d) (hbline : b ∉ line[ℝ, a, c]) :
    interior P =
      (interior (P ∩ pickHalfPlus a c) ∪ interior (P ∩ pickHalfMinus a c)) ∪
        openSegment ℝ a c := by
  have hopen : openSegment ℝ a c ⊆ interior P :=
    pick_openSegment_subset_interior hP hPint ha.1 hb hc.1 hd hac hyac hybd hbline
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy (pickNormal a c x) (pickNormal a c a) with hneg | heq | hpos
    · left
      right
      rw [interior_inter, pick_interior_halfMinus hac]
      exact ⟨hx, hneg⟩
    · right
      have hxline : x ∈ line[ℝ, a, c] := by
        apply (pick_side_eq_zero_iff_mem_line hac x).1
        dsimp only [pickSide]
        linarith
      have hxseg : x ∈ segment ℝ a c := by
        rw [← pick_inter_line_eq_segment hP hac ha hc]
        exact ⟨interior_subset hx, hxline⟩
      rw [← insert_endpoints_openSegment ℝ] at hxseg
      rcases hxseg with hxa | hxc | hxopen
      · exact (Set.disjoint_left.mp (disjoint_interior_extremePoints P) hx
          (hxa ▸ ha)).elim
      · exact (Set.disjoint_left.mp (disjoint_interior_extremePoints P) hx
          (hxc ▸ hc)).elim
      · exact hxopen
    · left
      left
      rw [interior_inter, pick_interior_halfPlus hac]
      exact ⟨hx, hpos⟩
  · rintro ((hx | hx) | hx)
    · exact interior_mono Set.inter_subset_left hx
    · exact interior_mono Set.inter_subset_left hx
    · exact hopen hx

private theorem pick_lattice_ncard_eq_interior_add_frontier {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) :
    (pickLatticePoints K).ncard = (pickLatticePoints (interior K)).ncard +
      (pickLatticePoints (frontier K)).ncard := by
  have hL : (pickLatticePoints K).Finite := pick_lattice_preimage_finite hK
  have hI : (pickLatticePoints (interior K)).Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ K
    exact interior_subset hz
  have hB : (pickLatticePoints (frontier K)).Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ K
    exact hK.isClosed.frontier_subset hz
  have hset : pickLatticePoints K =
      pickLatticePoints (interior K) ∪ pickLatticePoints (frontier K) := by
    change pickCast ⁻¹' K = pickCast ⁻¹' interior K ∪ pickCast ⁻¹' frontier K
    rw [← Set.preimage_union]
    congr 1
    calc
      K = closure K := hK.isClosed.closure_eq.symm
      _ = interior K ∪ frontier K := closure_eq_interior_union_frontier K
  rw [hset, Set.ncard_union_eq _ hI hB]
  rw [Set.disjoint_left]
  intro z hzI hzB
  exact Set.disjoint_left.mp disjoint_interior_frontier hzI hzB

private theorem pick_lattice_segment_ncard {A C : Fin 2 → ℤ} (hAC : A ≠ C) :
    (pickLatticePoints (segment ℝ (pickCast A) (pickCast C))).ncard =
      (pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))).ncard + 2 := by
  let O := pickLatticePoints (openSegment ℝ (pickCast A) (pickCast C))
  have hset : pickLatticePoints (segment ℝ (pickCast A) (pickCast C)) = {A, C} ∪ O := by
    change pickCast ⁻¹' segment ℝ (pickCast A) (pickCast C) = {A, C} ∪ O
    dsimp only [O]
    rw [← insert_endpoints_openSegment ℝ]
    ext z
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [pick_cast_injective.eq_iff, pick_cast_injective.eq_iff]
    tauto
  have hdisj : Disjoint ({A, C} : Set (Fin 2 → ℤ)) O := by
    rw [Set.disjoint_left]
    intro z hz hzO
    rcases hz with hza | hzc
    · rw [hza] at hzO
      apply hAC
      apply pick_cast_injective
      exact left_mem_openSegment_iff.mp hzO
    · rw [Set.mem_singleton_iff] at hzc
      rw [hzc] at hzO
      apply hAC
      apply pick_cast_injective
      exact right_mem_openSegment_iff.mp hzO
  have hO : O.Finite := by
    have hpair : ({pickCast A, pickCast C} : Set (Fin 2 → ℝ)).Finite :=
      Set.finite_insert.mpr (Set.finite_singleton _)
    have hseg : IsCompact (segment ℝ (pickCast A) (pickCast C)) := by
      rw [← convexHull_pair]
      exact hpair.isCompact_convexHull ℝ
    apply (pick_lattice_preimage_finite hseg).subset
    intro z hz
    exact openSegment_subset_segment ℝ _ _ hz
  dsimp only [O] at hset hdisj hO ⊢
  rw [hset, Set.ncard_union_eq hdisj (Set.finite_insert.mpr (Set.finite_singleton C)) hO,
    Set.ncard_pair hAC]
  omega

private theorem pick_cut_union (P : Set (Fin 2 → ℝ)) (a c : Fin 2 → ℝ) :
    (P ∩ pickHalfPlus a c) ∪ (P ∩ pickHalfMinus a c) = P := by
  ext x
  rw [Set.mem_union, Set.mem_inter_iff, Set.mem_inter_iff, pick_mem_halfPlus_iff,
    pick_mem_halfMinus_iff]
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · intro hx
    rcases le_total 0 (pickSide a c x) with hpos | hneg
    · exact Or.inl ⟨hx, hpos⟩
    · exact Or.inr ⟨hx, hneg⟩

private theorem pick_cut_inter {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    {a c : Fin 2 → ℝ} (hac : a ≠ c) (ha : a ∈ P.extremePoints ℝ)
    (hc : c ∈ P.extremePoints ℝ) :
    (P ∩ pickHalfPlus a c) ∩ (P ∩ pickHalfMinus a c) = segment ℝ a c := by
  ext x
  constructor
  · rintro ⟨⟨hxP, hxplus⟩, -, hxminus⟩
    rw [← pick_inter_line_eq_segment hP hac ha hc]
    refine ⟨hxP, ?_⟩
    rw [← pick_half_inter_eq_line hac]
    exact ⟨hxplus, hxminus⟩
  · intro hx
    have hx' : x ∈ P ∩ (line[ℝ, a, c] : Set (Fin 2 → ℝ)) := by
      rw [pick_inter_line_eq_segment hP hac ha hc]
      exact hx
    have hxhalf : x ∈ pickHalfPlus a c ∩ pickHalfMinus a c := by
      rw [pick_half_inter_eq_line hac]
      exact hx'.2
    exact ⟨⟨hx'.1, hxhalf.1⟩, hx'.1, hxhalf.2⟩

private theorem pick_volume_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    (hPcomp : IsCompact P) {a c : Fin 2 → ℝ} (hac : a ≠ c)
    (ha : a ∈ P.extremePoints ℝ) (hc : c ∈ P.extremePoints ℝ) :
    (volume P).toReal = (volume (P ∩ pickHalfPlus a c)).toReal +
      (volume (P ∩ pickHalfMinus a c)).toReal := by
  let Pp := P ∩ pickHalfPlus a c
  let Pm := P ∩ pickHalfMinus a c
  have hPp : IsCompact Pp := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have hPm : IsCompact Pm := hPcomp.inter_right (pick_halfMinus_isClosed a c)
  have hnull : volume (Pp ∩ Pm) = 0 := by
    rw [show Pp ∩ Pm = segment ℝ a c from pick_cut_inter hP hac ha hc]
    apply MeasureTheory.measure_mono_null _
      (volume.addHaar_affineSubspace line[ℝ, a, c] (pick_line_ne_top hac))
    intro x hx
    rw [← affineSegment_eq_segment ℝ] at hx
    exact affineSegment_subset_affineSpan ℝ a c hx
  have hmeasure := MeasureTheory.measure_union_add_inter (μ := volume) Pp
    hPm.isClosed.measurableSet
  rw [show Pp ∪ Pm = P from pick_cut_union P a c, hnull, add_zero] at hmeasure
  have hpfin : volume Pp ≠ ⊤ := ne_of_lt hPp.measure_lt_top
  have hmfin : volume Pm ≠ ⊤ := ne_of_lt hPm.measure_lt_top
  change (volume P).toReal = (volume Pp).toReal + (volume Pm).toReal
  rw [hmeasure, ENNReal.toReal_add hpfin hmfin]

private noncomputable def pickInvariant (K : Set (Fin 2 → ℝ)) : ℝ :=
  (pickLatticePoints K).ncard + (pickLatticePoints (interior K)).ncard - 2

private theorem pick_invariant_cut {P : Set (Fin 2 → ℝ)} (hP : Convex ℝ P)
    (hPcomp : IsCompact P) (hPint : (interior P).Nonempty) {A C : Fin 2 → ℤ}
    {b d y : Fin 2 → ℝ} (hAC : A ≠ C)
    (ha : pickCast A ∈ P.extremePoints ℝ) (hb : b ∈ P)
    (hc : pickCast C ∈ P.extremePoints ℝ) (hd : d ∈ P)
    (hyac : y ∈ openSegment ℝ (pickCast A) (pickCast C))
    (hybd : y ∈ openSegment ℝ b d) (hbline : b ∉ line[ℝ, pickCast A, pickCast C]) :
    pickInvariant P = pickInvariant (P ∩ pickHalfPlus (pickCast A) (pickCast C)) +
      pickInvariant (P ∩ pickHalfMinus (pickCast A) (pickCast C)) := by
  let a := pickCast A
  let c := pickCast C
  let Pp := P ∩ pickHalfPlus a c
  let Pm := P ∩ pickHalfMinus a c
  let L := pickLatticePoints P
  let Lp := pickLatticePoints Pp
  let Lm := pickLatticePoints Pm
  let I := pickLatticePoints (interior P)
  let Ip := pickLatticePoints (interior Pp)
  let Im := pickLatticePoints (interior Pm)
  let O := pickLatticePoints (openSegment ℝ a c)
  have hac : a ≠ c := fun hac ↦ hAC (pick_cast_injective hac)
  have hPpcomp : IsCompact Pp := hPcomp.inter_right (pick_halfPlus_isClosed a c)
  have hPmcomp : IsCompact Pm := hPcomp.inter_right (pick_halfMinus_isClosed a c)
  have hL : L.Finite := pick_lattice_preimage_finite hPcomp
  have hLp : Lp.Finite := pick_lattice_preimage_finite hPpcomp
  have hLm : Lm.Finite := pick_lattice_preimage_finite hPmcomp
  have hIp : Ip.Finite := by
    apply hLp.subset
    intro z hz
    change pickCast z ∈ Pp
    exact interior_subset hz
  have hIm : Im.Finite := by
    apply hLm.subset
    intro z hz
    change pickCast z ∈ Pm
    exact interior_subset hz
  have hI : I.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact interior_subset hz
  have hO : O.Finite := by
    apply hL.subset
    intro z hz
    change pickCast z ∈ P
    exact hP.segment_subset ha.1 hc.1 (openSegment_subset_segment ℝ a c hz)
  have hLunion : Lp ∪ Lm = L := by
    change pickCast ⁻¹' Pp ∪ pickCast ⁻¹' Pm = pickCast ⁻¹' P
    rw [← Set.preimage_union, pick_cut_union]
  have hLinter : Lp ∩ Lm = pickLatticePoints (segment ℝ a c) := by
    change pickCast ⁻¹' Pp ∩ pickCast ⁻¹' Pm = pickCast ⁻¹' segment ℝ a c
    rw [← Set.preimage_inter, pick_cut_inter hP hac ha hc]
  have hclosed := Set.ncard_union_add_ncard_inter Lp Lm hLp hLm
  rw [hLunion, hLinter] at hclosed
  have hsegment : (pickLatticePoints (segment ℝ a c)).ncard = O.ncard + 2 := by
    exact pick_lattice_segment_ncard hAC
  have hIset : I = (Ip ∪ Im) ∪ O := by
    change pickCast ⁻¹' interior P =
      (pickCast ⁻¹' interior Pp ∪ pickCast ⁻¹' interior Pm) ∪
        pickCast ⁻¹' openSegment ℝ a c
    rw [← Set.preimage_union, ← Set.preimage_union,
      pick_interior_cut hP hPint ha hb hc hd hac hyac hybd hbline]
  have hIpIm : Disjoint Ip Im := by
    rw [Set.disjoint_left]
    intro z hzp hzm
    have hp : pickNormal a c a < pickNormal a c (pickCast z) := by
      change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      exact hzp.2
    have hm : pickNormal a c (pickCast z) < pickNormal a c a := by
      change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      exact hzm.2
    linarith
  have hhalvesO : Disjoint (Ip ∪ Im) O := by
    rw [Set.disjoint_left]
    intro z hzhalf hzO
    have hzline : pickCast z ∈ line[ℝ, a, c] := by
      apply affineSegment_subset_affineSpan ℝ a c
      rw [affineSegment_eq_segment]
      exact openSegment_subset_segment ℝ a c hzO
    have hzeq : pickNormal a c (pickCast z) = pickNormal a c a := by
      have := (pick_side_eq_zero_iff_mem_line hac (pickCast z)).2 hzline
      dsimp only [pickSide] at this
      linarith
    rcases hzhalf with hzp | hzm
    · change pickCast z ∈ interior Pp at hzp
      rw [interior_inter, pick_interior_halfPlus hac] at hzp
      have hlt : pickNormal a c a < pickNormal a c (pickCast z) := hzp.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
    · change pickCast z ∈ interior Pm at hzm
      rw [interior_inter, pick_interior_halfMinus hac] at hzm
      have hlt : pickNormal a c (pickCast z) < pickNormal a c a := hzm.2
      rw [hzeq] at hlt
      exact (lt_irrefl _ hlt).elim
  have hhalfCard : (Ip ∪ Im).ncard = Ip.ncard + Im.ncard :=
    Set.ncard_union_eq hIpIm hIp hIm
  have hinter : I.ncard = Ip.ncard + Im.ncard + O.ncard := by
    rw [hIset, Set.ncard_union_eq hhalvesO (hIp.union hIm) hO, hhalfCard]
  have hclosedR := congrArg (fun n : ℕ ↦ (n : ℝ)) hclosed
  have hsegmentR := congrArg (fun n : ℕ ↦ (n : ℝ)) hsegment
  have hinterR := congrArg (fun n : ℕ ↦ (n : ℝ)) hinter
  push_cast at hclosedR hsegmentR hinterR
  change (L.ncard : ℝ) + I.ncard - 2 =
    ((Lp.ncard : ℝ) + Ip.ncard - 2) + ((Lm.ncard : ℝ) + Im.ncard - 2)
  linarith

private theorem pick_latticePoints_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
    pickLatticePoints (pickCast p +ᵥ K) =
      (fun z : Fin 2 → ℤ ↦ p + z) '' pickLatticePoints K := by
  ext z
  constructor
  · intro hz
    change pickCast z ∈ pickCast p +ᵥ K at hz
    rcases hz with ⟨x, hx, hpx⟩
    refine ⟨z - p, ?_, ?_⟩
    · change pickCast (z - p) ∈ K
      have heq : pickCast (z - p) = x := by
        ext i
        have hi := congrFun hpx i
        change (p i : ℝ) + x i = (z i : ℝ) at hi
        change (z i - p i : ℤ) = x i
        norm_num
        linarith
      rw [heq]
      exact hx
    · funext i
      simp
  · rintro ⟨q, hq, rfl⟩
    change pickCast (p + q) ∈ pickCast p +ᵥ K
    refine ⟨pickCast q, hq, ?_⟩
    ext i
    simp [pickCast]

private theorem pick_lattice_ncard_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
    (pickLatticePoints (pickCast p +ᵥ K)).ncard = (pickLatticePoints K).ncard := by
  rw [pick_latticePoints_vadd]
  exact Set.ncard_image_of_injective _ (Equiv.addLeft p).injective

private theorem pick_invariant_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
    pickInvariant (pickCast p +ᵥ K) = pickInvariant K := by
  rw [pickInvariant, pickInvariant, pick_lattice_ncard_vadd, interior_vadd,
    pick_lattice_ncard_vadd]

private theorem pick_volume_vadd (p : Fin 2 → ℤ) (K : Set (Fin 2 → ℝ)) :
    (volume (pickCast p +ᵥ K)).toReal = (volume K).toReal := by
  rw [MeasureTheory.measure_vadd]

private theorem pick_origin_triangle_doubled (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    2 * (volume (pickTriangle u v h)).toReal = pickInvariant (pickTriangle u v h) := by
  have hformula := toReal_volume_convexHull_lattice_triangle u v h
  rw [← pick_triangle_eq_explicit u v h] at hformula
  change (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (interior (pickTriangle u v h))).ncard +
      (pickLatticePoints (frontier (pickTriangle u v h))).ncard / 2 - 1 at hformula
  have hLB := pick_lattice_ncard_eq_interior_add_frontier (pick_triangle_isCompact u v h)
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  rw [pickInvariant]
  change 2 * (volume (pickTriangle u v h)).toReal =
    (pickLatticePoints (pickTriangle u v h)).ncard +
      (pickLatticePoints (interior (pickTriangle u v h))).ncard - 2
  linarith

private theorem pick_triangle_doubled (p q r : Fin 2 → ℤ)
    (h : pickDet (q - p) (r - p) ≠ 0) :
    2 * (volume (convexHull ℝ
      ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)))).toReal =
      pickInvariant (convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ))) := by
  let T := pickTriangle (q - p) (r - p) h
  have hset : ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) =
      pickCast p +ᵥ ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) := by
    rw [← Set.image_vadd]
    simp only [vadd_eq_add, Set.image_insert_eq, add_zero, Set.image_singleton]
    have hpq : pickCast p + pickCast (q - p) = pickCast q := by
      funext i
      simp [pickCast]
    have hpr : pickCast p + pickCast (r - p) = pickCast r := by
      funext i
      simp [pickCast]
    rw [hpq, hpr]
  have htriangle : convexHull ℝ
        ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T := by
    rw [hset, convexHull_vadd]
    change pickCast p +ᵥ convexHull ℝ
      ({0, pickCast (q - p), pickCast (r - p)} : Set (Fin 2 → ℝ)) = pickCast p +ᵥ T
    rw [← pick_triangle_eq_explicit]
  rw [htriangle, pick_volume_vadd, pick_invariant_vadd]
  exact pick_origin_triangle_doubled (q - p) (r - p) h

private theorem pick_radon_parts_two {f : Fin 4 → (Fin 2 → ℝ)}
    (hf : ConvexIndependent ℝ f) {I : Set (Fin 4)}
    (hI : (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty) :
    I.ncard = 2 ∧ Iᶜ.ncard = 2 := by
  rcases hI with ⟨y, hyI, hyIc⟩
  have hnontrivial (J : Set (Fin 4)) (hyJ : y ∈ convexHull ℝ (f '' J))
      (hyJc : y ∈ convexHull ℝ (f '' Jᶜ)) : J.Nontrivial := by
    have hJ : J.Nonempty := by
      apply Set.image_nonempty.mp
      exact convexHull_nonempty_iff.mp ⟨y, hyJ⟩
    rcases hJ with ⟨i, hi⟩
    refine (Set.nontrivial_iff_exists_ne hi).2 ?_
    by_contra h
    push Not at h
    have hJeq : J = {i} := by
      ext j
      constructor
      · intro hj
        exact Set.mem_singleton_iff.mpr (h j hj)
      · intro hj
        rw [Set.mem_singleton_iff] at hj
        simpa [hj] using hi
    have hyi : y = f i := by
      rw [hJeq, Set.image_singleton, convexHull_singleton] at hyJ
      exact Set.mem_singleton_iff.mp hyJ
    subst y
    exact ((hf.mem_convexHull_iff Jᶜ i).mp hyJc) hi
  have hnI : I.Nontrivial := hnontrivial I hyI hyIc
  have hnIc : Iᶜ.Nontrivial := hnontrivial Iᶜ hyIc (by simpa using hyI)
  have hloI : 2 ≤ I.ncard := (Set.one_lt_ncard_iff_nontrivial.mpr hnI)
  have hloIc : 2 ≤ Iᶜ.ncard := (Set.one_lt_ncard_iff_nontrivial.mpr hnIc)
  have hsum : I.ncard + Iᶜ.ncard = 4 := by
    simpa using Set.ncard_add_ncard_compl I
  omega

private theorem pick_not_collinear_of_convexIndependent {f : Fin 4 → (Fin 2 → ℝ)}
    (hf : ConvexIndependent ℝ f) {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ¬Collinear ℝ ({f i, f j, f k} : Set (Fin 2 → ℝ)) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hijk | hjki | hkij
  · have hjmem : f j ∈ convexHull ℝ (f '' ({i, k} : Set (Fin 4))) := by
      rw [Set.image_pair, convexHull_pair]
      exact hijk.mem_segment
    have := (hf.mem_convexHull_iff ({i, k} : Set (Fin 4)) j).mp hjmem
    simp [hij.symm, hjk] at this
  · have hkmem : f k ∈ convexHull ℝ (f '' ({j, i} : Set (Fin 4))) := by
      rw [Set.image_pair, convexHull_pair]
      exact hjki.mem_segment
    have := (hf.mem_convexHull_iff ({j, i} : Set (Fin 4)) k).mp hkmem
    simp [hjk.symm, hik.symm] at this
  · have himem : f i ∈ convexHull ℝ (f '' ({k, j} : Set (Fin 4))) := by
      rw [Set.image_pair, convexHull_pair]
      exact hkij.mem_segment
    have := (hf.mem_convexHull_iff ({k, j} : Set (Fin 4)) i).mp himem
    simp [hik, hij] at this

private theorem pick_polygon_doubled (vertices : Finset (Fin 2 → ℤ))
    (hfull : (interior (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    2 * (volume (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ))))).toReal =
      pickInvariant (convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))) := by
  classical
  induction vertices using Finset.strongInductionOn with
  | _ vertices ih =>
    let X := pickCast '' (vertices : Set (Fin 2 → ℤ))
    let P := convexHull ℝ X
    let E := vertices.filter fun z ↦ pickCast z ∈ P.extremePoints ℝ
    have hXfin : X.Finite := vertices.finite_toSet.image pickCast
    have hPconv : Convex ℝ P := convex_convexHull ℝ X
    have hPcomp : IsCompact P := hXfin.isCompact_convexHull ℝ
    have hEP : pickCast '' (E : Set (Fin 2 → ℤ)) = P.extremePoints ℝ := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Finset.mem_filter.mp hz).2
      · intro hx
        rcases extremePoints_convexHull_subset hx with ⟨z, hz, rfl⟩
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, hx⟩, rfl⟩
    have hPhull : convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = P := by
      calc
        convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) =
            closure (convexHull ℝ (pickCast '' (E : Set (Fin 2 → ℤ)))) :=
          ((E.finite_toSet.image pickCast).isCompact_convexHull ℝ).isClosed.closure_eq.symm
        _ = P := by
          rw [hEP]
          exact closure_convexHull_extremePoints hPcomp hPconv
    have hspan : affineSpan ℝ (pickCast '' (E : Set (Fin 2 → ℤ))) = ⊤ := by
      apply affineSpan_eq_top_of_nonempty_interior
      rw [hPhull]
      exact hfull
    by_cases hsmall : E.card ≤ 3
    · have hlarge : 3 ≤ E.card := by
        by_contra h
        have hcard : E.card ≤ 2 := by omega
        have hnotop := affineSpan_image_ne_top_of_encard_le_finrank ℝ E.finite_toSet
          (p := pickCast) (by
            rw [Set.encard_coe_eq_coe_finsetCard, Module.finrank_fin_fun]
            exact_mod_cast hcard)
        exact hnotop hspan
      have hcard : E.card = 3 := by omega
      obtain ⟨e : Fin 3 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_eq_finset (s := E) (α := Fin 3)
          (by simpa using hcard.symm)
      have herange : Set.range e = (E : Set (Fin 2 → ℤ)) := by
        have hcoe := congrArg (fun s : Finset (Fin 2 → ℤ) ↦ (s : Set (Fin 2 → ℤ))) he
        simpa using hcoe
      let p := e 0
      let q := e 1
      let r := e 2
      have htriple : pickCast '' (E : Set (Fin 2 → ℤ)) =
          ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [← herange] at hz
          rcases hz with ⟨i, rfl⟩
          fin_cases i <;> simp [p, q, r]
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rintro (rfl | rfl | rfl)
          · exact ⟨p, herange ▸ Set.mem_range_self 0, rfl⟩
          · exact ⟨q, herange ▸ Set.mem_range_self 1, rfl⟩
          · exact ⟨r, herange ▸ Set.mem_range_self 2, rfl⟩
      have hpq : pickCast p ≠ pickCast q := by
        intro hpq
        have hzeroone : (0 : Fin 3) = 1 := e.injective (pick_cast_injective hpq)
        norm_num at hzeroone
      have hdet : pickDet (q - p) (r - p) ≠ 0 := by
        intro hdet
        have hrline : pickCast r ∈ line[ℝ, pickCast p, pickCast q] := by
          apply (pick_side_eq_zero_iff_mem_line hpq (pickCast r)).1
          rw [pick_side_apply]
          norm_num [pickDet, pickCast] at hdet ⊢
          exact_mod_cast hdet
        have hle : affineSpan ℝ
            ({pickCast p, pickCast q, pickCast r} : Set (Fin 2 → ℝ)) ≤
              line[ℝ, pickCast p, pickCast q] := by
          apply affineSpan_le.2
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact left_mem_affineSpan_pair ℝ _ _
          · exact right_mem_affineSpan_pair ℝ _ _
          · exact hrline
        rw [← htriple, hspan] at hle
        exact pick_line_ne_top hpq (top_unique hle)
      change 2 * (volume P).toReal = pickInvariant P
      rw [← hPhull, htriple]
      exact pick_triangle_doubled p q r hdet
    · have hEcard : 4 ≤ E.card := by omega
      obtain ⟨e : Fin 4 ↪ (Fin 2 → ℤ), he⟩ :=
        Function.Embedding.exists_of_card_le_finset (s := E) (α := Fin 4)
          (by simpa using hEcard)
      let g : Fin 4 → (Fin 2 → ℝ) := fun i ↦ pickCast (e i)
      have hge (i : Fin 4) : g i ∈ P.extremePoints ℝ := by
        have hei := he (Set.mem_range_self i)
        change e i ∈ vertices.filter (fun z ↦ pickCast z ∈ P.extremePoints ℝ) at hei
        change pickCast (e i) ∈ P.extremePoints ℝ
        exact (Finset.mem_filter.mp hei).2
      let ee : Fin 4 ↪ P.extremePoints ℝ :=
        ⟨fun i ↦ ⟨g i, hge i⟩, fun i j hij ↦ e.injective
          (pick_cast_injective (Subtype.ext_iff.mp hij))⟩
      have hgconv : ConvexIndependent ℝ g := by
        intro s i hi
        by_contra his
        have hiext := (hPconv.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp (hge i)
        apply hiext.2
        apply convexHull_mono _ hi
        rintro _ ⟨j, hjs, rfl⟩
        refine ⟨(hge j).1, ?_⟩
        rw [Set.mem_singleton_iff]
        intro hji
        have : j = i := e.injective (pick_cast_injective hji)
        exact his (this ▸ hjs)
      have hgdep : ¬AffineIndependent ℝ g := by
        apply (finrank_vectorSpan_le_iff_not_affineIndependent ℝ g (n := 2) (by simp)).1
        simpa [Module.finrank_fin_fun] using (vectorSpan ℝ (Set.range g)).finrank_le
      obtain ⟨I, y, hyI, hyIc⟩ := Convex.radon_partition hgdep
      have hparts := pick_radon_parts_two hgconv ⟨y, hyI, hyIc⟩
      obtain ⟨i₀, i₁, hi₀i₁, hI⟩ := Set.ncard_eq_two.mp hparts.1
      obtain ⟨j₀, j₁, hj₀j₁, hIc⟩ := Set.ncard_eq_two.mp hparts.2
      have hi₀ : i₀ ∈ I := by simp [hI]
      have hi₁ : i₁ ∈ I := by simp [hI]
      have hj₀ : j₀ ∈ Iᶜ := by simp [hIc]
      have hj₁ : j₁ ∈ Iᶜ := by simp [hIc]
      have hyac : y ∈ openSegment ℝ (g i₀) (g i₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₀).mp (by simpa [hiy] using hyIc)) hi₀
        · intro hiy
          exact ((hgconv.mem_convexHull_iff Iᶜ i₁).mp (by simpa [hiy] using hyIc)) hi₁
        · rw [← convexHull_pair, ← Set.image_pair, ← hI]
          exact hyI
      have hybd : y ∈ openSegment ℝ (g j₀) (g j₁) := by
        apply mem_openSegment_of_ne_left_right
        · intro hjy
          exact hj₀ ((hgconv.mem_convexHull_iff I j₀).mp (by simpa [hjy] using hyI))
        · intro hjy
          exact hj₁ ((hgconv.mem_convexHull_iff I j₁).mp (by simpa [hjy] using hyI))
        · rw [← convexHull_pair, ← Set.image_pair, ← hIc]
          exact hyIc
      have hj₀i₀ : j₀ ≠ i₀ := fun h ↦ hj₀ (h ▸ hi₀)
      have hj₀i₁ : j₀ ≠ i₁ := fun h ↦ hj₀ (h ▸ hi₁)
      have hbline : g j₀ ∉ line[ℝ, g i₀, g i₁] := by
        intro hbline
        exact pick_not_collinear_of_convexIndependent hgconv hj₀i₀ hi₀i₁ hj₀i₁
          (collinear_insert_of_mem_affineSpan_pair hbline)
      have hprod : pickSide (g i₀) (g i₁) (g j₀) *
          pickSide (g i₀) (g i₁) (g j₁) < 0 :=
        pick_side_mul_side_neg_of_cross (fun h ↦ hi₀i₁ (e.injective
          (pick_cast_injective h))) hyac hybd hbline
      have hAV : e i₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₀))).1
      have hCV : e i₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self i₁))).1
      have hj₀V : e j₀ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₀))).1
      have hj₁V : e j₁ ∈ vertices := (Finset.mem_filter.mp (he (Set.mem_range_self j₁))).1
      have finish (B D : Fin 2 → ℤ) (hBV : B ∈ vertices) (hDV : D ∈ vertices)
          (hBpos : 0 < pickSide (g i₀) (g i₁) (pickCast B))
          (hDneg : pickSide (g i₀) (g i₁) (pickCast D) < 0)
          (hyBD : y ∈ openSegment ℝ (pickCast B) (pickCast D)) :
          2 * (volume P).toReal = pickInvariant P := by
        let Vp := vertices.filter fun z ↦ pickCast z ∈ pickHalfPlus (g i₀) (g i₁)
        let Vm := vertices.filter fun z ↦ pickCast z ∈ pickHalfMinus (g i₀) (g i₁)
        have hVp_lt : Vp ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨D, hDV, by rw [pick_mem_halfPlus_iff]; linarith⟩
        have hVm_lt : Vm ⊂ vertices := by
          rw [Finset.filter_ssubset]
          exact ⟨B, hBV, by rw [pick_mem_halfMinus_iff]; linarith⟩
        have hXp : pickCast '' (Vp : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfPlus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hXm : pickCast '' (Vm : Set (Fin 2 → ℤ)) =
            X ∩ pickHalfMinus (g i₀) (g i₁) := by
          ext x
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨⟨z, (Finset.mem_filter.mp hz).1, rfl⟩, (Finset.mem_filter.mp hz).2⟩
          · rintro ⟨⟨z, hz, rfl⟩, hzhalf⟩
            exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzhalf⟩, rfl⟩
        have hAC : e i₀ ≠ e i₁ := fun h ↦ hi₀i₁ (e.injective h)
        have hac : g i₀ ≠ g i₁ := fun h ↦ hAC (pick_cast_injective h)
        have ha : g i₀ ∈ P.extremePoints ℝ := hge i₀
        have hc : g i₁ ∈ P.extremePoints ℝ := hge i₁
        have hHullp : convexHull ℝ (pickCast '' (Vp : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfPlus (g i₀) (g i₁) := by
          rw [hXp]
          exact pick_convexHull_inter_halfPlus hXfin hac ha hc
        have hHullm : convexHull ℝ (pickCast '' (Vm : Set (Fin 2 → ℤ))) =
            P ∩ pickHalfMinus (g i₀) (g i₁) := by
          rw [hXm]
          exact pick_convexHull_inter_halfMinus hXfin hac ha hc
        have hBP : pickCast B ∈ P := subset_convexHull ℝ X ⟨B, hBV, rfl⟩
        have hDP : pickCast D ∈ P := subset_convexHull ℝ X ⟨D, hDV, rfl⟩
        have hfullp : (interior (convexHull ℝ
            (pickCast '' (Vp : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullp]
          exact pick_interior_inter_halfPlus_nonempty hPconv hPcomp.isClosed hfull hac hBP hBpos
        have hfullm : (interior (convexHull ℝ
            (pickCast '' (Vm : Set (Fin 2 → ℤ))))).Nonempty := by
          rw [hHullm]
          exact pick_interior_inter_halfMinus_nonempty hPconv hPcomp.isClosed hfull hac hDP hDneg
        have hpickp := ih Vp hVp_lt hfullp
        have hpickm := ih Vm hVm_lt hfullm
        rw [hHullp] at hpickp
        rw [hHullm] at hpickm
        have hvol := pick_volume_cut hPconv hPcomp hac ha hc
        have hBline : pickCast B ∉ line[ℝ, g i₀, g i₁] := by
          intro hline
          have := (pick_side_eq_zero_iff_mem_line hac (pickCast B)).2 hline
          linarith
        have hinv := pick_invariant_cut hPconv hPcomp hfull hAC ha hBP hc hDP hyac hyBD hBline
        linarith
      rcases mul_neg_iff.mp hprod with ⟨hj₀pos, hj₁neg⟩ | ⟨hj₀neg, hj₁pos⟩
      · exact finish (e j₀) (e j₁) hj₀V hj₁V hj₀pos hj₁neg hybd
      · exact finish (e j₁) (e j₀) hj₁V hj₀V hj₁pos hj₀neg
          (by simpa [openSegment_symm ℝ] using hybd)

/-- **Pick's theorem for convex lattice polygons.** Let $V \subset \mathbb{Z}^2$ be a finite
set of lattice points, let $P \subset \mathbb{R}^2$ be the convex hull of $V$, and suppose that
$P$ has nonempty interior. Let $I$ be the number of points of $\mathbb{Z}^2$ in the interior of
$P$ and $B$ the number of points of $\mathbb{Z}^2$ on the boundary of $P$. Then the area
(two-dimensional Lebesgue measure) of $P$ equals $I + B/2 - 1$.

Proof: The triangle case counts lattice points in a half-open fundamental
parallelogram. A crossing diagonal then cuts larger polygons into two smaller
full-dimensional lattice polygons, allowing strong induction on the vertex set.

Proves `Wanted` entry `pick_convex_lattice_polygon`.

Sources: Eugen J. Ionascu, "A Parametrization of Equilateral Triangles
Having Integer Coordinates", Journal of Integer Sequences 10 (2007),
Article 07.6.7, standard formula `Area = #b / 2 + #i - 1`, lines 87–100,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Ionascu/ionascu2.tex>;
Kevin A. Broughan, "The gcd-sum function", Journal of Integer Sequences 4
(2001), Article 01.2.2, trapezium application, lines 699–715 (the prose
there prints "+1" but the paper's own derived formula, equation label `10`,
uses the minus-one form),
<https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex>;
Gil Alon and Pete L. Clark, "On the Number of Representations of an
Integer by a Linear Form", Journal of Integer Sequences 8 (2005),
Article 05.5.2, generalized lattice version
`A(P) = δ * (h + b / 2 - 1)`, lines 633–638 (this module is the `δ = 1`
standard-lattice case),
<https://cs.uwaterloo.ca/journals/JIS/VOL8/Clark/clark80.tex>.
-/
theorem pick_convex_lattice_polygon (vertices : Finset (Fin 2 → ℤ))
    (hfull :
      (interior
        (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    (volume
      (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).toReal =
      (Set.ncard {z : Fin 2 → ℤ |
        (fun i => (z i : ℝ)) ∈
          interior
            (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) +
        (Set.ncard {z : Fin 2 → ℤ |
          (fun i => (z i : ℝ)) ∈
            frontier
              (convexHull ℝ
                ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) / 2 - 1 := by
  let P := convexHull ℝ (pickCast '' (vertices : Set (Fin 2 → ℤ)))
  have hPcomp : IsCompact P :=
    (vertices.finite_toSet.image pickCast).isCompact_convexHull ℝ
  have hdoubled := pick_polygon_doubled vertices hfull
  change 2 * (volume P).toReal = pickInvariant P at hdoubled
  rw [pickInvariant] at hdoubled
  have hLB := pick_lattice_ncard_eq_interior_add_frontier hPcomp
  have hLBR := congrArg (fun n : ℕ ↦ (n : ℝ)) hLB
  push_cast at hLBR
  change (volume P).toReal =
    (pickLatticePoints (interior P)).ncard +
      (pickLatticePoints (frontier P)).ncard / 2 - 1
  linarith

end

end MetaMathlibExt
