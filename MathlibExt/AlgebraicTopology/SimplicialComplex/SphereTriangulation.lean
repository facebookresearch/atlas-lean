/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.Morphism
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate

/-!
# Finite triangulations of the classical sphere

The actual nonempty proper faces of the simplex on `Fin (n + 1)` have their
weak finite-face realization. Its coordinates form exactly the zero-coordinate
locus of the standard simplex. The sphere comparison restricts the chosen
classical disk map and retains the actual realized boundary inclusion.
-/

public section

noncomputable section

open CategoryTheory Topology
open scoped Simplicial

universe u

namespace PreAbstractSimplicialComplex.SphereTriangulation

/-- The finite boundary complex on the original simplex labels. -/
@[expose]
def complex (n : ℕ) : PreAbstractSimplicialComplex (Fin (n + 1)) where
  faces := {s | s.Nonempty ∧ s ≠ Finset.univ}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, fun t hts ht => ⟨ht, ?_⟩⟩
    intro heq
    exact hs.2 (Finset.Subset.antisymm (Finset.subset_univ s) (heq ▸ hts))

/-- Finiteness of the actual nonempty proper face type is derived from its labels. -/
theorem finite_faces (n : ℕ) : Finite (Face (complex n)) := inferInstance

private theorem support_mem_iff (n : ℕ)
    (q : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    q.weights.support ∈ complex n ↔ ∃ i, q.weights i = 0 := by
  classical
  change q.weights.support.Nonempty ∧ q.weights.support ≠ Finset.univ ↔ _
  rw [and_iff_right q.support_weights_nonempty]
  constructor
  · intro h
    by_contra hz
    apply h
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Finsupp.mem_support_iff.mpr (fun hi => hz ⟨i, hi⟩)
  · rintro ⟨i, hi⟩ h
    have hm : i ∈ q.weights.support := h.symm ▸ Finset.mem_univ i
    exact Finsupp.mem_support_iff.mp hm hi

/-- The weak full simplex has its literal barycentric coordinate homeomorphism. -/
@[expose]
def fullSimplexHomeomorph (n : ℕ) :
    Realization (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) ≃ₜ
      Convexity.StdSimplex ℝ (Fin (n + 1)) where
  toFun x := x.point
  invFun q := ⟨q, q.support_weights_nonempty⟩
  left_inv x := Realization.ext rfl
  right_inv q := rfl
  continuous_toFun := Realization.continuous_point _
  continuous_invFun := by
    let s : Face (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) :=
      ⟨Finset.univ, ⟨0, Finset.mem_univ _⟩⟩
    let j : Fin (n + 1) → s.val := fun i => ⟨i, Finset.mem_univ _⟩
    have h : (fun q : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        (⟨q, q.support_weights_nonempty⟩ :
          Realization (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))))) =
        Realization.faceMap _ s ∘ Convexity.StdSimplex.map j := by
      funext q
      apply Realization.ext
      change q = (q.map j).map Subtype.val
      rw [← Convexity.StdSimplex.map_comp]
      exact (Convexity.StdSimplex.map_id q).symm
    rw [h]
    exact (Realization.continuous_faceMap _ s).comp
      (Convexity.StdSimplex.continuous_map ℝ j)

private theorem coordinates_isEmbedding (n : ℕ) :
    IsEmbedding (Realization.point (P := complex n)) := by
  exact (fullSimplexHomeomorph n).isEmbedding.comp
    (Realization.isClosedEmbedding_inclusion
      (show complex n ≤ (⊤ : PreAbstractSimplicialComplex (Fin (n + 1))) from le_top)).isEmbedding

private theorem coordinates_range (n : ℕ) :
    Set.range (Realization.point (P := complex n)) =
      Set.ofPred (fun q : Convexity.StdSimplex ℝ (Fin (n + 1)) => ∃ i, q.weights i = 0) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact (support_mem_iff n x.point).mp x.support_mem
  · intro hq
    exact ⟨⟨q, (support_mem_iff n q).mpr hq⟩, rfl⟩

/-- The weak boundary realization is exactly the standard simplex's zero-coordinate locus. -/
def coordinatesHomeomorph (n : ℕ) :
    Realization (complex n) ≃ₜ
      {q : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∃ i, q.weights i = 0} :=
  (coordinates_isEmbedding n).toHomeomorph.trans (Homeomorph.setCongr (coordinates_range n))


private theorem coordinatesHomeomorph_coe_impl (n : ℕ) (x : Realization (complex n)) :
    (coordinatesHomeomorph n x).val = x.point := rfl

/-- The boundary coordinate comparison retains the literal barycentric point. -/
@[simp]
theorem coordinatesHomeomorph_coe (n : ℕ) (x : Realization (complex n)) :
    (coordinatesHomeomorph n x).val = x.point := coordinatesHomeomorph_coe_impl n x

private theorem nativeBoundary_iff (n : ℕ)
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    x ∈ Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom ↔
      ∃ i, ((SimplexCategory.toTopHomeo.{u} ⦋n⦌) x).weights i = 0 := by
  constructor
  · exact SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange.{u} n x
  · rintro ⟨i, hi⟩
    have h := SSet.mem_realizedBoundary_of_zeroCoord.{u} n
      ((SimplexCategory.toTopHomeo.{u} ⦋n⦌) x) i hi
    simpa only [Homeomorph.symm_apply_apply] using h

private def nativeBoundaryCoordinatesHomeomorph (n : ℕ) :
    ↥(Set.range (SSet.toTop.map (SSet.boundary.{u} n).ι).hom) ≃ₜ
      {q : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∃ i, q.weights i = 0} :=
  (SimplexCategory.toTopHomeo.{u} ⦋n⦌).subtype (nativeBoundary_iff n)

private theorem nativeBoundary_isEmbedding (n : ℕ) :
    IsEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι).hom :=
  (TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.boundary.closedT1Embeddings_toTop_map_ι.{u} n)).isEmbedding

/-- The constructed finite weak boundary identifies with the actual realized simplex boundary. -/
def realizedBoundaryHomeomorph (n : ℕ) :
    Realization (complex n) ≃ₜ SSet.toTop.obj (SSet.boundary.{u} n) :=
  (coordinatesHomeomorph n).trans
    ((nativeBoundaryCoordinatesHomeomorph.{u} n).symm.trans
      (nativeBoundary_isEmbedding.{u} n).toHomeomorph.symm)

/-- The actual boundary inclusion retains the literal coordinates under the comparison. -/
theorem realizedBoundaryHomeomorph_map (n : ℕ) (x : Realization (complex n)) :
    (SSet.toTop.map (SSet.boundary.{u} n).ι).hom (realizedBoundaryHomeomorph.{u} n x) =
      (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm x.point := by
  let q := (nativeBoundaryCoordinatesHomeomorph.{u} n).symm (coordinatesHomeomorph n x)
  have h := (nativeBoundary_isEmbedding.{u} n).toHomeomorph.apply_symm_apply q
  exact congrArg Subtype.val h

private def sphereInClosedBallHomeomorph (n : ℕ) :
    {q : Metric.closedBall (0 : Fin n → ℝ) 1 //
      q.val ∈ Metric.sphere (0 : Fin n → ℝ) 1} ≃ₜ
      Metric.sphere (0 : Fin n → ℝ) 1 where
  toFun q := ⟨q.val.val, q.property⟩
  invFun q := ⟨⟨q.val, Metric.sphere_subset_closedBall q.property⟩, q.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def nativeBoundarySphereHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{0} n) ≃ₜ Metric.sphere (0 : Fin n → ℝ) 1 :=
  (nativeBoundary_isEmbedding.{0} n).toHomeomorph.trans
    (((SSet.stdSimplex.toClassicalDiskHomeomorph.{0} n).subtype
      (SSet.stdSimplex.toClassicalDiskHomeomorph_boundary_iff.{0} n)).trans
      (sphereInClosedBallHomeomorph n))

/-- The finite weak boundary sphere comparison restricts the chosen classical disk map. -/
def sphereHomeomorph (n : ℕ) :
    Realization (complex n) ≃ₜ Metric.sphere (0 : Fin n → ℝ) 1 :=
  (realizedBoundaryHomeomorph.{0} n).trans (nativeBoundarySphereHomeomorph n)

/-- The sphere identification has the original chosen disk gauge and actual coordinate map. -/
theorem sphereHomeomorph_coe (n : ℕ) (x : Realization (complex n)) :
    (sphereHomeomorph n x).val =
      (SSet.stdSimplex.toClassicalDiskHomeomorph.{0} n
        ((SimplexCategory.toTopHomeo.{0} ⦋n⦌).symm x.point)).val := by
  change (SSet.stdSimplex.toClassicalDiskHomeomorph.{0} n
    ((SSet.toTop.map (SSet.boundary.{0} n).ι).hom
      (realizedBoundaryHomeomorph.{0} n x))).val = _
  rw [realizedBoundaryHomeomorph_map]

/-- Dimension zero has no proper nonempty faces, actual vertices, realization points or sphere. -/
theorem zero_geometry :
    complex 0 = ⊥ ∧ IsEmpty (Face (complex 0)) ∧ IsEmpty (Vertex (complex 0)) ∧
      IsEmpty (Realization (complex 0)) ∧ IsEmpty (Metric.sphere (0 : Fin 0 → ℝ) 1) := by
  have hface : ∀ s : Finset (Fin 1), s ∉ complex 0 := by
    intro s hs
    change s.Nonempty ∧ s ≠ Finset.univ at hs
    obtain ⟨i, hi⟩ := hs.1
    apply hs.2
    apply Finset.Subset.antisymm (Finset.subset_univ _)
    intro j hj
    simpa only [Subsingleton.elim j i] using hi
  refine ⟨?_, ⟨fun s => hface s.val s.property⟩,
    ⟨fun v => hface {v.val} v.property⟩,
    ⟨fun x => hface x.point.weights.support x.support_mem⟩, ?_⟩
  · ext s
    exact iff_false_intro (hface s)
  · infer_instance

end PreAbstractSimplicialComplex.SphereTriangulation

end
