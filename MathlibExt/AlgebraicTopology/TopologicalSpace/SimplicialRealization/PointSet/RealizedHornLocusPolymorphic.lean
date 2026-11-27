/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Realized horn as an affine zero-coordinate locus

For `n > 0`, the standard realization homeomorphism sends the image of
`|Λ[n,k]| → |Δ[n]|` to the locus of simplex points with some zero coordinate
at an index different from `k`. This identifies the realized horn with that
locus by a homeomorphism, for arbitrary simplicial-set universe `u`.

The corresponding topological-category isomorphism uses the universe lift of
the finite-dimensional affine locus.
-/

@[expose] public section
universe u
open CategoryTheory
/--
Under the standard-simplex realization homeomorphism, the image of the
positive-dimensional horn is exactly `{x | ∃ j ≠ k, x_j = 0}`.
-/
theorem hornRange_image_eq_locus_u (n : ℕ) (k : Fin (n + 1))
    (hn : 0 < n) :
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
      Set.range (SSet.toTop.{u}.map (SSet.horn.{u} n k).ι) =
      {t : Convexity.StdSimplex ℝ (Fin (n + 1)) | ∃ j, j ≠ k ∧ t.weights j = 0} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  have hHorn := SSet.horn.toTop_map_ι_range_eq_iUnion m k
  have hFaceMem : ∀ (j : Fin (m + 2)) (t : Convexity.StdSimplex ℝ (Fin (m + 2))),
      t ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) ↔ t.weights j = 0 := by
    intro j t
    rw [Convexity.StdSimplex.mem_range_map_iff]
    constructor
    · intro h
      apply h j
      rw [Fin.range_succAbove]
      simp
    · intro h0 y hy
      have hmem : y ∈ ({j} : Set (Fin (m + 2))) := by
        by_contra hcon
        apply hy
        rw [Fin.range_succAbove, Set.mem_compl_iff]
        exact hcon
      rw [Set.mem_singleton_iff.mp hmem, h0]
  have hLocus : {t : Convexity.StdSimplex ℝ (Fin (m + 2)) | ∃ j, j ≠ k ∧ t.weights j = 0} =
      ⋃ (j : {j : Fin (m + 2) // j ≠ k}),
        Set.range (Convexity.StdSimplex.map (Fin.succAbove j.val)) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hjk, hj0⟩
      exact ⟨⟨j, hjk⟩, (hFaceMem j t).mpr hj0⟩
    · rintro ⟨⟨j, hjk⟩, hmem⟩
      exact ⟨j, hjk, (hFaceMem j t).mp hmem⟩
  have hFace : ∀ j : Fin (m + 2),
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1))) ''
        Set.range (SSet.toTop.{u}.map
          (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι)
        = Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) := by
    intro j
    let e := SSet.stdSimplex.faceSingletonComplIso.{u} (n := m) j
    have hHom : e.hom ≫ (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι
        = SSet.stdSimplex.δ.{u} (n := m) j :=
      SSet.stdSimplex.faceSingletonComplIso_hom_ι j
    have hFaceEq : (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι
        = e.inv ≫ SSet.stdSimplex.δ.{u} (n := m) j := by
      calc (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι
          = e.inv ≫ e.hom ≫ (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι := by
            simp
        _ = e.inv ≫ SSet.stdSimplex.δ.{u} (n := m) j := by rw [hHom]
    have hTopFace :
        SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι
          = SSet.toTop.{u}.map e.inv ≫
            SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j) := by
      rw [hFaceEq, CategoryTheory.Functor.map_comp]
    have hMapHom : SSet.toTop.{u}.map e.hom
          ≫ SSet.toTop.{u}.map (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι
        = SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j) := by
      rw [← CategoryTheory.Functor.map_comp, hHom]
    have hRangeFace :
        Set.range (SSet.toTop.{u}.map
            (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι)
          = Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j)) := by
      apply le_antisymm
      · rw [hTopFace, TopCat.coe_comp]
        exact Set.range_comp_subset_range _ _
      · rw [← hMapHom, TopCat.coe_comp]
        exact Set.range_comp_subset_range _ _
    have hNat : ∀ x,
        (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1)))
            (SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j) x)
          = (Convexity.StdSimplex.map (Fin.succAbove j))
            ((SimplexCategory.toTopHomeo (SimplexCategory.mk m)) x) := by
      intro x
      have hBridge : SSet.stdSimplex.map (SimplexCategory.δ (n := m) j)
          = SSet.stdSimplex.δ.{u} (n := m) j := rfl
      have h2 : (⇑(SimplexCategory.δ (n := m) j) : Fin (m + 1) → Fin (m + 2))
          = Fin.succAbove j := rfl
      have hPt :=
        SimplexCategory.toTopHomeo_naturality_apply
          (f := SimplexCategory.δ (n := m) j) x
      rw [← h2]
      rw [← hBridge]
      exact hPt
    have hImg : (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1))) ''
          Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j))
        = Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) := by
      ext t
      constructor
      · rintro ⟨y, ⟨x, hx⟩, hyt⟩
        refine ⟨(SimplexCategory.toTopHomeo (SimplexCategory.mk m)) x, ?_⟩
        have hEq : (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1)))
            (SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j) x) = t := by
          rw [hx, hyt]
        rw [hNat x] at hEq
        exact hEq
      · rintro ⟨s, hs⟩
        refine ⟨SSet.toTop.{u}.map (SSet.stdSimplex.δ.{u} (n := m) j)
          ((SimplexCategory.toTopHomeo (SimplexCategory.mk m)).symm s),
          ⟨_, rfl⟩, ?_⟩
        have hSym : (SimplexCategory.toTopHomeo (SimplexCategory.mk m))
            (((SimplexCategory.toTopHomeo (SimplexCategory.mk m)).symm s)) = s := by
          simp
        have hEq := hNat
          (((SimplexCategory.toTopHomeo (SimplexCategory.mk m)).symm s))
        rw [hSym] at hEq
        exact hEq.trans hs
    rw [hRangeFace]
    exact hImg
  ext t
  constructor
  · intro ht
    have htU : t ∈ (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1))) ''
        (⋃ (j : Fin (m + 2)) (hj : j ≠ k),
          Set.range (SSet.toTop.{u}.map
            (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι)) := by
      rw [← hHorn]
      exact ht
    obtain ⟨y, hy, hyt⟩ := htU
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨j, hj, x, hx⟩ := hy
    have hImgMem : t ∈ (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1))) ''
        Set.range (SSet.toTop.{u}.map
          (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι) :=
      ⟨y, Set.mem_range.mpr ⟨x, hx⟩, hyt⟩
    have hmem : t ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) := by
      rw [← hFace j]
      exact hImgMem
    rw [hLocus]
    simp only [Set.mem_iUnion]
    exact ⟨⟨j, hj⟩, hmem⟩
  · intro ht
    rw [hLocus] at ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨⟨j, hj⟩, hmem⟩ := ht
    have hmemI : t ∈ (SimplexCategory.toTopHomeo (SimplexCategory.mk (m + 1))) ''
        Set.range (SSet.toTop.{u}.map
          (SSet.stdSimplex.face.{u} (n := m + 1) {j}ᶜ).ι) := by
      rw [hFace j]
      exact hmem
    obtain ⟨y, hy, hyt⟩ := hmemI
    have hyHorn : y ∈ Set.range
        (SSet.toTop.{u}.map (SSet.horn.{u} (m + 1) k).ι) := by
      rw [hHorn]
      simp only [Set.mem_iUnion]
      exact ⟨j, hj, hy⟩
    exact ⟨y, hyHorn, hyt⟩

/--
For `n > 0`, the homeomorphism between the realized horn in universe `u`
and the affine locus with a zero coordinate at some index other than `k`.
-/
noncomputable def realizedHornHomeomorphHornLocus
    (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n) :
    ↥(SSet.toTop.{u}.obj (SSet.horn.{u} n k)) ≃ₜ
      ↥{t : Convexity.StdSimplex ℝ (Fin (n + 1)) |
        ∃ j, j ≠ k ∧ t.weights j = 0} :=
  ((TopCat.closedEmbeddings_iff _).mp
    (SSet.horn.closedEmbeddings_toTop_map_ι n k)).isEmbedding.toHomeomorph.trans
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).image _ |>.trans
      (Homeomorph.setCongr (hornRange_image_eq_locus_u n k hn)))

/--
For `n > 0`, the topological-category isomorphism from the realized horn to
the universe lift of its affine zero-coordinate locus.
-/
noncomputable def realizedHornIsoUliftHornLocus (n : ℕ) (k : Fin (n + 1))
    (hn : 0 < n) :
    SSet.toTop.{u}.obj (SSet.horn.{u} n k) ≅
      TopCat.uliftFunctor.obj (TopCat.of {t : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∃ j,
          j ≠ k ∧ t.weights j = 0}) :=
  TopCat.isoOfHomeo
    (((TopCat.closedEmbeddings_iff _).mp
      (SSet.horn.closedEmbeddings_toTop_map_ι n k)).isEmbedding.toHomeomorph.trans
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)).image _ |>.trans
        (Homeomorph.setCongr (hornRange_image_eq_locus_u n k hn) |>.trans
          ((TopCat.of {t : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∃ j,
              j ≠ k ∧ t.weights j = 0}).uliftFunctorObjHomeo))))
