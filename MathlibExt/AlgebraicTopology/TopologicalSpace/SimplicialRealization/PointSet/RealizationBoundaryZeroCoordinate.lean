/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Realized simplex-boundary zero-coordinate lift (reverse direction)

For `n : ℕ` and `p : Convexity.StdSimplex ℝ (Fin (n + 1))`, if some
coordinate vanishes (`p.weights j = 0`) then the corresponding realized
point lies in the realized boundary: `(⦋n⦌.toTopHomeo).symm p ∈
Set.range (SSet.toTop.map (SSet.boundary n).ι)`.

This is the reverse zero-coordinate-to-boundary-range implication. The forward
implication is supplied separately by
`SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange` in `Boundary.lean`:
membership in the realized boundary range forces a zero barycentric coordinate.
Together they give the
iff used by the barycenter-complement radial retraction and
`TopPair.GoodPairData` for `( |Δ[n]|, |∂Δ[n]| )`; only the reverse is
proved here to avoid duplicating that public forward theorem.

Reuse map (all pinned, no new abstraction):
* `Convexity.StdSimplex.mem_range_map_iff` for the coordinate-to-face
  range step (`p` with `p.weights j = 0` lies in `map (Fin.succAbove j)`);
* `SSet.face_singleton_compl_le_boundary` for the face-to-boundary
  inclusion (the `j`-th leg of `SSet.boundary_eq_iSup`, cited here as
  the SSet presentation rather than re-proved);
* `SimplexCategory.toTopHomeo_symm_naturality_apply`,
  `SSet.stdSimplex.faceSingletonComplIso_hom_ι`, and
  `SSet.Subcomplex.homOfLE_ι` with `Functor.map_comp` for the
  realization transport (same idiom as `SSet.boundary.singleton_face_coord_zero`).
The coordinate-to-face consequence is proved directly via
`Convexity.StdSimplex.mem_range_map_iff`, without importing private
OpenCell or horn helpers.

Nonclaims: no horn substitution, no subdivision, no Kan filling, and no
model-category, fibration, or weak-equivalence result is asserted.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

/-- Reverse boundary lift: a zero coordinate forces realized-boundary
membership. Together with `SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange`
this is the `∃ zero ↔ ∈ range boundary` characterization. -/
theorem mem_realizedBoundary_of_zeroCoord (n : ℕ)
    (p : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : p.weights j = 0) :
    (⦋n⦌.toTopHomeo).symm p ∈
      Set.range ⇑(SSet.toTop.map (SSet.boundary.{u} n).ι) := by
  cases n with
  | zero =>
    exfalso
    have hsum := Convexity.StdSimplex.total_of_fintype p
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have huniv : (Finset.univ : Finset (Fin (0 + 1))) = {j} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim x j
    rw [huniv, Finset.sum_singleton] at hsum
    rw [hj] at hsum
    exact zero_ne_one hsum
  | succ m =>
    have hmem :
        p ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove j)) := by
      rw [Convexity.StdSimplex.mem_range_map_iff]
      intro y hy
      rw [Fin.range_succAbove] at hy
      have hyj : y = j := by simpa using hy
      rw [hyj]
      exact hj
    obtain ⟨q, hq⟩ := hmem
    let e := SSet.stdSimplex.faceSingletonComplIso (n := m) j
    have hδ_eq : (SSet.stdSimplex.δ (n := m) j : (Δ[m] : SSet.{u}) ⟶
        (Δ[m + 1] : SSet.{u})) =
        SSet.stdSimplex.map (SimplexCategory.δ (n := m) j) := rfl
    have hcoe : (⇑(SimplexCategory.δ (n := m) j) :
        Fin (m + 1) → Fin (m + 2)) = Fin.succAbove j := rfl
    have hsym : (⦋m + 1⦌.toTopHomeo).symm p =
        SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
          ((⦋m⦌.toTopHomeo).symm q) := by
      have hnat := SimplexCategory.toTopHomeo_symm_naturality_apply
        (f := SimplexCategory.δ (n := m) j) (x := q)
      rw [← hq]
      rw [hδ_eq]
      simpa [hcoe] using hnat
    have hface : SSet.toTop.map (SSet.stdSimplex.δ (n := m) j)
          ((⦋m⦌.toTopHomeo).symm q) =
        SSet.toTop.map (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι
          (SSet.toTop.map e.hom ((⦋m⦌.toTopHomeo).symm q)) := by
      have hEq : e.hom ≫ (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι =
          SSet.stdSimplex.δ (n := m) j :=
        SSet.stdSimplex.faceSingletonComplIso_hom_ι j
      have hEqTop : SSet.toTop.map (SSet.stdSimplex.δ (n := m) j) =
          SSet.toTop.map e.hom ≫
            SSet.toTop.map (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι := by
        rw [← hEq, Functor.map_comp]
      have h1 := ConcreteCategory.congr_hom hEqTop
        ((⦋m⦌.toTopHomeo).symm q)
      simpa [CategoryTheory.comp_apply] using h1
    have hle : SSet.stdSimplex.face (n := m + 1) {j}ᶜ ≤
        SSet.boundary.{u} (m + 1) :=
      SSet.face_singleton_compl_le_boundary j
    have hbound : SSet.toTop.map (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι
          (SSet.toTop.map e.hom ((⦋m⦌.toTopHomeo).symm q)) =
        SSet.toTop.map (SSet.boundary.{u} (m + 1)).ι
          (SSet.toTop.map (SSet.Subcomplex.homOfLE hle)
            (SSet.toTop.map e.hom ((⦋m⦌.toTopHomeo).symm q))) := by
      have hEq : SSet.Subcomplex.homOfLE hle ≫ (SSet.boundary.{u} (m + 1)).ι =
          (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι :=
        SSet.Subcomplex.homOfLE_ι hle
      have hEqTop : SSet.toTop.map
          (SSet.stdSimplex.face (n := m + 1) {j}ᶜ).ι =
          SSet.toTop.map (SSet.Subcomplex.homOfLE hle) ≫
            SSet.toTop.map (SSet.boundary.{u} (m + 1)).ι := by
        rw [← hEq, Functor.map_comp]
      have h1 := ConcreteCategory.congr_hom hEqTop
        (SSet.toTop.map e.hom ((⦋m⦌.toTopHomeo).symm q))
      simpa [CategoryTheory.comp_apply] using h1
    rw [hsym, hface, hbound]
    exact Set.mem_range_self _

end SSet
