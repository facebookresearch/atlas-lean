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
# Zero barycentric coordinates and realized simplex boundaries

A point of the standard simplex with a zero barycentric coordinate lies in
the realized boundary of `Δ[n]`. The proof uses
`Convexity.StdSimplex.mem_range_map_iff` to place it in the opposite face,
then transports the face inclusion through realization. Together with
`SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange`, this characterizes
boundary-range membership by the existence of a zero coordinate.
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
