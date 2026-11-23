/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCellInterior

/-!
# Realized 1-simplex open-cell regression

Concrete universe-zero client of
`SSet.realizationCellInterior.toTopIso_preimage_openCell_compl_range` at `n = 0`:
the barycenter `(1 / 2, 1 / 2)` lies in the open cell, hence outside the
realized-boundary range. A vertex with a zero coordinate lies outside the open cell.
-/

@[expose] public section

namespace SSet

/-- Barycenter of the topological 1-simplex. -/
noncomputable def cellInteriorBary1 : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.duple (0 : Fin 2) (1 : Fin 2) (s := (1 / 2 : ℝ))
    (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

/-- The barycenter has strictly positive coordinates. -/
theorem cellInteriorBary1_mem :
    cellInteriorBary1 ∈ SSet.realizationCellInterior.openCell 1 := by
  simp only [SSet.realizationCellInterior.openCell, Set.mem_ofPred_eq]
  have hw : ∀ i : Fin 2, cellInteriorBary1.weights i = (1 / 2 : ℝ) := by
    rw [Fin.forall_fin_two]
    constructor
    · have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      simp [cellInteriorBary1, Convexity.StdSimplex.weights_duple, h]
    · have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      simp [cellInteriorBary1, Convexity.StdSimplex.weights_duple, h]
  intro i
  rw [hw i]
  norm_num

/-- Source point above the barycenter, pinned to universe zero. -/
noncomputable def cellInteriorBary1Src :
    SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) :=
  (SimplexCategory.toTopHomeo (SimplexCategory.mk 1)).symm cellInteriorBary1

/-- The barycenter source lies outside the realized-boundary range. -/
theorem cellInteriorBary1Src_outside :
    cellInteriorBary1Src ∉ Set.range ⇑(SSet.toTop.map (SSet.boundary 1).ι) := by
  have hThm := SSet.realizationCellInterior.toTopIso_preimage_openCell_compl_range 0
  have hPre : cellInteriorBary1Src ∈
      (SSet.stdSimplex.toTopIso (SimplexCategory.mk 1)).hom ⁻¹'
        SSet.realizationCellInterior.openCell 1 := by
    rw [Set.mem_preimage]
    have hEq : (SSet.stdSimplex.toTopIso (SimplexCategory.mk 1)).hom
        cellInteriorBary1Src = cellInteriorBary1 :=
      Homeomorph.apply_symm_apply _ _
    rw [hEq]
    exact cellInteriorBary1_mem
  rw [hThm] at hPre
  simpa using hPre

/-- Vertex `(1, 0)` of the topological 1-simplex. -/
noncomputable def cellInteriorVertex1 : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.single (0 : Fin 2)

/-- The vertex has a zero coordinate, hence lies outside the open cell. -/
theorem cellInteriorVertex1_outside :
    cellInteriorVertex1 ∉ SSet.realizationCellInterior.openCell 1 := by
  simp only [SSet.realizationCellInterior.openCell, Set.mem_ofPred_eq]
  intro h
  have h1 := h (1 : Fin 2)
  have hNe : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  have hZero : cellInteriorVertex1.weights (1 : Fin 2) = 0 := by
    simp [cellInteriorVertex1, Convexity.StdSimplex.weights_single, hNe]
  rw [hZero] at h1
  norm_num at h1

/-- Unique point of the topological 0-simplex. -/
noncomputable def cellInteriorPt0 : Convexity.StdSimplex ℝ (Fin (0 + 1)) :=
  Convexity.StdSimplex.single (0 : Fin (0 + 1))

/-- The 0-simplex point lies in the open cell. -/
theorem cellInteriorPt0_mem :
    cellInteriorPt0 ∈ SSet.realizationCellInterior.openCell 0 := by
  simp only [SSet.realizationCellInterior.openCell, Set.mem_ofPred_eq]
  intro i
  have : Subsingleton (Fin (0 + 1)) := by rw [zero_add]; infer_instance
  have h1 : cellInteriorPt0.weights i = 1 :=
    Convexity.StdSimplex.weights_apply_eq_one _ _
  rw [h1]
  norm_num

/-- Source point above the 0-simplex point, pinned to universe zero. -/
noncomputable def cellInteriorPt0Src :
    SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{0}) :=
  (SimplexCategory.toTopHomeo (SimplexCategory.mk 0)).symm cellInteriorPt0

/-- The 0-simplex source lies outside the realized-boundary range. -/
theorem cellInteriorPt0Src_outside :
    cellInteriorPt0Src ∉ Set.range ⇑(SSet.toTop.map (SSet.boundary 0).ι) := by
  have hThm :=
    SSet.realizationCellInterior.toTopIso_preimage_openCell_compl_range_zero
  have hPre : cellInteriorPt0Src ∈
      (SSet.stdSimplex.toTopIso (SimplexCategory.mk 0)).hom ⁻¹'
        SSet.realizationCellInterior.openCell 0 := by
    rw [Set.mem_preimage]
    have hEq : (SSet.stdSimplex.toTopIso (SimplexCategory.mk 0)).hom
        cellInteriorPt0Src = cellInteriorPt0 :=
      Homeomorph.apply_symm_apply _ _
    rw [hEq]
    exact cellInteriorPt0_mem
  rw [hThm] at hPre
  simpa using hPre

#print axioms cellInteriorBary1_mem
#print axioms cellInteriorBary1Src_outside
#print axioms cellInteriorVertex1_outside
#print axioms cellInteriorPt0_mem
#print axioms cellInteriorPt0Src_outside

end SSet
