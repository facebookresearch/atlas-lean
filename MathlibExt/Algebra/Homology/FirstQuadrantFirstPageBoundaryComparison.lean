/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageZeroBoundary

/-!
# Comparing the first-page boundary with the horizontal differential

The exactness-defined boundary cycle in the adjacent-column short exact
sequence is identified with the raw horizontal bicomplex representative.
After the previously computed untwisting sign is inserted, the adjacent
connecting homomorphism becomes `(-1)^(q+1)` times the horizontal homology
map in vertical degree `q`.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Supported-degree section of column `p` into complete filtration stage
`p`, using the direct zero-stage presentation and the natural positive-stage
presentation. -/
noncomputable def horizontalCompleteDirectColumnSupportedSection :
    (p q : ℕ) →
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) ⟶
        ((horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q)
  | 0, q => horizontalCompleteDirectColumnSectionComponent K 0 q
  | p + 1, q => horizontalCompleteSuccDirectColumnSection K p q

/-- In every column, the inverse cokernel comparison is the supported-degree
section followed by the cokernel projection. -/
theorem horizontalFirstPageCokernelIso_inv_f_supported (p q : ℕ) :
    (horizontalFirstPageCokernelIso K p).inv.f (-(p : ℤ) - q) =
      horizontalCompleteDirectColumnSupportedSection K p q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K p)).f
          (-(p : ℤ) - q) := by
  cases p with
  | zero =>
      exact horizontalFirstPageCokernelIso_inv_f_zero K q
  | succ p =>
      exact horizontalFirstPageCokernelIso_inv_f_succ K p q

/-- Uniform complete-stage boundary formula, including the edge from column
one to column zero. -/
theorem horizontalCompleteDirectColumnSupportedSection_d (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1))).d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      (horizontalDirectColumnCochainXIso K p q).inv ≫
      horizontalCompleteDirectColumnSupportedSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K p).f (-(p : ℤ) - q) := by
  cases p with
  | zero =>
      exact horizontalCompleteOneToZeroDirectColumnSection_d K q
  | succ p =>
      exact horizontalCompleteSuccDirectColumnSection_d K p q

/-- The supported target section followed by the next filtration map and the
middle cokernel projection is the left map of the adjacent short exact
sequence. -/
theorem horizontalCompleteDirectColumnSupportedSection_adjacent_f
    (p q : ℕ) :
    horizontalCompleteDirectColumnSupportedSection K p q ≫
        (horizontalFirstPageNextFiltrationMap K p).f (-(p : ℤ) - q) ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
          horizontalFirstPageNextFiltrationMap K p)).f (-(p : ℤ) - q) =
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) := by
  dsimp [horizontalFirstPageAdjacentDirectShortComplex,
    horizontalFirstPageAdjacentLeftIso,
    horizontalFirstPageAdjacentCokernelShortComplex,
    CategoryTheory.cokernelCompShortComplex]
  rw [horizontalFirstPageCokernelIso_inv_f_supported K p q]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f]
  rw [← HomologicalComplex.comp_f, cokernel.π_desc]

/-- The underlying raw horizontal representative between direct-column
presentations. -/
noncomputable def horizontalDirectColumnRawHorizontalRepresentative
    (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalDirectColumnCochain K (p + 1)).iCycles
      (-((p + 1 : ℕ) : ℤ) - q) ≫
    (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
    (K.d (p + 1) p).f q ≫
    (horizontalDirectColumnCochainXIso K p q).inv

/-- The differential of the canonical middle lift factors as the raw
horizontal representative followed by the left adjacent-sequence map. -/
theorem horizontalFirstPageAdjacentMiddleSection_d_eq_raw (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalFirstPageAdjacentMiddleSection K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) =
    horizontalDirectColumnRawHorizontalRepresentative K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) := by
  dsimp [horizontalFirstPageAdjacentMiddleSection]
  simp only [Category.assoc]
  change (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
        horizontalFirstPageNextFiltrationMap K p)).f
          (-((p + 1 : ℕ) : ℤ) - q) ≫
      (cokernel (horizontalFirstPageFiltrationMap K p ≫
        horizontalFirstPageNextFiltrationMap K p)).d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) = _
  have hπ := (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
    horizontalFirstPageNextFiltrationMap K p)).comm
      (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
  rw [hπ]
  rw [reassoc_of% horizontalCompleteDirectColumnSupportedSection_d K p q]
  dsimp [horizontalDirectColumnRawHorizontalRepresentative]
  rw [horizontalCompleteDirectColumnSupportedSection_adjacent_f K p q]
  simp only [Category.assoc]

/-- The exactness-defined adjacent boundary is the raw horizontal
representative. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_eq_raw (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q =
      horizontalDirectColumnRawHorizontalRepresentative K p q := by
  let S := horizontalFirstPageAdjacentDirectShortComplex K p
  let hS := horizontalFirstPageAdjacentDirectShortExact K p
  let _ := hS.mono_f
  have hm : Mono (S.f.f (-(p : ℤ) - q)) := by infer_instance
  let _ := hm
  apply (cancel_mono (S.f.f (-(p : ℤ) - q))).1
  change horizontalFirstPageAdjacentBoundaryCycles K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) =
    horizontalDirectColumnRawHorizontalRepresentative K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q)
  rw [horizontalFirstPageAdjacentBoundaryCycles_f]
  exact horizontalFirstPageAdjacentMiddleSection_d_eq_raw K p q

/-- The boundary representative is the signed transported horizontal cycle
representative. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_eq_horizontal (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        (horizontalDirectColumnHorizontalCyclesMap K p q ≫
          (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q)) := by
  rw [horizontalFirstPageAdjacentBoundaryCycles_eq_raw K p q]
  rw [horizontalDirectColumnHorizontalCyclesMap_iCycles K p q]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

/-- The canonical lift of the adjacent boundary to target cycles is the
signed transported horizontal cycles map. -/
theorem horizontalFirstPageAdjacentBoundaryLiftCycles_eq_horizontal
    (p q : ℕ) :
    (horizontalDirectColumnCochain K p).liftCycles
        (horizontalFirstPageAdjacentBoundaryCycles K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCycles_d K p q) =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalDirectColumnHorizontalCyclesMap K p q := by
  apply (cancel_mono
    ((horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q))).1
  rw [(horizontalDirectColumnCochain K p).liftCycles_i]
  simp only [Linear.units_smul_comp]
  exact horizontalFirstPageAdjacentBoundaryCycles_eq_horizontal K p q

/-- The connecting map on direct-column homology is the signed horizontal
homology map, conjugated by the direct-column homology identifications. -/
theorem horizontalFirstPageAdjacentConnectingMap_eq_horizontal
    (p q : ℕ) :
    horizontalFirstPageAdjacentConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        ((horizontalDirectColumnHomologyIso K (p + 1) q).hom ≫
          HomologicalComplex.homologyMap (K.d (p + 1) p) q ≫
          (horizontalDirectColumnHomologyIso K p q).inv) := by
  apply (cancel_epi ((horizontalDirectColumnCochain K (p + 1)).homologyπ
    (-((p + 1 : ℕ) : ℤ) - q))).1
  rw [horizontalFirstPageAdjacentConnectingMap_eq_boundaryCycles K p q]
  rw [horizontalFirstPageAdjacentBoundaryLiftCycles_eq_horizontal K p q]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  rw [horizontalDirectColumnHorizontalCyclesMap_homologyπ K p q]

/-- After transport to ordinary vertical homology, the adjacent first-page
connecting map is `(-1)^(q+1)` times the horizontal homology map. -/
theorem horizontalFirstPageAdjacentVerticalConnectingMap_eq_horizontal
    (p q : ℕ) :
    horizontalFirstPageAdjacentVerticalConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalFirstPageHorizontalHomologyMap K p q := by
  dsimp [horizontalFirstPageAdjacentVerticalConnectingMap,
    horizontalFirstPageHorizontalHomologyMap]
  rw [horizontalFirstPageAdjacentConnectingMap_eq_horizontal K p q]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  push_cast
  rfl

end HomologicalComplex₂

end
