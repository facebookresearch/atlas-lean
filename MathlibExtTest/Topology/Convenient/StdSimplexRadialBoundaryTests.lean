/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Convenient.StdSimplexRadialBoundary

@[expose] public section

/-!
# Focused radial-boundary regression tests

Concrete public-API checks for `StdSimplexRadialBoundary` addressing review
finding 2: a `(1 / 4, 3 / 4)` interior point of `Fin 2` whose radial image is
the expected boundary vertex, a boundary vertex with an explicit zero
coordinate fixed by the radial and homotopy maps, and the degree-zero fact
that the `Fin 1` barycenter complement is empty.

Reuse map (exact base `c92193887a0772730f7d1d48de502acfdc592719`):
- `StdSimplexRadialBoundary.radialMap`, `homotopyPoint`, `radialCoord`,
  `radMin`, `radDenom`, `radMin_le`, `radialMem`, `radial_id_of_has_zero`
  (`MathlibExt/Topology/Convenient/StdSimplexRadialBoundary.lean`): `reuse`.
- Companion `radialMap_weights` (`@[simp]` weights equation),
  `radialMap_eq_of_has_zero`, `homotopyPoint_eq_of_has_zero`
  (same provider, companion-owned): `reuse` as black box, never restated.
- `Convexity.StdSimplex.duple`, `single`, `weights_duple`, `weights_single`,
  `weights_barycenter_apply`, `ext`, `total_of_fintype` (pinned Mathlib): `reuse`.
- `Fin.forall_fin_two`, `fin_cases`, `Fintype.card_fin`, `Fin.sum_univ_one`,
  `Finset.le_inf'` (pinned Mathlib): `reuse`.
- Point/inequality/`decide` and `norm_num` idioms from
  `StdSimplexMinimalFaceTests` and `SSetRealizationCellInteriorTests`: `reuse`.
- No `generalize` or `local` entry: this file adds only concrete regression examples.

Nonclaims: no realized-boundary map, no global chart, no fibration,
no model-category result.
-/

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.Topology.Convenient.StdSimplexRadialBoundaryTests

open scoped unitInterval

/-- Concrete interior point `(1 / 4, 3 / 4)` in `Fin 2`. -/
noncomputable def pQuarter : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.duple (0 : Fin 2) (1 : Fin 2) (s := (1 / 4 : ℝ))
    (t := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

/-- First coordinate of `pQuarter`. -/
theorem pQuarter_weights_zero : pQuarter.weights 0 = (1 / 4 : ℝ) := by
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  simp [pQuarter, Convexity.StdSimplex.weights_duple, h]

/-- Second coordinate of `pQuarter`. -/
theorem pQuarter_weights_one : pQuarter.weights 1 = (3 / 4 : ℝ) := by
  have h : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  simp [pQuarter, Convexity.StdSimplex.weights_duple, h]

/-- The barycenter of `Fin 2` has coordinate `1 / 2`. -/
theorem bary2_weights_zero :
    (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 2)).weights 0 =
      (1 / 2 : ℝ) := by
  rw [Convexity.StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  norm_num

/-- `pQuarter` is not the barycenter. -/
theorem pQuarter_ne_bary :
    pQuarter ≠ (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 2)) := by
  intro hEq
  have h1 := pQuarter_weights_zero
  have h2 := bary2_weights_zero
  rw [hEq] at h1
  rw [h2] at h1
  norm_num at h1

/-- Minimum coordinate of `pQuarter` is `1 / 4`. -/
theorem pQuarter_radMin :
    StdSimplexRadialBoundary.radMin 1 pQuarter = (1 / 4 : ℝ) := by
  apply le_antisymm
  · calc StdSimplexRadialBoundary.radMin 1 pQuarter
        ≤ pQuarter.weights 0 :=
          StdSimplexRadialBoundary.radMin_le 1 pQuarter 0
      _ = (1 / 4 : ℝ) := pQuarter_weights_zero
  · apply Finset.le_inf'
    intro i _
    fin_cases i
    · change (1 / 4 : ℝ) ≤ pQuarter.weights 0
      simp [pQuarter_weights_zero]
    · change (1 / 4 : ℝ) ≤ pQuarter.weights 1
      simpa [pQuarter_weights_one] using (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)

/-- Radial denominator at `pQuarter` is `1 / 2`. -/
theorem pQuarter_radDenom :
    StdSimplexRadialBoundary.radDenom 1 pQuarter = (1 / 2 : ℝ) := by
  unfold StdSimplexRadialBoundary.radDenom
  rw [pQuarter_radMin]
  norm_num

/-- First radial coordinate of `pQuarter` is `0`. -/
theorem pQuarter_radialCoord_zero :
    StdSimplexRadialBoundary.radialCoord 1 pQuarter 0 = 0 := by
  unfold StdSimplexRadialBoundary.radialCoord
  rw [pQuarter_weights_zero, pQuarter_radMin, pQuarter_radDenom]
  norm_num

/-- Second radial coordinate of `pQuarter` is `1`. -/
theorem pQuarter_radialCoord_one :
    StdSimplexRadialBoundary.radialCoord 1 pQuarter 1 = 1 := by
  unfold StdSimplexRadialBoundary.radialCoord
  rw [pQuarter_weights_one, pQuarter_radMin, pQuarter_radDenom]
  norm_num

/-- The radial image of `pQuarter` is the expected boundary vertex. -/
theorem pQuarter_radial_eq_single :
    StdSimplexRadialBoundary.radialMap 1 ⟨pQuarter, pQuarter_ne_bary⟩ =
      Convexity.StdSimplex.single (1 : Fin 2) := by
  apply Convexity.StdSimplex.ext
  ext i
  fin_cases i
  · change (StdSimplexRadialBoundary.radialMap 1 ⟨pQuarter, pQuarter_ne_bary⟩).weights 0 =
      (Convexity.StdSimplex.single (1 : Fin 2)).weights 0
    have hL : (StdSimplexRadialBoundary.radialMap 1 ⟨pQuarter, pQuarter_ne_bary⟩).weights 0 =
        StdSimplexRadialBoundary.radialCoord 1 pQuarter 0 :=
        StdSimplexRadialBoundary.radialMap_weights 1 ⟨pQuarter, pQuarter_ne_bary⟩ 0
    have hR : (Convexity.StdSimplex.single (R := ℝ) (1 : Fin 2)).weights (0 : Fin 2) = 0 := by
      have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      simp [Convexity.StdSimplex.weights_single, h]
    rw [hL, pQuarter_radialCoord_zero]
    exact hR.symm
  · change (StdSimplexRadialBoundary.radialMap 1 ⟨pQuarter, pQuarter_ne_bary⟩).weights 1 =
      (Convexity.StdSimplex.single (1 : Fin 2)).weights 1
    have hL : (StdSimplexRadialBoundary.radialMap 1 ⟨pQuarter, pQuarter_ne_bary⟩).weights 1 =
        StdSimplexRadialBoundary.radialCoord 1 pQuarter 1 :=
        StdSimplexRadialBoundary.radialMap_weights 1 ⟨pQuarter, pQuarter_ne_bary⟩ 1
    have hR : (Convexity.StdSimplex.single (R := ℝ) (1 : Fin 2)).weights (1 : Fin 2) = 1 := by
      simp [Convexity.StdSimplex.weights_single]
    rw [hL, pQuarter_radialCoord_one]
    exact hR.symm

/-- Boundary vertex `(0, 1)` with an explicit zero at `0`. -/
noncomputable def vBdry : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.single (1 : Fin 2)

/-- The vertex has a zero coordinate. -/
theorem vBdry_has_zero : vBdry.weights 0 = 0 := by
  have h : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  simp [vBdry, Convexity.StdSimplex.weights_single, h]

/-- The vertex second coordinate is `1`. -/
theorem vBdry_weights_one : vBdry.weights 1 = 1 := by
  simp [vBdry, Convexity.StdSimplex.weights_single]

/-- The boundary vertex is not the barycenter. -/
theorem vBdry_ne_bary :
    vBdry ≠ (Convexity.StdSimplex.barycenter : Convexity.StdSimplex ℝ (Fin 2)) := by
  intro hEq
  have h1 := vBdry_has_zero
  have h2 := bary2_weights_zero
  rw [hEq] at h1
  rw [h2] at h1
  norm_num at h1

/-- The boundary vertex is fixed by the radial map. -/
theorem vBdry_radial_fixed :
    StdSimplexRadialBoundary.radialMap 1 ⟨vBdry, vBdry_ne_bary⟩ = vBdry :=
  StdSimplexRadialBoundary.radialMap_eq_of_has_zero 1 ⟨vBdry, vBdry_ne_bary⟩ 0
    vBdry_has_zero

/-- The boundary vertex is fixed by the homotopy at every `t`. -/
theorem vBdry_homotopy_fixed (t : I) :
    StdSimplexRadialBoundary.homotopyPoint 1 t vBdry vBdry_ne_bary = vBdry :=
  StdSimplexRadialBoundary.homotopyPoint_eq_of_has_zero 1 t ⟨vBdry, vBdry_ne_bary⟩ 0
    vBdry_has_zero

/-- The `Fin 1` simplex has no point away from its barycenter. -/
instance fin1_complement_empty :
    IsEmpty { x : Convexity.StdSimplex ℝ (Fin 1) //
      x ≠ Convexity.StdSimplex.barycenter } where
  false := by
    rintro ⟨x, hx⟩
    exact hx (Subsingleton.elim x _)

#print axioms pQuarter_radial_eq_single
#print axioms vBdry_radial_fixed
#print axioms vBdry_homotopy_fixed
#print axioms fin1_complement_empty

end MathlibExtTest.Topology.Convenient.StdSimplexRadialBoundaryTests
