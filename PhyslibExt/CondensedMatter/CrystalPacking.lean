/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
/-!
# Crystal structures and packing in the hard-sphere model

Atomic packing factors, theoretical density, explicit offset lists, ideal HCP
geometry, FCC interstitial holes, and radius-ratio thresholds, proved from
explicit conventional-cell geometry with hard-sphere touching relations as
hypotheses.

## i. Overview

All lengths are plain reals in one consistent unit. `R > 0` is an explicit
hypothesis wherever an atomic radius is used. Every hard-sphere touching
relation (touching along a cube edge, face diagonal, or body diagonal) is
carried as an explicit hypothesis on each lemma that uses it; no touching
relation is asserted as a standalone fact about nature. This module proves
packing formulas from explicit cell geometry (lattice parameters and atom
counts as hypotheses). It does not create a competing lattice/crystal
abstraction, does not claim a canonical crystal representation or space-group
classification, and does not prove densest packing (Kepler/Hales is referenced
only, never reproved). It does not prove coordination numbers either: the offset
lists in section B are explicit finsets whose cardinalities are computed, with no
statement connecting them to lattice positions, distances, or the complete set of
touching neighbors.

## ii. Key results

* `apf_simpleCubic`, `apf_bcc`, `apf_fcc`, `apf_hcp`, `apf_diamond`:
  atomic packing factors `π/6`, `π√3/8`, `π/(3√2)`, `π/(3√2)`, `π√3/16`
  within the hard-sphere model.
* `theoreticalDensity_eq`, `density_mat_c1`: the symbolic density formula
  and the MAT-C1 numeric instance.
* `fccFaceDiagonalOffsets_card`, `bccBodyDiagonalOffsets_card`,
  `diamondTetrahedralOffsets_card`, `scEdgeOffsets_card`: the listed offset sets
  have 12, 8, 4, 6 elements (cardinalities of explicit lists, not coordination
  numbers).
* `hcp_ideal_ratio`: ideal HCP `c/a = √(8/3)` via tetrahedron geometry.
* `fcc_octahedral_hole`, `fcc_tetrahedral_hole`: hole-radius ratios
  `√2 - 1`, `√(3/2) - 1` with certified decimals.
* `threshold_CN3`, `threshold_CN4`, `threshold_CN6`, `threshold_CN8`:
  radius-ratio thresholds as pure geometry (predictive use is empirical).

## iii. Table of contents

* Bounds: certified intervals for `√2`, `√3`, `√(3/2)` (`π` bounds come
  from Mathlib).
* A. Atomic packing factor.
* B. Theoretical density and offset lists.
* C. Ideal HCP ratio and FCC interstitial holes.
* D. Radius-ratio thresholds (geometry) and empirical predictive use.

## iv. References

* MIT OCW 3.012 Fundamentals of Materials Science (Fall 2005): crystal
  structures, packing, density, interstitials, radius ratios.
* Roadmap MAT-C1 capstone: synthetic density fixture (`a = 4 Å`, molar mass
  `64 g/mol`, 4 atoms per conventional cell).
-/

@[expose] public section

namespace CondensedMatter.CrystalPacking

/-! ## Certified irrational bounds -/

/-- Certified interval for `√2`, by squaring both sides. -/
lemma sqrt2_bounds : (1.4142 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1.4142 by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ 1.4143 by norm_num)]
    norm_num

/-- Certified interval for `√3`, by squaring both sides. -/
lemma sqrt3_bounds : (1.731 : ℝ) < Real.sqrt 3 ∧ Real.sqrt 3 < 1.733 := by
  constructor
  · rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1.731 by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (show (0 : ℝ) ≤ 3 by norm_num)
      (show (0 : ℝ) ≤ 1.733 by norm_num)]
    norm_num

/-- Certified interval for `√(3/2)`, by squaring both sides. -/
lemma sqrt32_bounds :
    (1.224 : ℝ) < Real.sqrt (3 / 2) ∧ Real.sqrt (3 / 2) < 1.226 := by
  constructor
  · rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1.224 by norm_num)]
    norm_num
  · rw [Real.sqrt_lt (show (0 : ℝ) ≤ 3 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1.226 by norm_num)]
    norm_num

/-! ## A. Atomic packing factor -/

/-- Atomic packing factor: `n` atoms per conventional cell, sphere radius `R`,
conventional-cell volume `Vc`. All lengths in one consistent unit. -/
noncomputable def atomicPackingFactor (n : ℕ) (R Vc : ℝ) : ℝ :=
  n * ((4 / 3) * Real.pi * R ^ 3) / Vc

/-- SC packing factor `π/6` from the edge-touching relation `a = 2R`. -/
lemma apf_simpleCubic (R a Vc : ℝ) (hR : 0 < R) (ha : a = 2 * R)
    (hVc : Vc = a ^ 3) :
    atomicPackingFactor 1 R Vc = Real.pi / 6 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2R3 : ((2 : ℝ) * R) ^ 3 ≠ 0 := pow_ne_zero 3 (mul_ne_zero h2ne hRne)
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  simp only [atomicPackingFactor, hVc, ha, Nat.cast_one, one_mul]
  rw [div_eq_div_iff h2R3 h6]
  ring

/-- BCC packing factor `π√3/8` from the body-diagonal touching relation. -/
lemma apf_bcc (R a Vc : ℝ) (hR : 0 < R)
    (h : 4 * R = Real.sqrt 3 * a) (hVc : Vc = a ^ 3) :
    atomicPackingFactor 2 R Vc = Real.pi * Real.sqrt 3 / 8 := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos
  have ha_eq : a = 4 * R / Real.sqrt 3 := by
    rw [eq_div_iff hs3ne]
    linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have ha_pos : 0 < a := by rw [ha_eq]; exact div_pos h4R hs3pos
  have hR_eq : R = Real.sqrt 3 * a / 4 := by rw [← h]; ring
  have hsq3 : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hcube3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    linear_combination Real.sqrt 3 * hsq3
  have hR3 : R ^ 3 = 3 * Real.sqrt 3 * a ^ 3 / 64 := by
    rw [hR_eq]
    linear_combination (a ^ 3 / 64) * hcube3
  have ha' : a ≠ 0 := ne_of_gt ha_pos
  have ha3 : (a : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 ha'
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  simp only [atomicPackingFactor, hVc, hR3, Nat.cast_ofNat]
  rw [div_eq_div_iff ha3 h8]
  ring

/-- FCC packing factor `π/(3√2)` from the face-diagonal touching relation. -/
lemma apf_fcc (R a Vc : ℝ) (hR : 0 < R)
    (h : 4 * R = Real.sqrt 2 * a) (hVc : Vc = a ^ 3) :
    atomicPackingFactor 4 R Vc = Real.pi / (3 * Real.sqrt 2) := by
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have ha_eq : a = 4 * R / Real.sqrt 2 := by
    rw [eq_div_iff hs2ne]
    linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have ha_pos : 0 < a := by rw [ha_eq]; exact div_pos h4R hs2pos
  have hR_eq : R = Real.sqrt 2 * a / 4 := by rw [← h]; ring
  have hsq2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcube2 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    linear_combination Real.sqrt 2 * hsq2
  have hR3 : R ^ 3 = Real.sqrt 2 * a ^ 3 / 32 := by
    rw [hR_eq]
    linear_combination (a ^ 3 / 64) * hcube2
  have ha' : a ≠ 0 := ne_of_gt ha_pos
  have ha3 : (a : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 ha'
  have h3s2 : (0 : ℝ) < 3 * Real.sqrt 2 := by linarith [hs2pos]
  have h3s2ne : (3 : ℝ) * Real.sqrt 2 ≠ 0 := ne_of_gt h3s2
  simp only [atomicPackingFactor, hVc, hR3, Nat.cast_ofNat]
  rw [div_eq_div_iff ha3 h3s2ne]
  linear_combination (Real.pi * a ^ 3 / 2) * hsq2

/-- HCP packing factor `π/(3√2)` (same value as FCC) for the hexagonal-prism
conventional cell, from basal-plane touching and the ideal ratio proved in
`hcp_ideal_ratio` (taken here as the hypothesis `hc`). -/
lemma apf_hcp (R a c Vc : ℝ) (hR : 0 < R) (ha : a = 2 * R)
    (hVc : Vc = (3 * Real.sqrt 3 / 2) * a ^ 2 * c)
    (hc : c = a * Real.sqrt (8 / 3)) :
    atomicPackingFactor 6 R Vc = Real.pi / (3 * Real.sqrt 2) := by
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have hs3ne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num))
  have ha_pos : (0 : ℝ) < a := by rw [ha]; linarith
  have hReq : R = a / 2 := by rw [ha]; ring
  have hR3 : R ^ 3 = a ^ 3 / 8 := by rw [hReq]; ring
  have h8eq : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [h8eq, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have h38 : (3 : ℝ) * (8 / 3) = 8 := by norm_num
  have hprod : Real.sqrt 3 * Real.sqrt (8 / 3) = 2 * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num), h38]
    exact hsqrt8
  have hVc_simp : (3 * Real.sqrt 3 / 2) * a ^ 2 * (a * Real.sqrt (8 / 3)) =
      3 * Real.sqrt 2 * a ^ 3 := by
    linear_combination (3 * a ^ 3 / 2) * hprod
  have ha' : a ≠ 0 := ne_of_gt ha_pos
  have h3s2 : (0 : ℝ) < 3 * Real.sqrt 2 := by linarith [hs2pos]
  have h3s2ne : (3 : ℝ) * Real.sqrt 2 ≠ 0 := ne_of_gt h3s2
  have hden : (3 : ℝ) * Real.sqrt 2 * a ^ 3 ≠ 0 :=
    mul_ne_zero h3s2ne (pow_ne_zero 3 ha')
  simp only [atomicPackingFactor, hVc, hc, hR3, Nat.cast_ofNat]
  rw [hVc_simp, div_eq_div_iff hden h3s2ne]
  ring

/-- Diamond packing factor `π√3/16` from the nearest-neighbour relation. -/
lemma apf_diamond (R a Vc : ℝ) (hR : 0 < R)
    (h : 8 * R = Real.sqrt 3 * a) (hVc : Vc = a ^ 3) :
    atomicPackingFactor 8 R Vc = Real.pi * Real.sqrt 3 / 16 := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos
  have ha_eq : a = 8 * R / Real.sqrt 3 := by
    rw [eq_div_iff hs3ne]
    linarith
  have h8R : (0 : ℝ) < 8 * R := by linarith
  have ha_pos : 0 < a := by rw [ha_eq]; exact div_pos h8R hs3pos
  have hR_eq : R = Real.sqrt 3 * a / 8 := by rw [← h]; ring
  have hsq3 : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hcube3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    linear_combination Real.sqrt 3 * hsq3
  have hR3 : R ^ 3 = 3 * Real.sqrt 3 * a ^ 3 / 512 := by
    rw [hR_eq]
    linear_combination (a ^ 3 / 512) * hcube3
  have ha' : a ≠ 0 := ne_of_gt ha_pos
  have ha3 : (a : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 ha'
  have h16 : (16 : ℝ) ≠ 0 := by norm_num
  simp only [atomicPackingFactor, hVc, hR3, Nat.cast_ofNat]
  rw [div_eq_div_iff ha3 h16]
  ring

/-! ## B. Theoretical density and offset lists -/

/-- Theoretical density: `n` atoms per cell, molar mass `A`, cell volume `Vc`,
Avogadro constant `NA`. All quantities are plain reals in consistent units. -/
noncomputable def theoreticalDensity (n A Vc NA : ℝ) : ℝ :=
  n * A / (Vc * NA)

/-- The symbolic density formula is exactly this definition. -/
lemma theoreticalDensity_eq (n A Vc NA : ℝ) :
    theoreticalDensity n A Vc NA = n * A / (Vc * NA) := rfl

/-- Unit conversion for the MAT-C1 fixture: `Vc = 4³ = 64 Å³` with
`1 Å = 1e-8 cm` gives `Vc = 64e-24 cm³`. -/
lemma angstrom_cubed_to_cm_cubed : (4 : ℝ) ^ 3 * (1e-8) ^ 3 = 64e-24 := by
  norm_num

/-- MAT-C1 numeric instance: with `a = 4` (Å), `n = 4`, `A = 64` (g/mol),
`Vc = 64e-24` (cm³), and `NA` the exact SI Avogadro constant, the density is
`6.64216 g/cm³` up to `0.001`. This is a synthetic fixture; it does not
identify a real metal. -/
lemma density_mat_c1 (NA : ℝ) (hNA : NA = 6.02214076e23) :
    |theoreticalDensity 4 64 (64e-24) NA - 6.64216| < 0.001 := by
  rw [hNA]
  unfold theoreticalDensity
  have hden : (64e-24 : ℝ) * 6.02214076e23 = 38.541700864 := by norm_num
  rw [hden]
  have hpos : (0 : ℝ) < 38.541700864 := by norm_num
  have hlo : (6.64116 : ℝ) < 4 * 64 / 38.541700864 := by
    rw [lt_div_iff₀ hpos]
    norm_num
  have hhi : (4 : ℝ) * 64 / 38.541700864 < 6.64316 := by
    rw [div_lt_iff₀ hpos]
    norm_num
  rw [abs_lt]
  constructor <;> linarith

/-- Unit conversion: a density `ρ` in g/cm³ equals `1000 * ρ` in kg/m³,
since `1 g = 1/1000 kg` and `1 cm³ = 1/1000000 m³`. -/
lemma density_unit_conversion (ρ : ℝ) :
    ρ * ((1 / 1000) / (1 / 1000000)) = 1000 * ρ := by
  have hfactor : ((1 / 1000 : ℝ) / (1 / 1000000)) = 1000 := by norm_num
  rw [hfactor]
  ring

/-- FCC face-diagonal offsets: the permutations of `(±1, ±1, 0)` in units of half
the cubic lattice parameter `a/2`, i.e. the half face diagonals of the
conventional cube. This is an explicit list only: no statement here connects it
to FCC atomic positions or distances, or claims that it is the set of touching
neighbors, so its cardinality (`fccFaceDiagonalOffsets_card`) is not a
coordination number. No space-group or classification result is claimed. -/
def fccFaceDiagonalOffsets : Finset (ℤ × ℤ × ℤ) :=
  {(1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0),
   (1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1),
   (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)}

/-- BCC body-diagonal offsets: `(±1, ±1, ±1)` in units of `a/2`, i.e. the half
body diagonals of the conventional cube. An explicit list only, as in
`fccFaceDiagonalOffsets`; its cardinality is not a coordination number. -/
def bccBodyDiagonalOffsets : Finset (ℤ × ℤ × ℤ) :=
  {(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1),
   (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)}

/-- Diamond tetrahedral offsets: `(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`,
`(-1,-1,1)` in units of `a/4`, quarter body diagonals pointing to the vertices of
a regular tetrahedron. An explicit list only, as in `fccFaceDiagonalOffsets`; its
cardinality is not a coordination number. -/
def diamondTetrahedralOffsets : Finset (ℤ × ℤ × ℤ) :=
  {(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)}

/-- SC edge offsets: the permutations of `(±2, 0, 0)` in units of `a/2`, i.e. the
cube edge vectors `(±a, 0, 0)`, `(0, ±a, 0)`, `(0, 0, ±a)`. An explicit list
only, as in `fccFaceDiagonalOffsets`; its cardinality is not a coordination
number. -/
def scEdgeOffsets : Finset (ℤ × ℤ × ℤ) :=
  {(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2)}

/-- The FCC face-diagonal offset list has 12 elements (a list cardinality, not a
coordination number). -/
lemma fccFaceDiagonalOffsets_card : fccFaceDiagonalOffsets.card = 12 := by decide

/-- The BCC body-diagonal offset list has 8 elements (a list cardinality, not a
coordination number). -/
lemma bccBodyDiagonalOffsets_card : bccBodyDiagonalOffsets.card = 8 := by decide

/-- The diamond tetrahedral offset list has 4 elements (a list cardinality, not a
coordination number). -/
lemma diamondTetrahedralOffsets_card : diamondTetrahedralOffsets.card = 4 := by decide

/-- The SC edge offset list has 6 elements (a list cardinality, not a
coordination number). -/
lemma scEdgeOffsets_card : scEdgeOffsets.card = 6 := by decide

/-! ## C. Ideal HCP ratio and FCC interstitial holes -/

/-- Squared centroid-to-vertex distance of the equilateral triangle of side
`a` with vertices `(0,0)`, `(a,0)`, `(a/2, a√3/2)` and centroid
`(a/2, a√3/6)`: `(a/2)² + (a√3/6)² = a²/3`. -/
lemma equilateral_centroid_sq (a : ℝ) :
    (a / 2) ^ 2 + (a * Real.sqrt 3 / 6) ^ 2 = a ^ 2 / 3 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination (a ^ 2 / 36) * hsq3

/-- Centroid-to-vertex distance of the equilateral triangle of side `a`
is `a/√3`, from the coordinate computation above. -/
lemma equilateral_centroid_dist (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((a / 2) ^ 2 + (a * Real.sqrt 3 / 6) ^ 2) =
      a / Real.sqrt 3 := by
  rw [equilateral_centroid_sq a, Real.sqrt_div (sq_nonneg a) 3,
    Real.sqrt_sq ha]

/-- Height of the regular tetrahedron of side `a`: with the apex above the
centroid of the equilateral-triangle base (the ideal-HCP model hypothesis
`hh_sq`), `h² = (2/3)a²` and `h = a√(2/3)` for `0 < a`. -/
lemma tetrahedron_height (a h : ℝ) (ha : 0 < a) (hh_nonneg : 0 ≤ h)
    (hh_sq : h ^ 2 = a ^ 2 - (a / Real.sqrt 3) ^ 2) :
    h ^ 2 = (2 / 3) * a ^ 2 ∧ h = a * Real.sqrt (2 / 3) := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hdiv : (a / Real.sqrt 3) ^ 2 = a ^ 2 / 3 := by
    rw [div_pow, hsq3]
  have h1 : h ^ 2 = (2 / 3) * a ^ 2 := by
    rw [hh_sq, hdiv]
    ring
  refine ⟨h1, ?_⟩
  have h2 : h = Real.sqrt (h ^ 2) := (Real.sqrt_sq hh_nonneg).symm
  rw [h1] at h2
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 / 3 by norm_num),
    Real.sqrt_sq ha.le] at h2
  rw [mul_comm] at h2
  exact h2

/-- Ideal HCP ratio `c/a = √(8/3)`: the `c` axis spans two regular
tetrahedra of side `a` (the ideal-HCP model hypothesis `hc`). -/
lemma hcp_ideal_ratio (a c h : ℝ) (ha : 0 < a)
    (hh : h = a * Real.sqrt (2 / 3)) (hc : c = 2 * h) :
    c / a = Real.sqrt (8 / 3) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have h83 : (8 / 3 : ℝ) = 2 ^ 2 * (2 / 3) := by norm_num
  have hsqrt83 : Real.sqrt (8 / 3) = 2 * Real.sqrt (2 / 3) := by
    rw [h83, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hc, hh, hsqrt83, div_eq_iff ha']
  ring

/-- FCC octahedral hole: with atom radius `R = a/(2√2)` (FCC touching) and
hole radius `r = a/2 - R`, `r/R = √2 - 1 ≈ 0.414`. -/
lemma fcc_octahedral_hole (a R r : ℝ) (ha : 0 < a)
    (hR : R = a / (2 * Real.sqrt 2)) (hr : r = a / 2 - R) :
    r / R = Real.sqrt 2 - 1 ∧ |r / R - 0.414| < 0.001 := by
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have ha' : a ≠ 0 := ne_of_gt ha
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2s : (2 : ℝ) * Real.sqrt 2 ≠ 0 := mul_ne_zero h2ne hs2ne
  have hRne : R ≠ 0 := by rw [hR]; exact div_ne_zero ha' h2s
  have hid : r / R = Real.sqrt 2 - 1 := by
    simp only [hr, hR]
    field_simp
  refine ⟨hid, ?_⟩
  rw [hid]
  have hb := sqrt2_bounds
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-- FCC tetrahedral hole: with atom radius `R = a/(2√2)` (FCC touching) and
hole radius `r = √3a/4 - R`, `r/R = √(3/2) - 1 ≈ 0.225`. -/
lemma fcc_tetrahedral_hole (a R r : ℝ) (ha : 0 < a)
    (hR : R = a / (2 * Real.sqrt 2))
    (hr : r = Real.sqrt 3 * a / 4 - R) :
    r / R = Real.sqrt (3 / 2) - 1 ∧ |r / R - 0.225| < 0.001 := by
  have hs2pos : 0 < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have ha' : a ≠ 0 := ne_of_gt ha
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have h2s : (2 : ℝ) * Real.sqrt 2 ≠ 0 := mul_ne_zero h2ne hs2ne
  have hRne : R ≠ 0 := by rw [hR]; exact div_ne_zero ha' h2s
  have hsq2 : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsd : Real.sqrt (3 / 2) = Real.sqrt 3 / Real.sqrt 2 :=
    Real.sqrt_div (show (0 : ℝ) ≤ 3 by norm_num) 2
  have hsplit : Real.sqrt 3 / Real.sqrt 2 =
      Real.sqrt 3 * Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff hs2ne h2ne]
    linear_combination -Real.sqrt 3 * hsq2
  have hsqrt32 : Real.sqrt (3 / 2) = Real.sqrt 3 * Real.sqrt 2 / 2 :=
    hsd.trans hsplit
  have hid : r / R = Real.sqrt (3 / 2) - 1 := by
    rw [hsqrt32]
    simp only [hr, hR]
    field_simp
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have hb := sqrt32_bounds
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-! ## D. Radius-ratio thresholds (geometry) and empirical predictive use

The thresholds below are geometry: each is proved from its stated geometric
configuration (hole center with `N` surrounding spheres of radius `R` at the
stated center distance, hole sphere of radius `r` touching all of them) taken
as hypotheses. Their PREDICTIVE use -- inferring a coordination number from
an observed radius ratio -- is EMPIRICAL: it is a rule of thumb, not a
theorem, and it fails when radii depend on coordination, when bonding is not
hard-sphere, or when `c/a` deviates from ideal. No lemma in this file claims
a predictive implication. The same element has different effective radii at
different coordinations, so a single `R` is a model input, not a physical
constant.

Non-goals: no Kepler/Hales densest-packing proof; no claim that real crystals
attain the ideal ratios.
-/

/-- Triangular-hole (`CN = 3`) threshold: `r/R = 2/√3 - 1 ≈ 0.155`. -/
lemma threshold_CN3 (R d r : ℝ) (hR : 0 < R)
    (hd : d = 2 * R / Real.sqrt 3) (hr : r = d - R) :
    r / R = 2 / Real.sqrt 3 - 1 ∧ |r / R - 0.155| < 0.001 := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt hs3pos
  have hRne : R ≠ 0 := ne_of_gt hR
  have hid : r / R = 2 / Real.sqrt 3 - 1 := by
    simp only [hr, hd]
    field_simp
  refine ⟨hid, ?_⟩
  rw [hid]
  have hb := sqrt3_bounds
  have hlo : (1.154 : ℝ) < 2 / Real.sqrt 3 := by
    rw [lt_div_iff₀ hs3pos]
    linarith [hb.2]
  have hhi : (2 : ℝ) / Real.sqrt 3 < 1.156 := by
    rw [div_lt_iff₀ hs3pos]
    linarith [hb.1]
  rw [abs_lt]
  constructor <;> linarith

/-- Tetrahedral-hole (`CN = 4`) threshold, derived from `fcc_tetrahedral_hole`:
`r/R = √(3/2) - 1 ≈ 0.225`. -/
lemma threshold_CN4 (a d R r : ℝ) (ha : 0 < a)
    (hR : R = a / (2 * Real.sqrt 2))
    (hd : d = Real.sqrt 3 * a / 4) (hr : r = d - R) :
    r / R = Real.sqrt (3 / 2) - 1 ∧ |r / R - 0.225| < 0.001 := by
  rw [hd] at hr
  exact fcc_tetrahedral_hole a R r ha hR hr

/-- Octahedral-hole (`CN = 6`) threshold, derived from `fcc_octahedral_hole`:
`r/R = √2 - 1 ≈ 0.414`. -/
lemma threshold_CN6 (a d R r : ℝ) (ha : 0 < a)
    (hR : R = a / (2 * Real.sqrt 2)) (hd : d = a / 2) (hr : r = d - R) :
    r / R = Real.sqrt 2 - 1 ∧ |r / R - 0.414| < 0.001 := by
  rw [hd] at hr
  exact fcc_octahedral_hole a R r ha hR hr

/-- Cubic-hole (`CN = 8`) threshold: from cube body-diagonal geometry
(center-to-corner `√3a/2`, corner spheres touching along the edge),
`r/R = √3 - 1 ≈ 0.732`. -/
lemma threshold_CN8 (R a d r : ℝ) (hR : 0 < R) (ha : a = 2 * R)
    (hd : d = Real.sqrt 3 * a / 2) (hr : r = d - R) :
    r / R = Real.sqrt 3 - 1 ∧ |r / R - 0.732| < 0.001 := by
  have hs3ne : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num))
  have hRne : R ≠ 0 := ne_of_gt hR
  have hid : r / R = Real.sqrt 3 - 1 := by
    simp only [hr, hd, ha]
    field_simp
  refine ⟨hid, ?_⟩
  rw [hid]
  have hb := sqrt3_bounds
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

end CondensedMatter.CrystalPacking
