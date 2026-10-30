/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalAlgebra
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.Duality
public import MathlibExt.Probability.Percolation.Universality.STT

/-!
# Critical surfaces of the inhomogeneous triangular and hexagonal random-cluster models

The star–triangle critical surfaces of the FK model on the triangular and hexagonal lattices with
three edge parameters, their exchange under planar duality, and their reduction to bond
percolation at `q = 1`.

## i. Overview

For cluster weight `q` and edge odds `yᵢ = pᵢ / (1 - pᵢ)` (`fkEdgeOdds`) on the three edge
directions, the triangular critical surface is
`y₀ y₁ y₂ + y₀ y₁ + y₁ y₂ + y₂ y₀ - q = 0` (`triangularFKCriticalSurface`) and the hexagonal one is
`y₀ y₁ y₂ - q (y₀ + y₁ + y₂) - q ^ 2 = 0` (`hexagonalFKCriticalSurface`); these are the surfaces on
which the star–triangle transformation maps one lattice to the other. On the diagonal they reduce
to the cubics of `CriticalAlgebra`. This file proves the algebraic identity
`y₀ y₁ y₂ · hex(q, y*) = -q ^ 2 · tri(q, y)` for dual odds `yᵢ yᵢ* = q`, hence the equivalence of
the two surfaces under the FK duality map `p ↦ dualParam p q`, and identifies both surfaces at
`q = 1` with the bond-percolation critical surfaces `κ_△ = 0` and `κ_⬡ = 0` of
`Universality.STT`. All results are unconditional algebra (with the stated range and
nonvanishing hypotheses). They do not prove that the surfaces are the phase boundaries of the FK
measures; that identification (Beffara–Duminil-Copin–Smirnov, Duminil-Copin–Li–Manolescu) is not
formalized here.

## ii. Key results

- `trihex_dual_surface_identity` : the polynomial identity linking the two surfaces under
  `yᵢ yᵢ* = q`. Unconditional.
- `triangularFKCriticalSurface_iff_hexagonal_dualParam` : for `pᵢ ∈ (0, 1)` and `q > 0`, the
  triangular surface holds at `p` iff the hexagonal surface holds at the dual parameters.
  Unconditional.
- `triangularFKCriticalSurface_one_iff_isCriticalTri`,
  `hexagonalFKCriticalSurface_one_iff_isCriticalHex` : at `q = 1` the surfaces are the
  bond-percolation star–triangle surfaces. Unconditional.

## iii. Table of contents

- A. Edge odds and the critical surfaces
- B. Duality of the critical surfaces
- C. Reduction to bond percolation at `q = 1`

## iv. References

- R. J. Baxter, H. N. V. Temperley and S. E. Ashley, *Triangular Potts model at its transition
  temperature, and related models*, Proc. R. Soc. Lond. A 358 (1978) 535–559.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
- J. C. Wierman, *Bond percolation on honeycomb and triangular lattices*, Adv. Appl. Probab. 13
  (1981) 298–313.
-/

@[expose] public section

namespace StatMech.FrontierA

/-! ## A. Edge odds and the critical surfaces -/

/-- The FK edge odds `p / (1 - p)` of an edge with parameter `p`. -/
noncomputable def fkEdgeOdds (p : ℝ) : ℝ := p / (1 - p)

/-- The triangular FK critical (star–triangle) surface `y₀ y₁ y₂ + y₀ y₁ + y₁ y₂ + y₂ y₀ - q` in the
three edge odds (Grimmett, *The Random-Cluster Model*, §6.6). -/
def triangularFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0 - q

/-- The hexagonal FK critical (star–triangle) surface `y₀ y₁ y₂ - q (y₀ + y₁ + y₂) - q ^ 2` in the
three edge odds (Grimmett, *The Random-Cluster Model*, §6.6). -/
def hexagonalFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 - q * (y0 + y1 + y2) - q ^ 2

lemma triangularFKCriticalSurface_diagonal (q y : ℝ) :
    triangularFKCriticalSurface q y y y = triangularFKCriticalPolynomial q y := by
  unfold triangularFKCriticalSurface triangularFKCriticalPolynomial
  ring

lemma hexagonalFKCriticalSurface_diagonal (q y : ℝ) :
    hexagonalFKCriticalSurface q y y y = hexagonalFKCriticalPolynomial q y := by
  unfold hexagonalFKCriticalSurface hexagonalFKCriticalPolynomial
  ring

/-! ## B. Duality of the critical surfaces -/

/-- Duality identity for the FK star–triangle surfaces: if `yᵢ yᵢ* = q` then `y₀ y₁ y₂ · hex(q, y*)
= -q ^ 2 · tri(q, y)` (Baxter–Temperley–Ashley 1978; Grimmett, *The Random-Cluster Model*, §6.6). -/
theorem trihex_dual_surface_identity {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q) :
    (y0 * y1 * y2) *
        hexagonalFKCriticalSurface q y0Star y1Star y2Star =
      -(q ^ 2) * triangularFKCriticalSurface q y0 y1 y2 := by
  unfold hexagonalFKCriticalSurface triangularFKCriticalSurface
  calc
    (y0 * y1 * y2) *
          (y0Star * y1Star * y2Star - q * (y0Star + y1Star + y2Star) - q ^ 2) =
        (y0 * y0Star) * (y1 * y1Star) * (y2 * y2Star) -
          q * ((y0 * y0Star) * y1 * y2 +
            (y1 * y1Star) * y2 * y0 + (y2 * y2Star) * y0 * y1) -
          q ^ 2 * (y0 * y1 * y2) := by ring
    _ = q ^ 3 - q * (q * y1 * y2 + q * y2 * y0 + q * y0 * y1) -
          q ^ 2 * (y0 * y1 * y2) := by rw [h0, h1, h2]; ring
    _ = -(q ^ 2) * (y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0 - q) := by
      ring

lemma hexagonalFKCriticalSurface_of_dual_triangular
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (htri : triangularFKCriticalSurface q y0 y1 y2 = 0) :
    hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 := by
  have hid := trihex_dual_surface_identity h0 h1 h2
  rw [htri, mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left (mul_ne_zero (mul_ne_zero hy0 hy1) hy2)

lemma triangularFKCriticalSurface_of_dual_hexagonal
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hhex : hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 := by
  have hid := trihex_dual_surface_identity h0 h1 h2
  rw [hhex, mul_zero] at hid
  have hq2 : -(q ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hq)
  exact (mul_eq_zero.mp hid.symm).resolve_left hq2

lemma triangularFKCriticalSurface_iff_hexagonal_of_dual
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 ↔
      hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 :=
  ⟨hexagonalFKCriticalSurface_of_dual_triangular hy0 hy1 hy2 h0 h1 h2,
    triangularFKCriticalSurface_of_dual_hexagonal hq h0 h1 h2⟩

lemma triangularFKCriticalSurface_iff_hexagonal_div
    {q y0 y1 y2 : ℝ} (hq : q ≠ 0)
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 ↔
      hexagonalFKCriticalSurface q (q / y0) (q / y1) (q / y2) = 0 := by
  apply triangularFKCriticalSurface_iff_hexagonal_of_dual hq hy0 hy1 hy2
  · field_simp
  · field_simp
  · field_simp

/-- The FK duality relation `y(p) · y(p*) = q` for the edge odds. See also
`BeffaraDC.dlt_dual_ratio_rel` (same statement with `fkEdgeOdds` unfolded). -/
lemma fkEdgeOdds_mul_dualParam {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkEdgeOdds p * fkEdgeOdds (BeffaraDC.dualParam p q) = q := by
  exact BeffaraDC.dlt_dual_ratio_rel hp hp1 hq

/-- Triangular–hexagonal duality of the inhomogeneous FK critical surfaces: for `pᵢ ∈ (0, 1)` and `q
> 0`, the triangular surface holds at `(p₀, p₁, p₂)` iff the hexagonal surface holds at the dual
parameters `dualParam pᵢ q` (Grimmett, *The Random-Cluster Model*, §6.6). -/
theorem triangularFKCriticalSurface_iff_hexagonal_dualParam
    {p0 p1 p2 q : ℝ}
    (hp0 : p0 ∈ Set.Ioo (0 : ℝ) 1) (hp1 : p1 ∈ Set.Ioo (0 : ℝ) 1)
    (hp2 : p2 ∈ Set.Ioo (0 : ℝ) 1) (hq : 0 < q) :
    triangularFKCriticalSurface q (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔
      hexagonalFKCriticalSurface q
        (fkEdgeOdds (BeffaraDC.dualParam p0 q))
        (fkEdgeOdds (BeffaraDC.dualParam p1 q))
        (fkEdgeOdds (BeffaraDC.dualParam p2 q)) = 0 := by
  apply triangularFKCriticalSurface_iff_hexagonal_of_dual
    (ne_of_gt hq)
  · exact div_ne_zero (ne_of_gt hp0.1) (by linarith [hp0.2])
  · exact div_ne_zero (ne_of_gt hp1.1) (by linarith [hp1.2])
  · exact div_ne_zero (ne_of_gt hp2.1) (by linarith [hp2.2])
  · exact fkEdgeOdds_mul_dualParam hp0.1 hp0.2 hq
  · exact fkEdgeOdds_mul_dualParam hp1.1 hp1.2 hq
  · exact fkEdgeOdds_mul_dualParam hp2.1 hp2.2 hq

/-! ## C. Reduction to bond percolation at `q = 1` -/

private lemma triangular_surface_one_scaled {p0 p1 p2 : ℝ}
    (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    (1 - p0) * (1 - p1) * (1 - p2) *
        triangularFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) =
      Universality.kappaTri p0 p1 p2 := by
  unfold triangularFKCriticalSurface fkEdgeOdds Universality.kappaTri
  field_simp
  ring

/-- At `q = 1` the triangular FK critical surface is the bond-percolation star–triangle surface
`κ_△(p₀, p₁, p₂) = 0` (Wierman 1981; Grimmett, *Percolation*, §11.9). -/
theorem triangularFKCriticalSurface_one_iff_isCriticalTri
    {p0 p1 p2 : ℝ} (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    triangularFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔
      Universality.IsCriticalTri p0 p1 p2 := by
  rw [Universality.IsCriticalTri]
  have hscale := triangular_surface_one_scaled hp0 hp1 hp2
  constructor
  · intro h
    rw [h, mul_zero] at hscale
    exact hscale.symm
  · intro h
    rw [h] at hscale
    have hfactor : (1 - p0) * (1 - p1) * (1 - p2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hp0.symm) (sub_ne_zero.mpr hp1.symm))
        (sub_ne_zero.mpr hp2.symm)
    exact (mul_eq_zero.mp hscale).resolve_left hfactor

private lemma hexagonal_surface_one_scaled {p0 p1 p2 : ℝ}
    (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    (1 - p0) * (1 - p1) * (1 - p2) *
        hexagonalFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) =
      Universality.kappaHex p0 p1 p2 := by
  unfold hexagonalFKCriticalSurface fkEdgeOdds Universality.kappaHex
    Universality.kappaTri
  field_simp
  ring

/-- At `q = 1` the hexagonal FK critical surface is the bond-percolation star–triangle surface
`κ_⬡(p₀, p₁, p₂) = 0` (Wierman 1981; Grimmett, *Percolation*, §11.9). -/
theorem hexagonalFKCriticalSurface_one_iff_isCriticalHex
    {p0 p1 p2 : ℝ} (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    hexagonalFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) = 0 ↔
      Universality.IsCriticalHex p0 p1 p2 := by
  rw [Universality.IsCriticalHex]
  have hscale := hexagonal_surface_one_scaled hp0 hp1 hp2
  constructor
  · intro h
    rw [h, mul_zero] at hscale
    exact hscale.symm
  · intro h
    rw [h] at hscale
    have hfactor : (1 - p0) * (1 - p1) * (1 - p2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hp0.symm) (sub_ne_zero.mpr hp1.symm))
        (sub_ne_zero.mpr hp2.symm)
    exact (mul_eq_zero.mp hscale).resolve_left hfactor

end StatMech.FrontierA
