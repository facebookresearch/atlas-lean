/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.FKCriticalAlgebra
import Code.BeffaraDC.Duality
import Code.Universality.STT

namespace StatMech.FrontierA


noncomputable def fkEdgeOdds (p : ℝ) : ℝ := p / (1 - p)


def triangularFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0 - q


def hexagonalFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 - q * (y0 + y1 + y2) - q ^ 2



theorem triangularFKCriticalSurface_diagonal (q y : ℝ) :
    triangularFKCriticalSurface q y y y = triangularFKCriticalPolynomial q y := by
  unfold triangularFKCriticalSurface triangularFKCriticalPolynomial
  ring



theorem hexagonalFKCriticalSurface_diagonal (q y : ℝ) :
    hexagonalFKCriticalSurface q y y y = hexagonalFKCriticalPolynomial q y := by
  unfold hexagonalFKCriticalSurface hexagonalFKCriticalPolynomial
  ring



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



theorem hexagonalFKCriticalSurface_of_dual_triangular
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (htri : triangularFKCriticalSurface q y0 y1 y2 = 0) :
    hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 := by
  have hid := trihex_dual_surface_identity h0 h1 h2
  rw [htri, mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left (mul_ne_zero (mul_ne_zero hy0 hy1) hy2)



theorem triangularFKCriticalSurface_of_dual_hexagonal
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hhex : hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 := by
  have hid := trihex_dual_surface_identity h0 h1 h2
  rw [hhex, mul_zero] at hid
  have hq2 : -(q ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hq)
  exact (mul_eq_zero.mp hid.symm).resolve_left hq2



theorem triangularFKCriticalSurface_iff_hexagonal_of_dual
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 ↔
      hexagonalFKCriticalSurface q y0Star y1Star y2Star = 0 :=
  ⟨hexagonalFKCriticalSurface_of_dual_triangular hy0 hy1 hy2 h0 h1 h2,
    triangularFKCriticalSurface_of_dual_hexagonal hq h0 h1 h2⟩



theorem triangularFKCriticalSurface_iff_hexagonal_div
    {q y0 y1 y2 : ℝ} (hq : q ≠ 0)
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) :
    triangularFKCriticalSurface q y0 y1 y2 = 0 ↔
      hexagonalFKCriticalSurface q (q / y0) (q / y1) (q / y2) = 0 := by
  apply triangularFKCriticalSurface_iff_hexagonal_of_dual hq hy0 hy1 hy2
  · field_simp
  · field_simp
  · field_simp





theorem fkEdgeOdds_mul_dualParam {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkEdgeOdds p * fkEdgeOdds (BeffaraDC.dualParam p q) = q := by
  exact BeffaraDC.dlt_dual_ratio_rel hp hp1 hq



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



private theorem triangular_surface_one_scaled {p0 p1 p2 : ℝ}
    (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    (1 - p0) * (1 - p1) * (1 - p2) *
        triangularFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) =
      Universality.kappaTri p0 p1 p2 := by
  unfold triangularFKCriticalSurface fkEdgeOdds Universality.kappaTri
  field_simp
  ring



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

private theorem hexagonal_surface_one_scaled {p0 p1 p2 : ℝ}
    (hp0 : p0 ≠ 1) (hp1 : p1 ≠ 1) (hp2 : p2 ≠ 1) :
    (1 - p0) * (1 - p1) * (1 - p2) *
        hexagonalFKCriticalSurface 1 (fkEdgeOdds p0) (fkEdgeOdds p1) (fkEdgeOdds p2) =
      Universality.kappaHex p0 p1 p2 := by
  unfold hexagonalFKCriticalSurface fkEdgeOdds Universality.kappaHex
    Universality.kappaTri
  field_simp
  ring



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
