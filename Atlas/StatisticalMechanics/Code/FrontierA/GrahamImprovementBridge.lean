/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.GrahamCorrections
import Code.Sharpness.GHSUnconditional

open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness
open StatMech.Walls StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def grahamGhostLeadingRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  -2 * onePt G beta h i * onePt G beta h j * onePt G beta h k


noncomputable def grahamImprovedGHSRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  -2 * cov2 G beta h i k * cov2 G beta h j k * onePt G beta h k



noncomputable def grahamGhostCorrectedRHS (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) : ℝ :=
  grahamGhostLeadingRHS G beta h i j k + grahamImprovedGHSRHS G beta h i j k


theorem grahamCov2_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (x y : V) :
    cov2 G beta h x y = cov2 G beta h y x := by
  unfold cov2
  have hxy : (fun s : ConfigSpace V => spin s x * spin s y) =
      (fun s => spin s y * spin s x) := by
    funext s
    ring
  rw [hxy]
  ring


theorem grahamCov2_self (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (x : V) :
    cov2 G beta h x x = 1 - onePt G beta h x ^ 2 := by
  unfold cov2 onePt
  rw [expectation_spin_mul_self]
  ring



theorem grahamCov2_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (x y : V) :
    0 ≤ cov2 G beta h x y := by
  by_cases hxy : x = y
  · subst y
    rw [grahamCov2_self]
    have hmNonneg : 0 ≤ onePt G beta h x :=
      expectation_spin_nonneg G beta h hbeta hh x
    have hmLe : onePt G beta h x ≤ 1 := expectation_spin_le_one G beta h x
    nlinarith
  · exact cov2_nonneg G beta h hbeta hh x y hxy


theorem grahamImprovedGHSRHS_nonpos (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (i j k : V) :
    grahamImprovedGHSRHS G beta h i j k ≤ 0 := by
  have hik := grahamCov2_nonneg G beta h hbeta hh i k
  have hjk := grahamCov2_nonneg G beta h hbeta hh j k
  have hmk : 0 ≤ onePt G beta h k := expectation_spin_nonneg G beta h hbeta hh k
  unfold grahamImprovedGHSRHS
  nlinarith [mul_nonneg (mul_nonneg hik hjk) hmk]



theorem grahamGhostCorrectedRHS_le_leading
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (i j k : V) :
    grahamGhostCorrectedRHS G beta h i j k ≤
      grahamGhostLeadingRHS G beta h i j k := by
  unfold grahamGhostCorrectedRHS
  linarith [grahamImprovedGHSRHS_nonpos G beta h hbeta hh i j k]



theorem grahamGhostFourPoint_iff_improvedGHS
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i j k : V) :
    gc_lebowitzU4 G beta h i j k ≤ grahamGhostCorrectedRHS G beta h i j k ↔
      eg_ursell3 G beta h i j k ≤ grahamImprovedGHSRHS G beta h i j k := by
  have hid := gc_ursell_eq_lebowitz_plus_triple G beta h i j k
  unfold grahamGhostCorrectedRHS grahamGhostLeadingRHS
  unfold onePt
  constructor <;> intro hineq <;> linarith



theorem grahamGhostLeadingBound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (i j k : V) :
    gc_lebowitzU4 G beta h i j k ≤ grahamGhostLeadingRHS G beta h i j k := by
  have hu : eg_ursell3 G beta h i j k ≤ 0 :=
    gc_ursell_nonpos_of_signDominance G beta h hbeta hh i
      (ghs_signDominance G beta h hbeta hh i) j k
  have hid := gc_ursell_eq_lebowitz_plus_triple G beta h i j k
  unfold grahamGhostLeadingRHS onePt
  linarith



theorem grahamImprovedGHS_zero_field
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 ≤ beta) (i j k : V) :
    eg_ursell3 G beta 0 i j k ≤ grahamImprovedGHSRHS G beta 0 i j k := by
  have hu : eg_ursell3 G beta 0 i j k ≤ 0 :=
    gc_ursell_nonpos_of_signDominance G beta 0 hbeta le_rfl i
      (ghs_signDominance G beta 0 hbeta le_rfl i) j k
  have hmk : onePt G beta 0 k = 0 := magnetization_zero_field G beta k
  unfold grahamImprovedGHSRHS
  rw [hmk, mul_zero]
  exact hu



theorem grahamGhostCorrectedBound_zero_field
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 ≤ beta) (i j k : V) :
    gc_lebowitzU4 G beta 0 i j k ≤ grahamGhostCorrectedRHS G beta 0 i j k := by
  rw [grahamGhostFourPoint_iff_improvedGHS]
  exact grahamImprovedGHS_zero_field G beta hbeta i j k



theorem grahamUrsell3_last_repeated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (i k : V) :
    eg_ursell3 G beta h i k k =
      -2 * onePt G beta h k * cov2 G beta h i k := by
  unfold eg_ursell3 cov2 onePt
  have hfirst : isingExpectation G beta h
      (fun s => spin s i * (spin s k * spin s k)) =
        isingExpectation G beta h (fun s => spin s i) := by
    congr 1
    funext s
    rw [spin_sq, mul_one]
  have hpair : isingExpectation G beta h
      (fun s => spin s k * spin s k) = 1 :=
    expectation_spin_mul_self G beta h k
  rw [hfirst, hpair]
  ring


theorem grahamImprovedGHS_right_pivot
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (i k : V) :
    eg_ursell3 G beta h i k k ≤ grahamImprovedGHSRHS G beta h i k k := by
  rw [grahamUrsell3_last_repeated]
  unfold grahamImprovedGHSRHS
  rw [grahamCov2_self]
  have hmNonneg : 0 ≤ onePt G beta h k :=
    expectation_spin_nonneg G beta h hbeta hh k
  have hmLe : onePt G beta h k ≤ 1 := expectation_spin_le_one G beta h k
  have hc := grahamCov2_nonneg G beta h hbeta hh i k
  nlinarith [mul_nonneg (pow_nonneg hmNonneg 3) hc]


theorem grahamImprovedGHS_left_pivot
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (j k : V) :
    eg_ursell3 G beta h k j k ≤ grahamImprovedGHSRHS G beta h k j k := by
  rw [ghc_ursell_swap]
  rw [ghc_ursell_degenerate]
  unfold grahamImprovedGHSRHS
  rw [grahamCov2_self, grahamCov2_comm G beta h j k]
  have hmNonneg : 0 ≤ onePt G beta h k :=
    expectation_spin_nonneg G beta h hbeta hh k
  have hmLe : onePt G beta h k ≤ 1 := expectation_spin_le_one G beta h k
  have hc := grahamCov2_nonneg G beta h hbeta hh k j
  change -2 * onePt G beta h k * cov2 G beta h k j ≤
    -2 * (1 - onePt G beta h k ^ 2) * cov2 G beta h k j * onePt G beta h k
  nlinarith [mul_nonneg (pow_nonneg hmNonneg 3) hc]



theorem grahamGhostCorrectedBound_of_pivot
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (i j k : V)
    (hpivot : i = k ∨ j = k) :
    gc_lebowitzU4 G beta h i j k ≤ grahamGhostCorrectedRHS G beta h i j k := by
  rw [grahamGhostFourPoint_iff_improvedGHS]
  rcases hpivot with hik | hjk
  · subst i
    exact grahamImprovedGHS_left_pivot G beta h hbeta hh j k
  · subst j
    exact grahamImprovedGHS_right_pivot G beta h hbeta hh i k

end StatMech.FrontierA
