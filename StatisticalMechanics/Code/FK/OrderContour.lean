/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Lattice.CrossingParity
import Code.Lattice.PlanarTopology
import Code.FK.OrderTransition

open Finset Set SimpleGraph Filter Topology
open scoped BigOperators NNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice









noncomputable def peierlsContourWeight (q : ℝ) (n : ℕ) : ℝ := (4 / q) ^ n

@[simp] theorem peierlsContourWeight_zero (q : ℝ) : peierlsContourWeight q 0 = 1 := by
  simp [peierlsContourWeight]

theorem peierlsContourWeight_nonneg {q : ℝ} (hq : 0 < q) (n : ℕ) :
    0 ≤ peierlsContourWeight q n := by
  unfold peierlsContourWeight
  positivity








theorem card_dualCircuits_qSuppressed_le {q : ℝ} (hq : 0 < q) (n : ℕ) (v : Site 2) :
    ((dualLattice.finsetWalkLength n v v).card : ℝ) / q ^ n ≤ peierlsContourWeight q n := by
  unfold peierlsContourWeight
  rw [div_pow]
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq n
  have hcard : ((dualLattice.finsetWalkLength n v v).card : ℝ) ≤ (4 : ℝ) ^ n := by
    have h : (dualLattice.finsetWalkLength n v v).card ≤ 4 ^ n := card_dual_circuits_le_pow n v
    calc ((dualLattice.finsetWalkLength n v v).card : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (4 : ℝ) ^ n := by push_cast; ring
  exact (div_le_div_iff_of_pos_right hqn).mpr hcard




theorem peierlsContourRatio_lt_one {q : ℝ} (hq : 4 < q) : (4 : ℝ) / q < 1 := by
  rw [div_lt_one (by linarith)]; linarith

theorem peierlsContourRatio_nonneg {q : ℝ} (hq : 4 < q) : (0 : ℝ) ≤ 4 / q := by
  have : (0 : ℝ) < q := by linarith
  positivity






theorem peierls_summable {q : ℝ} (hq : 4 < q) :
    Summable (peierlsContourWeight q) :=
  summable_geometric_of_lt_one (peierlsContourRatio_nonneg hq) (peierlsContourRatio_lt_one hq)




theorem peierls_tsum_eq {q : ℝ} (hq : 4 < q) :
    ∑' n, peierlsContourWeight q n = q / (q - 4) := by
  unfold peierlsContourWeight
  rw [tsum_geometric_of_lt_one (peierlsContourRatio_nonneg hq) (peierlsContourRatio_lt_one hq)]
  have hq0 : (0 : ℝ) < q := by linarith
  have hqne : q ≠ 0 := by linarith
  have h4q : (1 : ℝ) - 4 / q = (q - 4) / q := by field_simp
  rw [h4q, inv_div]







noncomputable def peierlsTail (q : ℝ) (N : ℕ) : ℝ :=
  ∑' n, peierlsContourWeight q (n + N)



theorem peierlsTail_eq {q : ℝ} (hq : 4 < q) (N : ℕ) :
    peierlsTail q N = (4 / q) ^ N * (q / (q - 4)) := by
  unfold peierlsTail peierlsContourWeight
  have hkey : ∀ n, (4 / q) ^ (n + N) = (4 / q) ^ N * (4 / q) ^ n := by
    intro n; rw [pow_add]; ring
  simp_rw [hkey]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (peierlsContourRatio_nonneg hq) (peierlsContourRatio_lt_one hq)]
  have hq0 : (0 : ℝ) < q := by linarith
  have hqne : q ≠ 0 := by linarith
  have h4q : (1 : ℝ) - 4 / q = (q - 4) / q := by field_simp
  rw [h4q, inv_div]

theorem peierlsTail_nonneg {q : ℝ} (hq : 4 < q) (N : ℕ) : 0 ≤ peierlsTail q N := by
  rw [peierlsTail_eq hq N]
  have hq0 : (0 : ℝ) < q := by linarith
  positivity




theorem peierlsTail_le {q : ℝ} (hq : 8 ≤ q) (N : ℕ) :
    peierlsTail q N ≤ 2 * (4 / q) ^ N := by
  have hq4 : 4 < q := by linarith
  rw [peierlsTail_eq hq4 N]
  have hq0 : (0 : ℝ) < q := by linarith
  have hfac : q / (q - 4) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hpow : (0 : ℝ) ≤ (4 / q) ^ N := by positivity
  calc (4 / q) ^ N * (q / (q - 4)) ≤ (4 / q) ^ N * 2 :=
        mul_le_mul_of_nonneg_left hfac hpow
    _ = 2 * (4 / q) ^ N := by ring






theorem peierlsTail_tendsto_zero {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun q => peierlsTail q N) atTop (nhds 0) := by
  
  have hub : Tendsto (fun q : ℝ => 2 * (4 / q) ^ N) atTop (nhds 0) := by
    have h1 : Tendsto (fun q : ℝ => 4 / q) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have h2 : Tendsto (fun q : ℝ => (4 / q) ^ N) atTop (nhds (0 ^ N)) :=
      h1.pow N
    rw [zero_pow (by omega : N ≠ 0)] at h2
    have := h2.const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero' ?_ ?_ hub
  · filter_upwards [eventually_ge_atTop (8 : ℝ)] with q hq
    exact peierlsTail_nonneg (by linarith) N
  · filter_upwards [eventually_ge_atTop (8 : ℝ)] with q hq
    exact peierlsTail_le hq N












theorem dualCircuit_support_near (n : ℕ) (v : Site 2)
    (w : dualLattice.Walk v v) (hw : w.length = n) :
    ∀ z ∈ w.support, l1dist 2 v z ≤ n :=
  circuit_support_subset_ball 2 n v w hw





theorem card_dualCircuits_based_in_le (B : Finset (Site 2)) (n : ℕ) :
    (B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card ≤ B.card * 4 ^ n := by
  have h := card_circuits_based_in_le_pow 2 B n
  simpa using h






theorem card_dualCircuits_based_qSuppressed_le {q : ℝ} (hq : 0 < q)
    (B : Finset (Site 2)) (n : ℕ) :
    ((B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card : ℝ) / q ^ n
      ≤ (B.card : ℝ) * peierlsContourWeight q n := by
  unfold peierlsContourWeight
  rw [div_pow]
  rw [div_le_iff₀ (pow_pos hq n)]
  have hcard : ((B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card : ℝ)
      ≤ (B.card : ℝ) * (4 : ℝ) ^ n := by
    have h := card_dualCircuits_based_in_le B n
    calc ((B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card : ℝ)
        ≤ ((B.card * 4 ^ n : ℕ) : ℝ) := by exact_mod_cast h
      _ = (B.card : ℝ) * (4 : ℝ) ^ n := by push_cast; ring
  calc ((B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card : ℝ)
      ≤ (B.card : ℝ) * (4 : ℝ) ^ n := hcard
    _ = (B.card : ℝ) * (4 : ℝ) ^ n / q ^ n * q ^ n := by
        field_simp
    _ = (B.card : ℝ) * ((4 : ℝ) ^ n / q ^ n) * q ^ n := by ring









variable {ω : ConfigSpace (Sym2 (Site 2))}







theorem finite_cluster_yields_dualCircuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle :=
  exists_dualCircuit_of_finite_cluster o hfin w hz






theorem escape_crosses_dualContour_oddly (o : Site 2)
    {z : Site 2} (hz : z ∉ cluster 2 ω o) (γ : (hypercubicLattice 2).Walk o z) :
    ¬ Even (crossCount (cluster 2 ω o) γ) :=
  origin_crossCount_odd o hz γ























theorem qLarge_contour_estimate {q : ℝ} (hq : 4 < q) :
    Summable (peierlsContourWeight q)
      ∧ ∑' n, peierlsContourWeight q n = q / (q - 4)
      ∧ (∀ {q' : ℝ}, 8 ≤ q' → ∀ N : ℕ, peierlsTail q' N ≤ 2 * (4 / q') ^ N) :=
  ⟨peierls_summable hq, peierls_tsum_eq hq, fun hq' N => peierlsTail_le hq' N⟩

end FK

end StatMech
