/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Theta
public import MathlibExt.Probability.Percolation.PcNontrivial
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanZ2

/-!
# Upper bound on `p_c(2)` from a contour bound (Peierls argument)

The Peierls argument for bond percolation on `ℤ²`: if the cluster of the origin is finite, it is
surrounded by a closed dual circuit; there are at most `ℓ · 4^ℓ` dual circuits of length `ℓ`
surrounding the origin, each closed with probability `(1 - p)^ℓ`. This file contains the analytic
half: with `pcUpperBound p = ∑_ℓ ℓ 4^ℓ (1 - p)^ℓ`, which tends to `0` as `p → 1`, a contour bound
`1 - θ(p) ≤ pcUpperBound p` for all `p` close to `1` gives `p_c(2) < 1`. The contour bound is a
hypothesis here (`PcContourBound`); see `MathlibExt.Probability.Percolation.PcUpperEnclosure` for
its geometric input. An unconditional proof of `p_c(2) < 1` is
`StatMech.Percolation.pc_two_lt_one_via_fk` in `PhyslibExt`.

## Main definitions

* `StatMech.Percolation.pcUpperBound`: `∑_ℓ ℓ 4^ℓ (1 - p)^ℓ`.
* `StatMech.Percolation.PcContourBound`: the Peierls bound `1 - θ_2(p) ≤ pcUpperBound p`.

## Main results

* `StatMech.Percolation.pcUpperBound_tendsto_one`: `pcUpperBound p → 0` as `p → 1`.
* `StatMech.Percolation.pc_lt_one`, `StatMech.Percolation.pc_pos_and_lt_one`: `0 < p_c(2) < 1` under
  the contour bound for `p` near `1`.

## References

* R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936), 477–481.
* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Theorem 1.10.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

/-- The Peierls series `∑_ℓ ℓ 4^ℓ (1 - p)^ℓ` bounding the probability of a closed dual circuit
around the origin. -/
noncomputable def pcUpperBound (p : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ

/-- The ratio `4(1 - p)` of the geometric part of `pcUpperBound`. -/
noncomputable def pcRatio (p : ℝ) : ℝ := 4 * (1 - p)

@[simp] lemma pcRatio_def (p : ℝ) : pcRatio p = 4 * (1 - p) := rfl

lemma pcSummand_eq (p : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ = (ℓ : ℝ) * (pcRatio p) ^ ℓ := by
  rw [pcRatio_def, mul_assoc, ← mul_pow]

lemma pcUpperBound_eq_closedForm (p : ℝ) (hx : ‖pcRatio p‖ < 1) :
    pcUpperBound p = (pcRatio p) / (1 - pcRatio p) ^ 2 := by
  unfold pcUpperBound
  rw [show (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (pcRatio p) ^ ℓ) from funext (pcSummand_eq p)]
  exact tsum_coe_mul_geometric_of_norm_lt_one hx

lemma pcRatio_tendsto_one : Tendsto (fun p : ℝ => pcRatio p) (nhds 1) (nhds 0) := by
  have h : Tendsto (fun p : ℝ => pcRatio p) (nhds 1) (nhds (4 * (1 - 1))) := by
    unfold pcRatio
    exact (((tendsto_id).const_sub 1).const_mul 4)
  simpa using h

lemma pcClosedForm_tendsto_zero :
    Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds 0) := by
  have : Tendsto (fun x : ℝ => x / (1 - x) ^ 2) (nhds 0) (nhds (0 / (1 - 0) ^ 2)) := by
    apply Tendsto.div tendsto_id (Continuous.tendsto (by fun_prop) 0)
    norm_num
  simpa using this

lemma pcUpperBound_tendsto_one : Tendsto (fun p : ℝ => pcUpperBound p) (nhds 1) (nhds 0) := by
  have hev : (fun p : ℝ => pcUpperBound p) =ᶠ[nhds 1]
      (fun p : ℝ => (pcRatio p) / (1 - pcRatio p) ^ 2) := by
    have hlt : ∀ᶠ p in nhds 1, ‖pcRatio p‖ < 1 := by
      have := (pcRatio_tendsto_one).eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
      have hgt : ∀ᶠ p in nhds 1, (-1 : ℝ) < pcRatio p :=
        (pcRatio_tendsto_one).eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))
      filter_upwards [this, hgt] with p hp hp'
      rw [Real.norm_eq_abs, abs_lt]; exact ⟨hp', hp⟩
    filter_upwards [hlt] with p hp
    exact pcUpperBound_eq_closedForm p hp
  rw [tendsto_congr' hev]
  exact pcClosedForm_tendsto_zero.comp (pcRatio_tendsto_one)

theorem exists_p_lt_one_pcUpperBound_lt_one :
    ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 := by
  have h : ∀ᶠ p in nhds 1, pcUpperBound p < 1 :=
    (pcUpperBound_tendsto_one).eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hfn⟩ := h
  refine ⟨1 - ε / 2, by linarith, fun p hp1 _ => ?_⟩
  apply hfn
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

lemma pcUpperBound_nonneg {p : ℝ} (hp : p ≤ 1) : 0 ≤ pcUpperBound p := by
  unfold pcUpperBound
  apply tsum_nonneg
  intro ℓ
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

lemma pcContour_card_le (B : Finset (Site 2)) (ℓ : ℕ) (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ)
      ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ := by
  have h1 := card_circuits_based_in_le_pow 2 B ℓ
  have h3 : ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℕ)
      ≤ ℓ * (2 * 2) ^ ℓ := le_trans h1 (Nat.mul_le_mul_right _ hB)
  calc ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ)
      ≤ ((ℓ * (2 * 2) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (ℓ : ℝ) * (4 : ℝ) ^ ℓ := by push_cast; ring

lemma pcContour_card_le_summand {p : ℝ} (hp : p ≤ 1) (B : Finset (Site 2)) (ℓ : ℕ)
    (hB : B.card ≤ ℓ) :
    ((B.sigma (fun v => dualLattice.finsetWalkLength ℓ v v)).card : ℝ) * (1 - p) ^ ℓ
      ≤ (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ := by
  have hpow : (0 : ℝ) ≤ (1 - p) ^ ℓ := by
    have : (0 : ℝ) ≤ 1 - p := by linarith
    positivity
  exact mul_le_mul_of_nonneg_right (pcContour_card_le B ℓ hB) hpow

/-- The Peierls contour bound `1 - θ_2(p) ≤ pcUpperBound p` at density `p`. -/
def PcContourBound (p : ℝ≥0) (hp : p ≤ 1) : Prop :=
  1 - theta 2 p hp ≤ pcUpperBound (p : ℝ)

theorem theta_pos_of_contourBound {p : ℝ≥0} (hp : p ≤ 1)
    (hContour : PcContourBound p hp) (hBound : pcUpperBound (p : ℝ) < 1) :
    0 < theta 2 p hp := by
  have h : 1 - theta 2 p hp ≤ pcUpperBound (p : ℝ) := hContour
  linarith

theorem not_mem_subcriticalSet_of_theta_pos {p : ℝ≥0} (hp : p ≤ 1)
    (hθ : 0 < theta 2 p hp) : p ∉ subcriticalSet 2 := by
  intro hmem
  obtain ⟨hp', hzero⟩ := hmem
  rw [show hp' = hp from rfl] at hzero
  exact (ne_of_gt hθ) hzero

/-- `p_c(2) < 1`, assuming the Peierls contour bound `PcContourBound` for all `p` above some
`p₀ < 1`. -/
theorem pc_lt_one
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ≥0) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
    pc 2 < 1 := by
  obtain ⟨p₁, hp₁lt, hp₁bound⟩ := exists_p_lt_one_pcUpperBound_lt_one
  obtain ⟨p₂, hp₂lt, hp₂geom⟩ := hGeom
  set t : ℝ := max (max p₁ p₂) 0 with ht
  have htlt : t < 1 := max_lt (max_lt hp₁lt hp₂lt) (by norm_num)
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have hp₁t : p₁ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have hp₂t : p₂ ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  set s : ℝ := (t + 1) / 2 with hs
  have hts : t < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) ≤ s := by rw [hs]; linarith
  set sN : ℝ≥0 := s.toNNReal with hsN
  have hsNcoe : (sN : ℝ) = s := by rw [hsN]; exact Real.coe_toNNReal s hs0
  have hsN1 : sN ≤ 1 := by
    rw [hsN, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hslt.le
  have hsNlt1 : sN < 1 := by
    rw [hsN, ← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff_of_nonneg hs0]
    exact hslt
  have hub : ∀ q ∈ subcriticalSet 2, q ≤ sN := by
    intro q hq
    by_contra hcon
    push Not at hcon
    have hqreal : s < (q : ℝ) := by
      have hsq : (sN : ℝ) < (q : ℝ) := by exact_mod_cast hcon
      rwa [hsNcoe] at hsq
    have hq1 : q ≤ 1 := hq.1
    have hp₁q : p₁ < (q : ℝ) := lt_of_le_of_lt (le_trans hp₁t hts.le) hqreal
    have hp₂q : (p₂ : ℝ) < (q : ℝ) := lt_of_le_of_lt (le_trans hp₂t hts.le) hqreal
    have hbnd : pcUpperBound (q : ℝ) < 1 := hp₁bound (q : ℝ) hp₁q hq1
    have hcb : PcContourBound q hq1 := hp₂geom q hq1 hp₂q
    have hθ : 0 < theta 2 q hq1 := theta_pos_of_contourBound hq1 hcb hbnd
    exact not_mem_subcriticalSet_of_theta_pos hq1 hθ hq
  calc pc 2 = sSup (subcriticalSet 2) := rfl
    _ ≤ sN := csSup_le' hub
    _ < 1 := hsNlt1

theorem pc_pos_and_lt_one
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ≥0) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
    0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_lt_one hGeom⟩

end Percolation

end StatMech
