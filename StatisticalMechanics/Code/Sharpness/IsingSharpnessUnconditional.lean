/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.IsingMagnetizationZero
import Code.Sharpness.IsingExponentialPlus
import Code.Sharpness.MeanfieldIsingPlusBridge
import Code.IsingFK.PcUpperAllDimensions

open MeasureTheory Set
open scoped BigOperators StatMech

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}

private theorem corrOriginInner_le_one (d : ℕ) (beta : ℝ)
    (S : Finset (Site d)) (x : Site d) :
    corrOriginInner d beta S x ≤ 1 := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact le_trans (le_abs_self _) (abs_freeCorr_le_one d beta S _ _)
    · norm_num
  · norm_num

private theorem card_boundaryEdges_le (S : Finset (Site d)) :
    (boundaryEdges d S).card ≤ S.card * (2 * d) := by
  classical
  unfold boundaryEdges
  refine le_trans Finset.card_image_le ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_bool]
  ring_nf
  omega

private theorem phiIsing_le_boundary_card (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Site d)) :
    phiIsing d beta S ≤ beta * (boundaryEdges d S).card := by
  unfold phiIsing
  have hsum :
      (∑ e ∈ boundaryEdges d S, corrOriginInner d beta S e.1) ≤
        (boundaryEdges d S).card := by
    calc
      (∑ e ∈ boundaryEdges d S, corrOriginInner d beta S e.1) ≤
          ∑ _e ∈ boundaryEdges d S, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => corrOriginInner_le_one d beta S e.1)
      _ = (boundaryEdges d S).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have htanh0 : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos _).le
  calc
    Real.tanh beta *
          (∑ e ∈ boundaryEdges d S, corrOriginInner d beta S e.1) ≤
        Real.tanh beta * (boundaryEdges d S).card :=
      mul_le_mul_of_nonneg_left hsum htanh0
    _ ≤ beta * (boundaryEdges d S).card :=
      mul_le_mul_of_nonneg_right (tanh_le_self_of_nonneg hbeta)
        (Nat.cast_nonneg _)



theorem tildeBetaCIsingSet_bddAbove (hd : 2 ≤ d) :
    BddAbove (tildeBetaCIsingSet d) := by
  obtain ⟨betaC, _hbetaC, _hbelow, habove⟩ :=
    IsingFK.ising_transition_unconditional_of_two_le hd
  refine ⟨betaC, ?_⟩
  intro gamma hgamma
  obtain ⟨hgamma0, S, ho, hphi⟩ := mem_tildeBetaCIsingSet.mp hgamma
  have hsum := plusCorr_summable_of_phi_lt_one gamma hgamma0 S ho hphi
  have hzero := magnetization_eq_zero_of_plusCorr_summable
    (le_trans (by omega : 1 ≤ 2) hd) gamma hgamma0 hsum
  by_contra hnot
  have hlt : betaC < gamma := lt_of_not_ge hnot
  have hpos := habove gamma hlt
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos).elim



theorem tildeBetaCIsing_pos (hd : 2 ≤ d) : 0 < tildeBetaCIsing d := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
  let beta : ℝ := 1 / (4 * d + 1)
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  let S : Finset (Site d) := {Percolation.origin d}
  have ho : Percolation.origin d ∈ S := by simp [S]
  have hcard : (boundaryEdges d S).card ≤ 2 * d := by
    have h := card_boundaryEdges_le (d := d) S
    simpa [S] using h
  have hcardR : ((boundaryEdges d S).card : ℝ) ≤ 2 * d := by
    exact_mod_cast hcard
  have hphi : phiIsing d beta S < 1 := by
    calc
      phiIsing d beta S ≤ beta * (boundaryEdges d S).card :=
        phiIsing_le_boundary_card beta hbeta.le S
      _ ≤ beta * (2 * d) := mul_le_mul_of_nonneg_left hcardR hbeta.le
      _ = (1 / (4 * d + 1)) * (2 * d) := rfl
      _ < 1 := by
        rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
        linarith
  have hmem : beta ∈ tildeBetaCIsingSet d :=
    ⟨hbeta.le, S, ho, hphi⟩
  exact hbeta.trans_le (le_csSup (tildeBetaCIsingSet_bddAbove hd) hmem)



theorem ising_sharpness_unconditional (hd : 2 ≤ d) :
    (∀ beta, Ising.betaC d ≤ beta →
      Real.sqrt (1 - (Ising.betaC d / beta) ^ 2) ≤
        magnetization d beta) ∧
    (∀ beta, 0 ≤ beta → beta < Ising.betaC d →
      Summable (plusCorr d beta (Percolation.origin d))) ∧
    (∀ beta, 0 ≤ beta → beta < Ising.betaC d →
      ∃ c > 0, ∀ z, plusCorr d beta (Percolation.origin d) z ≤
        Real.exp (-c * (l1dist d (Percolation.origin d) z : ℝ))) := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := d) hd
  have hcrit := tildeBetaCIsing_pos (d := d) hd
  have hsqrt : ∀ beta, tildeBetaCIsing d ≤ beta →
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        magnetization d beta :=
    fun beta hbeta =>
      sct_magnetization_meanfield_lower_bound_integrated d hbdd hcrit hbeta
  have heq : Ising.betaC d = tildeBetaCIsing d :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := d) (by omega) hsqrt
  refine ⟨?_, ?_, ?_⟩
  · simpa only [heq] using hsqrt
  · intro beta hbeta hlt
    rw [heq] at hlt
    obtain ⟨_S, _ho, _hphi, hsum⟩ :=
      finite_susceptibility_of_lt_tildeBetaCIsing (d := d) hbeta hlt
    exact hsum
  · intro beta hbeta hlt
    rw [heq] at hlt
    exact exponential_decay_of_lt_tildeBetaCIsing hbeta hlt

end Sharpness
end StatMech
