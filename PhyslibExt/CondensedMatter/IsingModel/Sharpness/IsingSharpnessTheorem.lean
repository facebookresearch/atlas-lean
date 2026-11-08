/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingMagnetizationZero
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.IsingExponentialPlus
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldIsingPlusBridge
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperAllDimensions

/-!
# Sharpness of the phase transition for the Ising model on ℤ^d

For the nearest-neighbour Ising model on `ℤ^d`, `d ≥ 2`: the mean-field lower bound on the
spontaneous magnetization above `β_c`, and summability and exponential decay of the plus-state
two-point function below `β_c`.

## i. Overview

Let `β_c(d) = inf {β ≥ 0 | m*(β) > 0}` be the critical inverse temperature defined through the
spontaneous magnetization `m*(β) = ⟨σ_0⟩^+_β` of the plus state. Following Duminil-Copin and
Tassion, one introduces the auxiliary point `β̃_c = sup {β ≥ 0 | ∃ S ∋ 0 finite, φ_β(S) < 1}`, where
`φ_β(S) = tanh β ∑_{(x,y) ∈ ∂S} ⟨σ_0σ_x⟩_S`.

Below `β̃_c` a finite set with `φ_β(S) < 1` gives, through Simon's inequality, a finite
susceptibility and exponential decay of `⟨σ_0σ_z⟩^+_β`. Above `β̃_c` the finite-volume differential
inequality integrates to `m*(β) ≥ √(1 - (β̃_c/β)²)`. Together these force `β̃_c = β_c`. The
existence of a phase transition for `d ≥ 2` (Peierls) bounds the set defining `β̃_c` and gives `β̃_c
> 0`.

## ii. Key results

- `tildeBetaCIsing_pos` : `0 < β̃_c` for `d ≥ 2`
- `ising_sharp_phase_transition` : the sharpness theorem: mean-field lower bound above `β_c`,
  finite susceptibility and exponential decay below `β_c`

## iii. Table of contents

- A. Elementary bounds on `φ_β`
- B. The auxiliary critical point
- C. The sharpness theorem

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
- M. Aizenman, D. J. Barsky, R. Fernández, "The phase transition in a general class of Ising-type
  models is sharp", J. Stat. Phys. 47 (1987) 343–374
- B. Simon, "Correlation inequalities and the decay of correlations in ferromagnets", Comm. Math.
  Phys. 77 (1980) 111–126

-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators StatMech

namespace StatMech
namespace Sharpness

open Ising StatMech.Lattice Percolation

variable {d : ℕ}

/-! ## A. Elementary bounds on `φ_β` -/

private lemma corrOriginInner_le_one (d : ℕ) (beta : ℝ)
    (S : Finset (Site d)) (x : Site d) :
    corrOriginInner d beta S x ≤ 1 := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact le_trans (le_abs_self _) (abs_freeCorr_le_one d beta S _ _)
    · norm_num
  · norm_num

private lemma phiIsing_le_boundary_card (beta : ℝ) (hbeta : 0 ≤ beta)
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

/-! ## B. The auxiliary critical point -/

lemma tildeBetaCIsingSet_bddAbove (hd : 2 ≤ d) :
    BddAbove (tildeBetaCIsingSet d) := by
  obtain ⟨betaC, _hbetaC, _hbelow, habove⟩ :=
    IsingFK.ising_phase_transition_of_two_le hd
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

/-- For `d ≥ 2` the auxiliary critical point `β̃_c(d)` is positive: `φ_β({0}) ≤ 2dβ < 1` for small
`β`. -/
lemma tildeBetaCIsing_pos (hd : 2 ≤ d) : 0 < tildeBetaCIsing d := by
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

/-! ## C. The sharpness theorem -/

/-- Sharpness of the phase transition for the Ising model on `ℤ^d`, `d ≥ 2`: for `β ≥ β_c`, `m*(β) ≥
√(1 - (β_c/β)²)`; for `0 ≤ β < β_c`, the plus-state two-point function `z ↦ ⟨σ_0σ_z⟩^+_β` is
summable and decays as `exp(-c‖z‖₁)`. Reference: H. Duminil-Copin, V. Tassion, "A new proof of the
sharpness of the phase transition for Bernoulli percolation and the Ising model", Comm. Math. Phys.
343 (2016) 725–745, Theorem 1.2; first proved in M. Aizenman, D. J. Barsky, R. Fernández, "The phase
transition in a general class of Ising-type models is sharp", J. Stat. Phys. 47 (1987) 343–374.
Scope: `β_c` is `Ising.betaC d`, the infimum of the inverse temperatures with positive spontaneous
magnetization, and distance is the `ℓ¹` distance (equivalent to the Euclidean one up to constants).
The statement does not include `0 < β_c < ∞`; positivity follows from `tildeBetaCIsing_pos` and the
identification `β_c = β̃_c` in the proof, finiteness from the Peierls transition. -/
theorem ising_sharp_phase_transition (hd : 2 ≤ d) :
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
