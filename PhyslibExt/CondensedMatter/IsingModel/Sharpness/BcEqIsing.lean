/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Magnetization
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildeBc

/-!
# Identification of β_c with the auxiliary critical point

`β_c = β̃_c` for the Ising model on `ℤ^d`, given the mean-field lower bound above `β̃_c` and
vanishing magnetization below it.

## i. Overview

If the magnetization is positive above `β̃_c`, then `β_c ≤ β̃_c`; if it vanishes on `[0, β̃_c)`,
then `β̃_c ≤ β_c`. The mean-field bound `m*(β) ≥ √(1 - (β̃_c/β)²)` gives positivity above `β̃_c`
when `β̃_c > 0`.

## ii. Key results

- `bc_le_tildeBc_ising` : `β_c ≤ β̃_c` from positivity above `β̃_c`
- `tildeBc_le_bc_ising` : `β̃_c ≤ β_c` from vanishing below `β̃_c`
- `bc_eq_ising` : `β_c = β̃_c`
- `bc_eq_ising_of_meanfield` : `β_c = β̃_c` from the mean-field bound

## iii. Table of contents

- A. Comparison of the critical points
- B. Positivity from the mean-field bound

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open Set

namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {d : ℕ}

/-! ## A. Comparison of the critical points -/

lemma tildeBetaCIsing_nonneg : 0 ≤ tildeBetaCIsing d := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  unfold tildeBetaCIsing
  by_cases hbdd : BddAbove (tildeBetaCIsingSet d)
  · exact le_csSup hbdd hzero
  · rw [csSup_of_not_bddAbove hbdd, Real.sSup_empty]

lemma bc_le_tildeBc_ising
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β) :
    betaC d ≤ tildeBetaCIsing d := by
  unfold betaC
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro β' hβ'
  exact csInf_le hbdd
    ⟨(tildeBetaCIsing_nonneg (d := d)).trans hβ'.le, hpos β' hβ'⟩

lemma tildeBc_le_bc_ising
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    tildeBetaCIsing d ≤ betaC d := by
  unfold betaC
  refine le_csInf hne ?_
  intro β hβ
  by_contra hcon
  rw [not_le] at hcon
  rw [mem_positiveMagnetizationSet] at hβ
  have hz := hzero β hβ.1 hcon
  rw [hz] at hβ
  exact lt_irrefl 0 hβ.2

lemma bc_eq_ising
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d :=
  le_antisymm (bc_le_tildeBc_ising hbdd hpos) (tildeBc_le_bc_ising hne hzero)

/-! ## B. Positivity from the mean-field bound -/

lemma posMag_of_meanfield_sqrt (htc_pos : 0 < tildeBetaCIsing d)
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
    ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
  intro β hβ
  have hβpos : 0 < β := lt_trans htc_pos hβ
  have hlt1 : (tildeBetaCIsing d / β) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    apply sq_lt_sq'
    · nlinarith [htc_pos]
    · exact hβ
  have hsqrtpos : 0 < Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) :=
    Real.sqrt_pos.mpr (by linarith)
  exact lt_of_lt_of_le hsqrtpos (hsqrt β hβ.le)

lemma posMag_of_meanfield_sqrt_nonneg
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
    ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
  rcases (tildeBetaCIsing_nonneg (d := d)).eq_or_lt with hzero | hpos
  · intro β hβ
    have htc : tildeBetaCIsing d = 0 := hzero.symm
    have hβpos : 0 < β := by simpa [htc] using hβ
    have hone : (1 : ℝ) ≤ magnetization d β := by
      simpa [htc] using hsqrt β hβ.le
    linarith
  · exact posMag_of_meanfield_sqrt hpos hsqrt

lemma positiveMagnetizationSet_bddBelow :
    BddBelow (positiveMagnetizationSet d) := by
  refine ⟨0, ?_⟩
  intro β hβ
  exact (mem_positiveMagnetizationSet.mp hβ).1

lemma bc_eq_ising_of_items
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d := by
  have hpos := posMag_of_meanfield_sqrt_nonneg (d := d) hsqrt
  have hbdd := positiveMagnetizationSet_bddBelow (d := d)
  have hne : (positiveMagnetizationSet d).Nonempty := by
    refine ⟨tildeBetaCIsing d + 1, ?_⟩
    exact ⟨by linarith [tildeBetaCIsing_nonneg (d := d)], hpos _ (by linarith)⟩
  exact bc_eq_ising hbdd hne hpos hzero

lemma bc_eq_ising_of_meanfield (htc_pos : 0 < tildeBetaCIsing d)
    (hbdd : BddBelow (positiveMagnetizationSet d))
    (hne : (positiveMagnetizationSet d).Nonempty)
    (hsqrt : ∀ β, tildeBetaCIsing d ≤ β →
      Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
    (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
    betaC d = tildeBetaCIsing d :=
  bc_eq_ising hbdd hne (posMag_of_meanfield_sqrt htc_pos hsqrt) hzero

end Sharpness

end StatMech
